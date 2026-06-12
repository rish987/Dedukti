open Basic
open Rule
open Term
open Dtree
open Ac

(* DK_LAZY_DELTA: when comparing two applications headed by the SAME (non-AC)
   constant with equal arity, try arg-wise convertibility (congruence) BEFORE
   whnf-unfolding the head. This mirrors Lean's lazy-delta `isDefEqArgs`: it
   avoids unfolding (e.g.) well-founded recursors when the arguments are already
   convertible, which keeps the conversion check out of reduction sequences that
   have no normal form (the `Acc`/`WellFounded.fix` accessibility-proof towers).
   Sound: congruence is always valid, and we fall back to the usual whnf-based
   step when the arguments are not (syntactically/recursively) convertible, so
   completeness is preserved. AC-headed symbols are excluded (they need
   set-based comparison, handled separately in [conversion_step]). *)
let dk_lazy_delta = try Sys.getenv "DK_LAZY_DELTA" <> "" with Not_found -> false

(* DK_PROGRESS: lightweight per-declaration progress heartbeat, to tell whether
   type-checking is making progress or stuck on a subterm. Enabled by setting the
   DK_PROGRESS environment variable. [prog_nodes]/[prog_total] track the typing
   descent over the declaration (a percentage); [prog_conv]/[prog_whnf] count
   convertibility pairs / whnf calls. Every ~2s a heartbeat reports them: a frozen
   descent % with a climbing conv counter means we are stuck reducing one subterm. *)
let dk_progress = try Sys.getenv "DK_PROGRESS" <> "" with Not_found -> false

let prog_conv = ref 0

let prog_whnf = ref 0

let prog_nodes = ref 0

let prog_total = ref 0

let prog_last_t = ref 0.0

let prog_last_conv = ref 0

let prog_decl = ref ""

(* ---- diagnostics: capture the diverging pair when stuck ---- *)
(* outermost are_convertible pair (the "equation" the type-checker requested) *)
let prog_seed : (term * term) option ref = ref None

(* worklist pair most recently processed *)
let prog_cur : (term * term) option ref = ref None

let prog_depth = ref 0

let prog_dumped = ref false

(* composition of conversion work: universe-level machinery vs. genuine terms *)
let prog_conv_lvl = ref 0

let prog_conv_oth = ref 0

let prog_last_lvl = ref 0

let prog_last_oth = ref 0

(* state_whnf rewrite-loop instrumentation: catches non-termination *inside* a
   single whnf call (where the conv/whnf-entry counters can't, since we never
   return to them). Its own timer, since the outer prog_beat is starved. *)
let prog_sw_steps = ref 0

let prog_sw_last_t = ref 0.0

let prog_sw_dumped = ref false

(* the term most recently passed to [whnf]; if that whnf call loops in state_whnf,
   this is the self-contained term whose reduction does not terminate. *)
let prog_whnf_entry : term option ref = ref None

(* value of [prog_sw_steps] when the current whnf call started; lets us measure the
   state_whnf steps spent *within a single whnf call* (the cumulative counter cannot).
   If this exceeds a large bound, that one whnf call is genuinely non-terminating. *)
let prog_whnf_entry_steps : int ref = ref 0

(* the typing context (Gamma) of the convertibility check currently in progress,
   stashed by typing.ml. Used to lambda-close a looping subterm into a standalone,
   well-typed term for `#EVAL`/`#CHECK`. Innermost binder (DB 0) is the list head. *)
let prog_typing_ctx : (Basic.loc * Basic.ident * term) list ref = ref []

(* Per-declaration materialization budget (DK_TOS_BUDGET): a cap on the number of term
   nodes [term_of_state] may build while checking one declaration. A declaration whose
   translated normal form is exponentially large (e.g. structure-eta-recursor terms over
   brecOn) blows up here; with a budget set, the check aborts fast (bounded memory) and
   names the offending declaration so it can be force-stubbed, instead of OOMing. [<0]
   disables it. [tos_count] is reset per declaration by [prog_reset]. *)
exception Materialization_budget of int

let tos_budget = ref (-1)
let tos_count = ref 0

(* Heap-size guard (DK_MEM_BUDGET, in bytes; <0 disables). A robust catch-all for the
   exponential-normal-form constants (structure-eta-recursor over brecOn): regardless of
   *where* the blowup allocates (materialization, conversion obligation lists, caches),
   we periodically check the major-heap size and abort fast — bounded memory — naming the
   offending declaration so it can be force-stubbed, instead of OOMing the machine. *)
let mem_budget = ref (-1)

exception Mem_budget of int

let check_mem () =
  if !mem_budget >= 0 then begin
    let bytes = (Gc.quick_stat ()).Gc.heap_words * (Sys.word_size / 8) in
    if bytes > !mem_budget then begin
      Printf.eprintf
        "\n[DK_MEM_BUDGET] declaration %S exceeded heap budget (%d MB): its check is \
         infeasible (force-stub it).\n%!"
        !prog_decl (bytes / 1048576);
      raise (Mem_budget bytes)
    end
  end

(* count of rewrite-rule firings per head symbol — symbols whose count grows without
   bound are the ones being rewritten infinitely (the loop). *)
let prog_rule_fires : (string, int) Hashtbl.t = Hashtbl.create 64

let prog_rule_bump (n : name) : unit =
  if dk_progress then
    let k = string_of_mident (md n) ^ "." ^ string_of_ident (id n) in
    Hashtbl.replace prog_rule_fires k
      (1 + (try Hashtbl.find prog_rule_fires k with Not_found -> 0))

let prog_rule_top () : string =
  let l = Hashtbl.fold (fun k v acc -> (k, v) :: acc) prog_rule_fires [] in
  let l = List.sort (fun (_, a) (_, b) -> compare b a) l in
  let rec take n = function [] -> [] | x :: xs -> if n <= 0 then [] else x :: take (n - 1) xs in
  String.concat "  " (List.map (fun (k, v) -> Printf.sprintf "%s=%d" k v) (take 10 l))

let level_modules =
  [ "lvl"; "sublvl"; "nat"; "normalize"; "AuxLvls"; "bool"; "instantiate" ]

let rec prog_head (t : term) : term =
  match t with App (f, _, _) -> prog_head f | _ -> t

let pair_is_level (t1 : term) (t2 : term) : bool =
  let mod_of t =
    match prog_head t with
    | Const (_, n) -> Some (string_of_mident (md n))
    | _ -> None
  in
  let is_lvl = function Some m -> List.mem m level_modules | None -> false in
  is_lvl (mod_of t1) || is_lvl (mod_of t2)

(* ---------------------------------------------------------------------------
   Convertibility memoization (DK_MEMO; disable with DK_NO_MEMO=1).

   The Prod/PProd projection/eta rules are non-linear in their universe-level
   arguments (required for the rules to be subject-reduction-correct), so every
   match fires a level convertibility check via [constraint_convertibility]
   (= [are_convertible]). On brecOn/Nat_rec-built structures these identical
   level checks are run millions of times, which is what makes e.g.
   `Nat.Linear.ExprCnstr.denote_toNormPoly` fail to terminate in practice.

   We cache only *positive* (convertible) results, and only for level-typed
   pairs while the full rule set is active (`selection = None`):
   - positive-only + full-ruleset means the cache needs no invalidation:
     convertibility is monotonic under signature extension (adding rules only
     adds reducts, so `t1 == t2` stays true), and we never reuse a result under
     a restricted rule selection.
   - the level-pair restriction bounds key size (we never hash whole types) and
     targets exactly the repeated checks.
   The key uses [term_eq] (loc/binder-insensitive) with a matching bounded-depth
   hash. --------------------------------------------------------------------- *)
let dk_memo = (try Sys.getenv "DK_NO_MEMO" with Not_found -> "") = ""

let rec term_hash (d : int) (t : term) : int =
  if d <= 0 then 0
  else
    match t with
    | Kind -> 1
    | Type _ -> 2
    | DB (_, _, n) -> Hashtbl.hash (3, n)
    | Const (_, c) -> Hashtbl.hash (4, Hashtbl.hash c)
    | App (f, a, l) ->
        Hashtbl.hash
          ( 5, term_hash (d - 1) f, term_hash (d - 1) a, List.length l,
            match l with x :: _ -> term_hash (d - 1) x | [] -> 0 )
    | Lam (_, _, _, b) -> Hashtbl.hash (6, term_hash (d - 1) b)
    | Pi (_, _, a, b) -> Hashtbl.hash (7, term_hash (d - 1) a, term_hash (d - 1) b)

module ConvKey = struct
  type t = term * term

  let equal (a, b) (c, d) = term_eq a c && term_eq b d
  let hash (a, b) = Hashtbl.hash (term_hash 6 a, term_hash 6 b)
end

module ConvCache = Hashtbl.Make (ConvKey)

(* presence of a key means "known convertible" (we only ever store `true`) *)
let conv_cache : unit ConvCache.t = ConvCache.create 4096
let conv_hits = ref 0

(* Single-term-keyed cache module for reduction sharing (whnf memoization).
   The value type ([state]) is filled in once [state] is in scope (see
   [whnf_cache] below). See [whnf_cache] for the soundness discussion. *)
module TermKey = struct
  type t = term

  let equal = term_eq
  let hash t = term_hash 8 t
end

module WhnfCache = Hashtbl.Make (TermKey)
let whnf_hits = ref 0

(* depth-bounded term printer so we can dump giant/looping subterms cheaply *)
let rec pp_trunc (d : int) (fmt : Format.formatter) (t : term) : unit =
  if d <= 0 then Format.fprintf fmt "_"
  else
    match t with
    | Kind -> Format.fprintf fmt "Kind"
    | Type _ -> Format.fprintf fmt "Type"
    | DB (_, x, n) -> Format.fprintf fmt "%a#%d" pp_ident x n
    | Const (_, c) -> Format.fprintf fmt "%a" pp_name c
    | App (f, a, args) ->
        Format.fprintf fmt "(%a %a%s)" (pp_trunc (d - 1)) f (pp_trunc (d - 1)) a
          (if args = [] then "" else Format.asprintf " +%d" (List.length args))
    | Lam (_, x, _, b) -> Format.fprintf fmt "\\%a.%a" pp_ident x (pp_trunc (d - 1)) b
    | Pi (_, x, a, b) ->
        Format.fprintf fmt "{%a:%a}%a" pp_ident x (pp_trunc (d - 1)) a
          (pp_trunc (d - 1)) b

let prog_reset (name : string) (total : int) : unit =
  if dk_progress then (
    prog_conv := 0;
    prog_whnf := 0;
    prog_nodes := 0;
    prog_total := total;
    prog_last_conv := 0;
    prog_decl := name;
    prog_seed := None;
    prog_cur := None;
    prog_depth := 0;
    prog_dumped := false;
    prog_conv_lvl := 0;
    prog_conv_oth := 0;
    prog_last_lvl := 0;
    prog_last_oth := 0;
    prog_sw_steps := 0;
    prog_sw_last_t := (try Unix.gettimeofday () with _ -> 0.0);
    prog_sw_dumped := false;
    prog_whnf_entry := None;
    prog_whnf_entry_steps := 0;
    prog_typing_ctx := [];
    tos_count := 0;
    Hashtbl.clear prog_rule_fires;
    prog_last_t := (try Unix.gettimeofday () with _ -> 0.0);
    Printf.eprintf "[DK_PROGRESS] >>> checking %s (%d nodes)\n%!" name total)

let prog_beat () =
  if dk_progress then
    let now = try Unix.gettimeofday () with _ -> 0.0 in
    if now -. !prog_last_t >= 2.0 then (
      let pct =
        if !prog_total <= 0 then 0.0
        else 100.0 *. float_of_int !prog_nodes /. float_of_int !prog_total
      in
      Printf.eprintf
        "[DK_PROGRESS] %s: descent %d/%d (%.1f%%)  conv=%d (+%d/2s)  whnf=%d\n%!"
        !prog_decl !prog_nodes !prog_total pct !prog_conv
        (!prog_conv - !prog_last_conv) !prog_whnf;
      Printf.eprintf
        "    conv composition: level=%d (+%d/2s)  other=%d (+%d/2s)  conv_hits=%d  whnf_hits=%d\n%!"
        !prog_conv_lvl (!prog_conv_lvl - !prog_last_lvl)
        !prog_conv_oth (!prog_conv_oth - !prog_last_oth) !conv_hits !whnf_hits;
      (match !prog_seed with
      | Some (l, r) ->
          Format.eprintf "    seed L: %a@.    seed R: %a@." (pp_trunc 10) l (pp_trunc 10) r
      | None -> ());
      (match !prog_cur with
      | Some (l, r) ->
          Format.eprintf "    cur  L: %a@.    cur  R: %a@." (pp_trunc 9) l (pp_trunc 9) r
      | None -> ());
      (if (not !prog_dumped) && !prog_conv > 150_000 then
         match !prog_seed with
         | Some (l, r) ->
             prog_dumped := true;
             (try
                let oc = open_out "/tmp/dk_seed_full.txt" in
                let fmt = Format.formatter_of_out_channel oc in
                Format.fprintf fmt "SEED L:@.%a@.@.SEED R:@.%a@." pp_term l pp_term r;
                Format.pp_print_flush fmt ();
                close_out oc;
                Printf.eprintf "    [dumped full seed pair to /tmp/dk_seed_full.txt]\n%!"
              with _ -> ())
         | None -> ());
      prog_last_t := now;
      prog_last_conv := !prog_conv;
      prog_last_lvl := !prog_conv_lvl;
      prog_last_oth := !prog_conv_oth)

let d_reduce = Debug.register_flag "Reduce"

type red_target = Snf | Whnf

type red_strategy = ByName | ByValue | ByStrongValue

type dtree_finder = Signature.t -> Basic.loc -> Basic.name -> t

type red_cfg = {
  select : (Rule.rule_name -> bool) option;
  nb_steps : int option;
  (* [Some 0] for no evaluation, [None] for no bound *)
  target : red_target;
  strat : red_strategy;
  beta : bool;
  logger : position -> Rule.rule_name -> term Lazy.t -> term Lazy.t -> unit;
  finder : dtree_finder;
}

let pp_red_cfg fmt cfg =
  let args =
    (match cfg.target with Snf -> ["SNF"] | _ -> [])
    @ (match cfg.strat with
      | ByValue -> ["CBV"]
      | ByStrongValue -> ["CBSV"]
      | _ -> [])
    @ match cfg.nb_steps with Some i -> [string_of_int i] | _ -> []
  in
  Format.fprintf fmt "[%a]" (pp_list "," Format.pp_print_string) args

let default_cfg =
  {
    select = None;
    nb_steps = None;
    target = Snf;
    strat = ByName;
    beta = true;
    logger = (fun _ _ _ _ -> ());
    finder = Signature.get_dtree;
  }

exception Not_convertible

let rec zip_lists l1 l2 lst =
  match (l1, l2) with
  | [], [] -> lst
  | s1 :: l1, s2 :: l2 -> zip_lists l1 l2 ((s1, s2) :: lst)
  | _, _ -> raise Not_convertible

(* State *)

type env = term Lazy.t LList.t

(* A state {ctx; term; stack} is the state of an abstract machine that
   represents a term where [ctx] is a ctx that contains the free variables
   of [term] and [stack] represents the terms that [term] is applied to. *)
type state = {
  ctx : env;
  (* context *)
  term : term;
  (* term to reduce *)
  stack : stack; (* stack *)
}

and stack = state ref list
(* TODO: implement  constant time random access / in place mutable value.  *)

let rec term_of_state {ctx; term; stack} : term =
  (if !tos_budget >= 0 || !mem_budget >= 0 then begin
     incr tos_count;
     if !tos_budget >= 0 && !tos_count > !tos_budget then begin
       Printf.eprintf
         "\n[DK_TOS_BUDGET] declaration %S exceeded materialization budget (%d term nodes): \
          its translated normal form is too large to check (force-stub it).\n%!"
         !prog_decl !tos_count;
       raise (Materialization_budget !tos_count)
     end;
     (* materializing a huge term keeps [state_whnf]/conv counters idle, so also poll the
        heap guard here (every ~256k nodes) to catch term_of_state-driven blowups. *)
     if !mem_budget >= 0 && !tos_count land 0x3FFFF = 0 then check_mem ()
   end);
  let t = if LList.is_empty ctx then term else Subst.psubst_l ctx term in
  mk_App2 t (List.map term_of_state_ref stack)

and term_of_state_ref r = term_of_state !r

let () = tos_budget := (try int_of_string (Sys.getenv "DK_TOS_BUDGET") with _ -> -1)
let () = mem_budget := (try int_of_string (Sys.getenv "DK_MEM_BUDGET") with _ -> -1)

let state_of_term t = {ctx = LList.nil; term = t; stack = []}

let state_ref_of_term t = ref {ctx = LList.nil; term = t; stack = []}

(* whnf memoization cache (reduction sharing). A rule RHS that duplicates a
   pattern variable -- the structure-eta recursor
   `Prod_rec C f x --> f (Prod_fst x) (Prod_snd x)` is the motivating case --
   otherwise re-reduces the shared subterm once per occurrence; on nested
   brecOn/PProd structures that is exponential. We memoize the whnf of closed,
   unapplied, redex-headed states so the reduction is shared.

   whnf is NOT monotone under signature extension, so this cache MUST be cleared
   when the signature changes: the typing module calls [clear_conv_cache] per
   declaration. It is only consulted while the full rule set is active
   (`selection = None`). *)
let whnf_cache : state WhnfCache.t = WhnfCache.create 4096

let clear_conv_cache () =
  ConvCache.clear conv_cache;
  WhnfCache.clear whnf_cache;
  conv_hits := 0;
  whnf_hits := 0

(* Invalidate the memoization caches whenever the signature changes (see the
   cache headers: convertibility is monotone so [conv_cache] could persist, but
   whnf is not, so we clear both for safety). *)
let () = Signature.on_signature_change := clear_conv_cache

(**************** Pretty Printing ****************)

(*
open Format

let pp_env fmt (env:env) = pp_list ", " pp_term fmt (List.map Lazy.force (LList.lst env))
let pp_stack fmt (st:stack) =
  fprintf fmt "[ %a ]\n" (pp_list "\n | " pp_term) (List.map term_of_state_ref st)

let pp_stack_oneline fmt (st:stack) =
  fprintf fmt "[ %a ]" (pp_list " | " pp_term) (List.map term_of_state_ref st)

let pp_state ?(if_ctx=true) ?(if_stack=true) fmt { ctx; term; stack } =
  if if_ctx
  then fprintf fmt "{ctx=[%a];@." pp_env ctx
  else fprintf fmt "{ctx=[...](%i);@." (LList.len ctx);
  fprintf fmt "term=%a;@." pp_term term;
  if if_stack
  then fprintf fmt "stack=%a}@." pp_stack stack
  else fprintf fmt "stack=[...](%i)}@." (List.length stack);
  fprintf fmt "@.%a@." pp_term (term_of_state {ctx; term; stack})

let pp_state_oneline = pp_state ~if_ctx:true ~if_stack:true
*)

type convertibility_test = Signature.t -> term -> term -> bool

module type ConvChecker = sig
  val are_convertible : convertibility_test

  val constraint_convertibility :
    Rule.constr -> Rule.rule_name -> convertibility_test

  val conversion_step :
    Signature.t -> term * term -> (term * term) list -> (term * term) list
end

module type S = sig
  include ConvChecker

  val reduction : red_cfg -> Signature.t -> term -> term

  val whnf : Signature.t -> term -> term

  val snf : Signature.t -> term -> term
end

(* Should eta expansion be allowed at conversion check ? *)
let eta = ref false

(* Should beta steps be allowed at reduction ? *)
let beta = ref true

(* Rule filter *)
let selection = ref None

(* Where to find the dtree associated to a symbol *)
let dtree_finder : dtree_finder ref = ref Signature.get_dtree

module Make (C : ConvChecker) (M : Matching.Matcher) : S = struct
  (*******      AC manipulating functions   *******)

  let filter_neutral sg l cst terms =
    match Signature.get_algebra sg l cst with
    | ACU neu -> (
        match List.filter (fun x -> not (C.are_convertible sg neu x)) terms with
        | [] -> [neu]
        | s -> s)
    | _ -> terms

  (** Builds a comb-shaped AC term from a list of arguments. *)
  let to_comb sg l cst ctx stack =
    let rec f = function
      | [] ->
          {ctx = LList.nil; term = Signature.get_neutral sg l cst; stack = []}
      | [t] -> !t
      | t1 :: t2 :: tl ->
          f (ref {ctx; term = mk_Const l cst; stack = [t1; t2]} :: tl)
    in
    f stack

  (* Unfolds all occurences of the AC(U) symbol in the stack
   * Removes occurence of neutral element. *)
  let rec flatten_AC_stack sg (cst : name) : stack -> stack =
    let rec flatten acc = function
      | [] -> acc
      | st :: tl -> (
          match !st with
          | {term = Const (_, cst'); stack = [st1; st2]; _}
            when name_eq cst cst' ->
              flatten acc (st1 :: st2 :: tl)
          | _ -> (
              st := state_whnf sg !st;
              match !st with
              | {term = Const (_, cst'); stack = [st1; st2]; _}
                when name_eq cst cst' ->
                  flatten acc (st1 :: st2 :: tl)
              | _ -> flatten (st :: acc) tl))
    in
    flatten []

  and comb_state_if_AC alg sg st =
    if Term.is_AC alg then
      match st with
      | {ctx; term = Const (l, cst); stack = s1 :: s2 :: rstack; _} ->
          let nstack = flatten_AC_stack sg cst [s1; s2] in
          let nstack =
            match alg with
            | ACU neu ->
                List.filter
                  (fun st ->
                    not (C.are_convertible sg (term_of_state_ref st) neu))
                  nstack
            | _ -> nstack
          in
          let combed = to_comb sg l cst ctx nstack in
          let fstack =
            match rstack with [] -> combed.stack | l -> combed.stack @ l
          in
          {combed with stack = fstack}
      | st -> st
    else st

  and comb_term_if_AC sg : term -> term = function
    | App (Const (l, cst), a1, a2 :: remain_args) as t ->
        let alg = Signature.get_algebra sg l cst in
        if is_AC alg then
          let id_comp = Signature.get_id_comparator sg in
          let args = flatten_AC_terms cst [a1; a2] in
          let args = filter_neutral sg l cst args in
          let args = List.sort (compare_term id_comp) args in
          let _ = assert (List.length args > 0) in
          mk_App2 (unflatten_AC (cst, alg) args) remain_args
        else t
    | t -> t

  (*******   Matching with a decision tree  *******)

  and find_case sg (st : state) (case : case) : stack option =
    match (st, case) with
    | {term = Const (_, cst); stack; _}, CConst (nargs, cst', false) ->
        if name_eq cst cst' && List.length stack == nargs then Some stack
        else None
    | {ctx; term = DB (_, _, n); stack; _}, CDB (nargs, n') ->
        assert (ctx = LList.nil);
        (* no beta in patterns *)
        if n == n' && List.length stack == nargs then Some stack else None
    | {term = Lam (_, _, _, _); _}, CLam -> (
        match term_of_state st with
        (*TODO could be optimized*)
        | Lam (_, _, _, te) -> Some [state_ref_of_term te]
        | _ -> assert false)
    | ( {term = Const (_, cst); stack = t1 :: t2 :: s; _},
        CConst (nargs, cst', true) )
      when name_eq cst cst' && nargs == List.length s + 2 ->
        Some (ref {st with stack = flatten_AC_stack sg cst [t1; t2]} :: s)
    (* This case is a bit tricky: when + is AC,
       C (+ f g 1) can match C (h 1)
       The corresponding matching problem is  +{f,g} = +{h}
       which is not necessarily unsolvable in general:
       maybe + is acu and a solution is {f = u, g = h}
       TODO: check that this case is used properly !
    *)
    | {ctx; term; stack}, CConst (nargs, cst, true)
      when List.length stack == nargs - 2 ->
        let new_st = ref {ctx; term; stack = []} in
        let new_stack = flatten_AC_stack sg cst [new_st] in
        Some (ref {ctx; term = mk_Const dloc cst; stack = new_stack} :: stack)
    | _ -> None

  and fetch_case sg (state : state ref) (case : case) (dt_suc : dtree)
      (dt_def : dtree option) : (dtree * state ref * stack) list =
    let def_s = match dt_def with None -> [] | Some g -> [(g, state, [])] in
    let stack = !state.stack in
    match !state.term with
    | Const _ ->
        let rec f acc (stack_acc : state ref list) st =
          match (st, case) with
          | [], _ -> acc
          | hd :: tl, _ ->
              let new_stack_acc = hd :: stack_acc in
              let new_acc =
                match find_case sg !hd case with
                | None -> acc
                | Some s ->
                    let new_stack = List.rev_append stack_acc tl in
                    (* Remove hd from stack *)
                    let new_state = ref {!state with stack = new_stack} in
                    (dt_suc, new_state, s) :: acc
              in
              f new_acc new_stack_acc tl
        in
        List.rev_append (f [] [] stack) def_s
    | _ -> assert false

  and find_cases sg (st : state) (cases : (case * dtree) list)
      (default : dtree option) : (dtree * stack) list =
    List.fold_left
      (fun acc (case, tr) ->
        match find_case sg st case with
        | None -> acc
        | Some stack -> (tr, stack) :: acc)
      (match default with None -> [] | Some g -> [(g, [])])
      cases

  (* TODO implement the stack as an array ? (the size is known in advance). *)
  and gamma_rw (sg : Signature.t) (filter : (Rule.rule_name -> bool) option) :
      stack -> dtree -> (rule_name * env * term) option =
    let rec rw_list : (stack * dtree) list -> (rule_name * env * term) option =
      function
      | [] -> None
      | [(stack, tree)] -> rw stack tree
      | (stack, tree) :: tl -> (
          match rw stack tree with None -> rw_list tl | x -> x)
    and rw (stack : stack) : dtree -> (rule_name * env * term) option = function
      (* Fetch case from AC-headed i-th state
         This may branch and generate many case, one for each possible term to fetch
      *)
      | Fetch (i, case, dt_suc, dt_def) ->
          let rec split_ith acc i l =
            match (i, l) with
            | 0, h :: t -> (acc, h, t)
            | i, h :: t -> split_ith (h :: acc) (i - 1) t
            | _ -> assert false
          in
          let stack_h, arg_i, stack_t = split_ith [] i stack in
          assert (
            match !arg_i.term with
            | Const (l, cst) -> Signature.is_AC sg l cst
            | _ -> false);
          let process (g, new_s, s) =
            ( List.rev_append stack_h
                (new_s :: (match s with [] -> stack_t | s -> stack_t @ s)),
              g )
          in
          let cases =
            (* Generate all possible picks for the fetch *)
            fetch_case sg arg_i case dt_suc dt_def
          in
          let new_cases = List.map process cases in
          rw_list new_cases
          (* ... try them all *)
      | ACEmpty (i, dt_suc, dt_def) -> (
          match !(List.nth stack i) with
          | {term = Const (l, cst); stack = st; _} ->
              assert (Signature.is_AC sg l cst);
              if st = [] then rw stack dt_suc else bind_opt (rw stack) dt_def
          | _ -> assert false)
      | Switch (i, cases, def) ->
          let arg_i = List.nth stack i in
          arg_i := state_whnf sg !arg_i;
          (* Several cases may match !!
                   when max and plus are ACU symbols, they can match anything
                   (max  f g) ... = x ...
                   (plus f g) ... = x ...
                   x          ... = x ...
                   FIXME: This should really be handled by the decision tree.
                   It impacts performance a bit to have a list of size 1 computed then mapped
                   then matched upon (instead of just jumping to the recursive call).
          *)
          let new_cases =
            List.map
              (fun (g, l) -> (concat stack l, g))
              (find_cases sg !arg_i cases def)
          in
          rw_list new_cases
      | Test (rule_name, matching_pb, cstr, right, def) ->
          let keep_rule =
            match filter with None -> true | Some f -> f rule_name
          in
          if keep_rule then (
            (* FIXME: Several calls to [convert(_ac) i] generates different lazy values.
                     Whnf may be computed several times in case of non linearity. *)
            let convert i =
              let te = List.nth stack i in
              lazy (term_of_state_ref te)
            in
            let convert_ac i =
              List.map
                (fun s -> lazy (term_of_state_ref s))
                !(List.nth stack i).stack
            in
            (* Convert problem on stack indices to a problem on terms *)
            match
              M.solve_problem rule_name sg convert convert_ac matching_pb
            with
            | None -> bind_opt (rw stack) def
            | Some ctx ->
                List.iter
                  (fun (i, t2) ->
                    let t1 = Lazy.force (LList.nth ctx i) in
                    let t2 = term_of_state {ctx; term = t2; stack = []} in
                    if
                      not
                        (C.constraint_convertibility (i, t2) rule_name sg t1 t2)
                    then
                      raise
                        (Signature.Signature_error
                           (Signature.GuardNotSatisfied (get_loc t1, t1, t2))))
                  cstr;
                Some (rule_name, ctx, right))
          else bind_opt (rw stack) def
    in
    rw

  (* ************************************************************** *)

  (* This function reduces a state to a weak-head-normal form.
   * This means that the term [term_of_state (state_whnf sg state)] is a
   * weak-head-normal reduct of [term_of_state state].
   *
   * Moreover the returned state verifies the following properties:
   * - state.term is not an application
   * - state.term can only be a variable if term.ctx is empty
   *    (and therefore this variable is free in the corresponding term)
   * - when state.term is an AC constant, then state.stack contains no application
   *     of that same constant
   *)
  and state_whnf (sg : Signature.t) (st : state) : state =
    (*
  Debug.(debug D_reduce "Reducing %a" pp_state_oneline st);
  *)
    if dk_progress then begin
      incr prog_sw_steps;
      (* One-shot: a *single* whnf call has run >400k state_whnf steps without
         returning (measured per-call via [prog_whnf_entry_steps], not the cumulative
         counter): [prog_whnf_entry] is then the self-contained term whose reduction
         does not terminate. Dump it closed over the current typing context (set by
         typing.ml) as a ready-to-run `#EVAL`, plus the current redex for reference. *)
      if (not !prog_sw_dumped)
         && !prog_sw_steps - !prog_whnf_entry_steps > 400_000
         && !prog_sw_steps land 0x3F = 0
      then begin
        prog_sw_dumped := true;
        let cur = try term_of_state st with _ -> st.term in
        let closed t = List.fold_left
            (fun body (l, x, a) -> mk_Lam l x (Some a) body) t !prog_typing_ctx in
        (try
           let oc = open_out "/tmp/dk_whnf_entry.txt" in
           let fmt = Format.formatter_of_out_channel oc in
           (match !prog_whnf_entry with
            | Some e ->
                Format.fprintf fmt "WHNF_ENTRY (raw, may have free DB vars):@.%a@.@." pp_term e;
                Format.fprintf fmt
                  "WHNF_ENTRY_CLOSED (lambda-closed over typing ctx, %d binders):@.%a@.@."
                  (List.length !prog_typing_ctx) pp_term (closed e)
            | None -> Format.fprintf fmt "(no whnf entry captured)@.@.");
           Format.fprintf fmt "CURRENT_REDEX (state_whnf step %d):@.%a@."
             !prog_sw_steps pp_term cur;
           Format.pp_print_flush fmt ();
           close_out oc;
           Printf.eprintf "    [dumped looping whnf entry to /tmp/dk_whnf_entry.txt]\n%!"
         with _ -> ())
      end;
      if !prog_sw_steps land 0x3FFF = 0 then begin
        check_mem ();
        let now = try Unix.gettimeofday () with _ -> 0.0 in
        if now -. !prog_sw_last_t >= 2.0 then begin
          prog_sw_last_t := now;
          let cur = try term_of_state st with _ -> st.term in
          Format.eprintf "[DK_WHNF] %s: state_whnf step %d  redex: %a@."
            !prog_decl !prog_sw_steps (pp_trunc 12) cur;
          Printf.eprintf "    rule firings (top): %s\n%!" (prog_rule_top ())
        end
      end
    end;
    let rec_call ctx term stack = state_whnf sg {ctx; term; stack} in
    let compute () =
    match st with
    (* Weak head beta normal terms *)
    | {term = Type _; _}
    | {term = Kind; _}
    | {term = Pi _; _}
    | {term = Lam _; stack = []; _} ->
        st
    (* DeBruijn index: environment lookup *)
    | {ctx; term = DB (l, x, n); stack} ->
        if LList.is_empty ctx then st
        else if n < LList.len ctx then
          state_whnf sg
            {ctx = LList.nil; term = Lazy.force (LList.nth ctx n); stack}
        else {ctx = LList.nil; term = mk_DB l x (n - LList.len ctx); stack}
    (* Beta redex *)
    | {ctx; term = Lam (_, _, _, t); stack = p :: s; _} ->
        if not !beta then st
        else rec_call (LList.cons (lazy (term_of_state_ref p)) ctx) t s
    (* Application: arguments go on the stack *)
    | {ctx; term = App (f, a, lst); stack = s; _} ->
        (* rev_map + rev_append to avoid map + append*)
        let tl' =
          List.rev_map (fun t -> ref {ctx; term = t; stack = []}) (a :: lst)
        in
        rec_call ctx f (List.rev_append tl' s)
    (* Potential Gamma redex *)
    | {ctx; term = Const (l, n); stack; _} -> (
        let trees = !dtree_finder sg l n in
        match find_dtree (List.length stack) trees with
        | alg, None -> comb_state_if_AC alg sg st
        | alg, Some (ar, tree) -> (
            let s1, s2 = split ar stack in
            let s1 =
              if ar > 1 && Term.is_AC alg then
                match s1 with
                | t1 :: t2 :: tl ->
                    let flat = flatten_AC_stack sg n [t1; t2] in
                    ref {ctx; term = mk_Const l n; stack = flat} :: tl
                | _ -> assert false
              else s1
            in
            match gamma_rw sg !selection s1 tree with
            | None -> comb_state_if_AC alg sg st
            | Some (_, ctx, term) ->
                if dk_progress then prog_rule_bump n;
                rec_call ctx term s2))
    in
    (* Reduction sharing (DK_MEMO): memoize the whnf of closed, unapplied states
       whose head is a (potential) redex, so a duplicated subterm is reduced once.
       Sound within a fixed signature + full rule selection; the cache is cleared
       per declaration by the typing module (whnf is not monotone in the signature). *)
    match st with
    | {ctx; term; stack = []}
      when dk_memo && LList.is_empty ctx
           && (match !selection with None -> true | _ -> false)
           && (match term with Const _ | App (Const _, _, _) -> true | _ -> false) -> (
        match WhnfCache.find_opt whnf_cache term with
        | Some s ->
            if dk_progress then incr whnf_hits;
            s
        | None ->
            let s = compute () in
            WhnfCache.replace whnf_cache term s;
            s)
    | _ -> compute ()

  (* ************************************************************** *)

  (* Weak Head Normal Form *)
  and whnf sg term =
    if dk_progress then (
      incr prog_whnf;
      prog_whnf_entry := Some term;
      prog_whnf_entry_steps := !prog_sw_steps;
      if !prog_whnf land 0x3FFF = 0 then prog_beat ());
    term_of_state (state_whnf sg (state_of_term term))

  (* Strong Normal Form *)
  and snf sg (t : term) : term =
    match whnf sg t with
    | (Kind | Const _ | DB _ | Type _) as t' -> t'
    | App (f, a, lst) ->
        let res = mk_App (snf sg f) (snf sg a) (List.map (snf sg) lst) in
        comb_term_if_AC sg res
    | Pi (_, x, a, b) -> mk_Pi dloc x (snf sg a) (snf sg b)
    | Lam (_, x, a, b) -> mk_Lam dloc x (map_opt (snf sg) a) (snf sg b)

  and conversion_step sg :
      term * term -> (term * term) list -> (term * term) list =
   fun (l, r) lst ->
    match (l, r) with
    | Kind, Kind | Type _, Type _ -> lst
    | Const (_, n), Const (_, n') when name_eq n n' -> lst
    | DB (_, _, n), DB (_, _, n') when n == n' -> lst
    | App (Const (lc, cst), _, _), App (Const (_, cst'), _, _)
      when Signature.is_AC sg lc cst && name_eq cst cst' -> (
        (* TODO: Eventually replace this with less hardcore criteria: put all terms in whnf
         * then look at the heads to match arguments with one another.
         * Careful, this is tricky:
         * The whnf would need here to make sure that no reduction may occur at the AC-head.
         * Whenever  max n n --> n,   the whnf of "max a (max a b)" should be "max a b"
         * If not all head reduction are exhausted, then comparing AC argument sets is not enough
         *)
        match (snf sg l, snf sg r) with
        | App (Const (_, cst2), a, args), App (Const (_, cst2'), a', args')
          when name_eq cst2 cst && name_eq cst2' cst && name_eq cst2 cst'
               && name_eq cst2' cst' ->
            (a, a') :: zip_lists args args' lst
        | p -> p :: lst)
    | App (f, a, args), App (f', a', args') ->
        (f, f') :: (a, a') :: zip_lists args args' lst
    | Lam (_, _, _, b), Lam (_, _, _, b') -> (b, b') :: lst
    (* Potentially eta-equivalent terms *)
    | Lam (_, i, _, b), a when !eta ->
        let b' = mk_App (Subst.shift 1 a) (mk_DB dloc i 0) [] in
        (b, b') :: lst
    | a, Lam (_, i, _, b) when !eta ->
        let b' = mk_App (Subst.shift 1 a) (mk_DB dloc i 0) [] in
        (b, b') :: lst
    | Pi (_, _, a, b), Pi (_, _, a', b') -> (a, a') :: (b, b') :: lst
    | t1, t2 ->
        Debug.(debug d_reduce "Not convertible: %a / %a" pp_term t1 pp_term t2);
        raise Not_convertible

  let rec are_convertible_lst sg : (term * term) list -> bool = function
    | [] -> true
    | (t1, t2) :: lst ->
        if dk_progress then (
          incr prog_conv;
          if pair_is_level t1 t2 then incr prog_conv_lvl else incr prog_conv_oth;
          prog_cur := Some (t1, t2);
          if !prog_conv land 0x3FFF = 0 then (check_mem (); prog_beat ()));
        (* Check physical equality first for optimisation. *)
        if t1 == t2 then are_convertible_lst sg lst
          (* This test can be less expensive than computing the `whnf` if the
             two terms are equal. *)
        else if term_eq t1 t2 then are_convertible_lst sg lst
        else if dk_lazy_delta && lazy_delta_congruent sg t1 t2 then
          (* Closed by arg-wise congruence without unfolding the shared head. *)
          are_convertible_lst sg lst
        else are_convertible_lst sg (conversion_step sg (whnf sg t1, whnf sg t2) lst)

  (* Lazy-delta congruence (see [dk_lazy_delta]): [t1] and [t2] are applications
     of the same non-AC constant to the same number of arguments, all pairwise
     convertible. *)
  and lazy_delta_congruent sg (t1 : term) (t2 : term) : bool =
    match (t1, t2) with
    | App (Const (lc, f), a1, r1), App (Const (_, f2), a2, r2)
      when name_eq f f2
           && (not (Signature.is_AC sg lc f))
           && List.length r1 = List.length r2 ->
        are_convertible sg a1 a2 && List.for_all2 (are_convertible sg) r1 r2
    | _ -> false

  (* Convertibility Test *)
  and are_convertible sg t1 t2 =
    if dk_progress then (
      if !prog_depth = 0 then prog_seed := Some (t1, t2);
      incr prog_depth);
    (* Memoize positive level-convertibility under the full rule set (see header).
       Restricted to level pairs: caching all pairs was tried and only bloated memory
       on `denote_toNormPoly` (its comparison pairs are largely distinct, so nothing is
       reused) without collapsing the work. *)
    let memoable =
      dk_memo && (match !selection with None -> true | _ -> false)
      && pair_is_level t1 t2
    in
    let r =
      if memoable && ConvCache.mem conv_cache (t1, t2) then (
        incr conv_hits;
        true)
      else
        let b =
          try are_convertible_lst sg [(t1, t2)]
          with Not_convertible | Invalid_argument _ -> false
        in
        if memoable && b then ConvCache.replace conv_cache (t1, t2) ();
        b
    in
    if dk_progress then decr prog_depth;
    r

  (* ************************************************************** *)

  type state_reducer = position -> state -> state

  type term_reducer = position -> term -> term

  let logged_state_whnf log stop (strat : red_strategy) (sg : Signature.t) :
      state_reducer =
    let rec aux : state_reducer =
     fun (pos : position) (st : state) ->
      if stop () then st
      else
        match (st, strat) with
        (* Weak head beta normal terms *)
        | {term = Type _; _}, _ | {term = Kind; _}, _ -> st
        | {term = Pi _; _}, ByName | {term = Pi _; _}, ByValue -> st
        | {ctx; term = Pi (l, x, a, b); _}, ByStrongValue ->
            let a' =
              term_of_state (aux (0 :: pos) {ctx; term = a; stack = []})
            in
            (* Should we also reduce b ? *)
            {st with term = mk_Pi l x a' b}
        (* Reducing type annotation *)
        | {ctx; term = Lam (l, x, Some ty, t); stack = []; _}, ByStrongValue ->
            let ty' =
              term_of_state (aux (0 :: pos) {ctx; term = ty; stack = []})
            in
            {st with term = mk_Lam l x (Some ty') t}
        (* Empty stack *)
        | {term = Lam _; stack = []; _}, _ -> st
        (* Beta redex with type annotation *)
        | {ctx; term = Lam (l, x, Some ty, t); stack = p :: s; _}, ByStrongValue
          ->
            let ty' =
              term_of_state (aux (0 :: pos) {ctx; term = ty; stack = []})
            in
            if stop () || not !beta then
              {st with term = mk_Lam l x (Some ty') t}
            else
              let st' =
                {
                  ctx = LList.cons (lazy (term_of_state_ref p)) ctx;
                  term = t;
                  stack = s;
                }
              in
              let _ = log pos Rule.Beta st st' in
              aux pos st'
        (* Beta redex *)
        | {ctx; term = Lam (_, _, _, t); stack = p :: s; _}, _ ->
            if not !beta then st
            else
              let st' =
                {
                  ctx = LList.cons (lazy (term_of_state_ref p)) ctx;
                  term = t;
                  stack = s;
                }
              in
              let _ = log pos Rule.Beta st st' in
              aux pos st'
        (* DeBruijn index: environment lookup *)
        | {ctx; term = DB (l, x, n); stack; _}, _ ->
            if n < LList.len ctx then
              aux pos
                {ctx = LList.nil; term = Lazy.force (LList.nth ctx n); stack}
            else {ctx = LList.nil; term = mk_DB l x (n - LList.len ctx); stack}
        (* Application: arguments go on the stack *)
        | {ctx; term = App (f, a, lst); stack; _}, ByName ->
            (* rev_map + rev_append to avoid map + append *)
            let tl' =
              List.rev_map (fun t -> ref {ctx; term = t; stack = []}) (a :: lst)
            in
            aux pos {ctx; term = f; stack = List.rev_append tl' stack}
        (* Application: arguments are reduced to values then go on the stack *)
        | {ctx; term = App (f, a, lst); stack; _}, _ ->
            let arg_reduce i t =
              ref (aux (i :: pos) {ctx; term = t; stack = []})
            in
            let tl' = rev_mapi arg_reduce (a :: lst) in
            aux pos {ctx; term = f; stack = List.rev_append tl' stack}
        (* Potential Gamma redex *)
        | {ctx; term = Const (l, n); stack; _}, _ -> (
            let trees = !dtree_finder sg l n in
            match find_dtree (List.length stack) trees with
            | alg, None -> comb_state_if_AC alg sg st
            | alg, Some (ar, tree) -> (
                let s1, s2 = split ar stack in
                let s1 =
                  if ar > 1 && Term.is_AC alg then
                    match s1 with
                    | t1 :: t2 :: tl ->
                        let flat = flatten_AC_stack sg n [t1; t2] in
                        ref {ctx; term = mk_Const l n; stack = flat} :: tl
                    | _ -> assert false
                  else s1
                in
                match gamma_rw sg !selection s1 tree with
                | None -> comb_state_if_AC alg sg st
                | Some (rn, ctx, term) ->
                    let st' = {ctx; term; stack = s2} in
                    log pos rn st st'; aux pos st'))
    in
    aux

  let term_whnf (st_reducer : state_reducer) : term_reducer =
   fun pos t -> term_of_state (st_reducer pos (state_of_term t))

  let term_snf (st_reducer : state_reducer) : term_reducer =
    let rec aux pos t =
      match term_whnf st_reducer pos t with
      | (Kind | Const _ | DB _ | Type _) as t' -> t'
      | App (f, a, lst) ->
          mk_App
            (aux (0 :: pos) f)
            (aux (1 :: pos) a)
            (List.mapi (fun p arg -> aux (p :: pos) arg) lst)
      | Pi (_, x, a, b) -> mk_Pi dloc x (aux (0 :: pos) a) (aux (1 :: pos) b)
      | Lam (_, x, a, b) ->
          mk_Lam dloc x (map_opt (aux (0 :: pos)) a) (aux (1 :: pos) b)
    in
    aux

  let reduction cfg sg te =
    let log, stop =
      match cfg.nb_steps with
      | None -> ((fun _ _ _ _ -> ()), fun () -> false)
      | Some n ->
          let aux = ref n in
          ((fun _ _ _ _ -> decr aux), fun () -> !aux <= 0)
    in
    let st_logger p rn stb sta =
      log p rn stb sta;
      cfg.logger p rn (lazy (term_of_state stb)) (lazy (term_of_state sta))
    in
    let st_red = logged_state_whnf st_logger stop cfg.strat sg in
    let term_red =
      match cfg.target with Snf -> term_snf | Whnf -> term_whnf
    in
    selection := cfg.select;
    beta := cfg.beta;
    dtree_finder := cfg.finder;
    let te' = term_red st_red [] te in
    selection := default_cfg.select;
    beta := default_cfg.beta;
    dtree_finder := default_cfg.finder;
    te'

  let are_convertible = are_convertible

  let constraint_convertibility _ _ = are_convertible
end

module rec Default : S = Make (Default) (Matching.Make (Default))
