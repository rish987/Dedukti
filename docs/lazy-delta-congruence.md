# `DK_LAZY_DELTA`: lazy-delta congruence in the conversion checker

This fork adds an opt-in tweak to the kernel's convertibility test
(`kernel/reduction.ml`), enabled by the environment variable **`DK_LAZY_DELTA`**
(set to any non-empty value).

## What it does

When `are_convertible_lst` is about to compare a pair `(t1, t2)` and the cheap
checks (`==`, `term_eq`) have failed, the stock behaviour is to `whnf` **both**
sides and then decompose with `conversion_step`. If `t1`/`t2` are headed by a
*defined* constant `f`, `whnf` **unfolds** `f` before any congruence is tried.

With `DK_LAZY_DELTA` set, we first check whether both terms are applications of
the **same non-AC constant** `f` to the **same number of arguments**, and if so
try to close the pair by **arg-wise convertibility (congruence)**:

```
f a1 … an  ≡  f b1 … bn      if   a1 ≡ b1   ∧ … ∧   an ≡ bn
```

Only if that fails do we fall back to the usual `whnf`-based step. This mirrors
the lazy-delta `isDefEqArgs` step in Lean's kernel (`isDefEqCore`).

## Why

A term translated from a Lean well-founded definition (e.g. `Nat.modCore`)
unfolds, via the `WellFounded.fix`/`Acc.rec` encoding, into an accessibility
proof whose **strong normal form does not exist** for a symbolic argument (an
infinite `Nat.rec`/`Nat.below`/`PProd` tower — this is the well-known fact that
Lean's kernel reduction is not strongly normalizing; it is safe only because the
kernel is *lazy*). When two such terms must be compared (e.g. the two sides of a
`modCore = mod` equation, written with `Nat.succ n` on one side and `n + 1` on
the other), stock Dedukti `whnf`-unfolds the recursor and is dragged into that
non-terminating reduction.

Lean avoids this by comparing the recursor's *arguments* first (they are
convertible — `succ n ≡ n + 1`) and never unfolding the recursor. `DK_LAZY_DELTA`
gives Dedukti the same escape hatch.

## Soundness

Congruence is always valid, so accepting a pair via the new path never accepts a
non-convertible pair. When the arguments are *not* convertible we fall back to
the original `whnf`-based comparison, so nothing that converted before stops
converting (completeness preserved). AC-headed symbols are excluded, since they
require the set-based comparison already implemented in `conversion_step`.

## Effect

Checking the lean2dk translation of `Init.Data.Nat.Div.Basic` (which contains
the `Nat.modCore`/`Nat.mod` well-founded definitions and their equation lemmas):

| | stock | `DK_LAZY_DELTA=1` |
|---|---|---|
| `Init_Data_Nat_Div_Basic.dk` | does not terminate (killed after >26 min) | **`SUCCESS` in ~5 s** |
| full enc/ + out/ recheck (18 files) | — | all `SUCCESS`, 0 errors |

## Usage

```
DK_LAZY_DELTA=1 dk check -I enc -I out --eta -e <file>.dk
```

Off by default, so stock behaviour is unchanged unless the variable is set.

## Background

Discovered while debugging [lean2dk](https://github.com/rish987/lean2dk) (a
Lean→Dedukti translator). The non-termination is documented, with a kernel-side
reproducer, on the `acc-wf-nontermination-demo` branch of
[Lean4Lean](https://github.com/rish987/Lean4Lean).
