# MassDescentRecursion — full recursive child cost, exact multiplicities, anchor charging

Lean source: `RequestProject/Root/CodingTheory/MassDescentRecursion.lean`.
Axiom audit: `RequestProject/MassDescentRecursionAxiomAudit.lean` (only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`).
Prerequisite: `BRANCHING_CONTROL_REPORT.md` (`BranchingControl.lean`).

## Notation (unchanged)

```
tauMax = τ = maximal correlated agreement      t = n − e = official support threshold
s      = τ − k                                 a = window mass of an official witness
w      = n − k − e                             μR = parent multiplicity of the child class R
C(R)   = full recursive bad-cost of child R    cR = μR · C(R)
```

## 1. Why this file exists

`BranchingControl` gives the covering bound `#Bad ≤ (e+1) + Σ_{R ∈ childClasses} C(R)`, a sum over
the *index set* of admissible child classes.  It says nothing about how many parent challenges
actually reach a given child, and it can only be closed by bounding the number of children — the
`#children × max child cost` route, which is not available (the a priori child count is
astronomical).  This file replaces that with:

* the **exact** multiplicity decomposition of the recursive cost, and
* a **charging** of the recursive cost onto coordinates,

so that the branching factor never appears.

## 2. Canonical objects (all choice-fixed, so they are honest functions)

* `officialWitness k e f₀ f₁ γ` — a *fixed* choice of positive-mass official witness `(p, S)`
  (`p ≠ 0`, `deg p < k`, `|S| ≥ t`, `f₀ + γ f₁ = p` on `S`), `(0, ∅)` when none exists.
  `officialWitness_spec` gives its defining property whenever one exists, and
  `exists_officialWitness_of_mem_posBadSet` shows one exists for every non-terminal bad challenge.
* `officialClass k e A f₀ f₁ γ = windowZeros A p` — the **canonical residual child class**.
* `classCost k e A R f₀ f₁ = #Bad(child R)` — the **full recursive** cost of the child instance
  `(D ∖ A, k − |R|, e − a)`; `childCost … γ = classCost … (officialClass … γ)`.
* `parentMult k e A R f₀ f₁ = μR` — the number of parent challenges with class `R`.
* `totalChildCost k e A f₀ f₁ = Σ_{γ ∈ Bad⁺} childCost γ`.

**Canonical child equivalence** (`officialClass_determines_child`): challenges with equal class
have the same residual dimension, radius, words and cost — the child depends on the challenge only
through its class.  **Exact transport** (`officialWitness_shortened`, `mem_resBadSet_official`):
`p = V_Z · r`, `r ≠ 0`, `deg r < k₁ = k − |Z|`, the residual line point *is* `r` on the residual
support, and the challenge is again bad for the child RS instance.  The descent invariants come
from `BranchingControl` via `officialClass_mem_childClasses`:
`officialClass_capacity_gap` (`n₁ = k₁ + e₁ + w`, so `w` is preserved) and
`officialClass_complexity_lt` (`e₁ < e` and `k₁ + e₁ < k + e`).

## 3. Exact multiplicity, no double counting

```
card_posBadSet_eq_sum_parentMult :  #Bad⁺        = Σ_R μR
totalChildCost_eq_sum_parentMult :  totalChildCost = Σ_R μR · C(R)
parentMult_le_classCost          :  μR ≤ C(R)
```

The fibres of `officialClass` partition `Bad⁺` (each challenge is assigned to exactly one class,
and its cost is counted against exactly one child), which is what "no double counting" means here.
`fibre_subset_resBadSet` is the reason `μR ≤ C(R)`: the whole fibre lives inside that single
child's bad set.

Consequently the one-step recursion carries the **full recursive** child cost:

```
card_badSet_le_terminal_add_totalChildCost :  #Bad ≤ (e + 1) + Σ_R μR · C(R)
```

which is strictly stronger than bounding `Σ_R μR = #Bad⁺`, since `C(R) ≥ μR ≥ 1` on occupied
classes.  The terminal `e + 1` is the zero-witness branch (`card_zeroWitnessBadSet_le_succ`).

## 4. The anchor charging

Fix an **anchor** challenge `γ₀` of window mass `0` with support `S0`, `|S0| ≥ t` (i.e. a terminal,
zero-witness challenge).  For a positive-mass challenge `γ` with official support `S_γ` define

```
chargeSet  D_γ = (S_γ ∖ A) ∖ S0 ,      chargeLoad  load(i) = Σ_{γ : i ∈ D_γ} C(class γ) .
```

Two facts:

* `card_chargeSet_ge`:  `|D_γ| ≥ w − s`.  Indeed `|S_γ ∖ A| ≥ (w − s) + a` (the official support
  beats the threshold outside the window by the mass), while the exact challenge transport against
  a *zero-mass* anchor gives `|(S_γ ∩ S0) ∖ A| ≤ a + 0`; subtracting leaves `w − s`.
* `chargeSet_subset` + `card_compl_anchor_le`: all charges land in `univ ∖ S0`, which has at most
  `e` coordinates.

Double counting (`sum_chargeLoad_eq`, `massDescent_charging`) then gives the **primary target**

```
(w − s) · Σ_R μR·C(R)  ≤  Σ_{i ∉ S0} load(i)  ≤  e · M_X      (massDescent_load_bound)
```

for any uniform bound `M_X` on the per-coordinate load, and hence the closed bounds

```
card_badSet_le_of_load_bound :  (w − s) · (#Bad − (e+1)) ≤ e · M_X
card_badSet_le_potential     :  #Bad ≤ Φ ,  Φ = (e + 1) + e·M_X/(w − s) .
```

`Φ` is the amortised potential asked for: the local terminal cost `e + 1` plus the charged share of
the recursive cost.  The abstract pattern is isolated as `cost_le_potential`: on any state space
with a well-founded complexity, a potential satisfying
`localCost X + Σ_Y mult X Y · Φ Y ≤ Φ X` dominates a cost satisfying
`cost X ≤ localCost X + Σ_Y mult X Y · cost Y`.  Here the concrete descent is
`officialClass_complexity_lt` (`k₁ + e₁ < k + e`, `e₁ < e`; note `e` is *not* assumed to drop by
`w`).

## 5. The exact remaining obstruction

`exists_concentrated_coordinate` is unconditional: for `0 < w − s`, either

* `#Bad ≤ e + 1` (the positive-mass branch is empty — terminal), or
* **some single coordinate `i ∉ S0` carries `(w − s)/e` of the entire recursive cost**:
  `(w − s) · totalChildCost ≤ e · load(i)`.

So the recursion is summable exactly when the per-coordinate recursive load is bounded away from
the total; nothing else is missing.  This is the precise, formal statement of the obstruction:
the charging is complete, and it fails to close only through the load.  Note that the trivial
bound `load(i) ≤ totalChildCost` makes the inequality vacuous, so any progress must show that the
recursive cost cannot concentrate on one coordinate outside the anchor — a *spread* statement about
the official supports of positive-mass witnesses, not a counting statement.

`massDescent_master` packages the four items (multiplicity decomposition, one-step recursion with
the full recursive cost, charging inequality, dichotomy) into one theorem.

## 6. Deployed

`n = 2²¹`, `k = 2²⁰`, `e = 978944`, `w = 69632`, `s = 0`:

```
deployed_massDescent        :  69632 · (#Bad − 978945) ≤ 978944 · M_X
deployed_massDescent_budget :  M_X ≤ 19·10¹⁵  ⇒  #Bad ≤ B* = 274980728111395087
```

The concentration fraction is `(w − s)/e = 69632/978944 = 1/14.06`: some coordinate outside the
anchor support must carry more than a fourteenth of the entire recursive cost.

## 7. Non-claims

* No unconditional bound on `#Bad` in the positive-mass branch is claimed; the closed bounds are
  conditional on a per-coordinate load bound `M_X`, stated as an explicit hypothesis.
* `#children × max child cost` is never used, and no assumption is made that `e` drops by `w`.
* The anchor must be a genuine zero-mass (terminal) challenge; with an anchor of mass `a₀` the same
  argument only yields `|D_γ| ≥ (w − s) − a₀`, which is why the hypothesis is stated as
  `∀ x ∈ S0, f₀ x + γ₀ f₁ x = 0` with `|S0| ≥ t`.
