# Official canonical residual ledger — audit verdict

**VERDICT: `MISSING_INTERFACE`**

The deployed target `Σ_R μ_R Φ(R) ≤ T = 19559298652205332` can be *stated* with the interfaces that
are source-present, but it cannot be derived from them: a named canonical interface that bounds the
family quantity is absent. The obstruction is of the second preferred kind — a **proved theorem
that the currently exported official semantics leave the relevant family quantity unconstrained**
(`ledger_sum_unbounded`, `ledger_sum_unbounded_with_child_cap`,
`ledger_load_unbounded_with_child_cap`). No admissible official Reed–Solomon counterexample is
produced, so the target is **not** labelled `REFUTED`.

All new material is in
`RequestProject/Root/CodingTheory/ResidualLedgerAudit.lean`
(axiom-checked in `RequestProject/ResidualLedgerAuditAxiomAudit.lean`; every statement below
depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no new `axiom`).

---

## STEP 0 — frozen interfaces (reconstructed from source, not invented)

| notion | source declaration | file | exact type / definition |
|---|---|---|---|
| child support `C_R` | `officialSupport k e f₀ f₁ γ` | `MassDescentRecursion.lean:165` | `(officialWitness k e f₀ f₁ γ).2 : Finset ↥D` |
| `chargeSet(R)` (challenge level) | `chargeSet k e A S0 f₀ f₁ γ` | `MassDescentRecursion.lean:351` | `(officialSupport k e f₀ f₁ γ \ A) \ S0` |
| `chargeSet(R)` (class level) | `classChargeSet k e A S0 f₀ f₁ γ₀ R` | `GlobalRecursionLoadGate.lean:341` | `chargeSet k e A S0 f₀ f₁ (classRep k e A f₀ f₁ γ₀ R)` |
| canonical residual child class `R` | `officialClass k e A f₀ f₁ γ` | `MassDescentRecursion.lean:169` | `windowZeros A (officialWitness k e f₀ f₁ γ).1 : Finset ↥D` |
| child-class equivalence | `officialClass_determines_child` | `MassDescentRecursion.lean:216` | equal class ⇒ equal `resDim`, `resRad`, `resWord`, `childCost` |
| child multiplicity `μ_R` | `capturedMult k e A R f₀ f₁ γ₀` | `GlobalAnchorRecursion.lean:399` | `((posBadSet k e f₀ f₁).erase γ₀).filter (officialClass … = R) |>.card` |
| recursive child cost `Φ(R)` | `classCost k e A R f₀ f₁` | `MassDescentRecursion.lean:191` | `(resBadSet k e A R f₀ f₁).card` |
| `capturedChildCost` | `capturedChildCost k e A f₀ f₁ γ₀` | `GlobalAnchorRecursion.lean:408` | `∑ γ ∈ capturedChallenges …, childCost …`, equal to `Σ_R μ_R Φ(R)` by `capturedChildCost_eq_sum_capturedMult` |
| `classLoad(i)` | `classLoad k e A S0 f₀ f₁ γ₀ i` | `GlobalRecursionLoadGate.lean:353` | `∑ R ∈ capturedClasses …, if i ∈ classChargeSet … R then μ_R * Φ(R) else 0` |
| `localCost` | **no canonical RS-level definition** | `GlobalAnchorRecursion.lean:98`, `GlobalRecursionLoadGate.lean:69` | only an abstract bound variable `localCost : σ → ℕ` in `globalCost` / `radius_descent_cost_bound` |
| `terminalCost` | **no declaration of that name** | `MassDescentRecursion.lean:336` | present only as the literal `e + 1` in `card_badSet_le_terminal_add_totalChildCost` (via `card_zeroWitnessBadSet_le_succ`) |
| anchor data | `AnchorData k e f₀ f₁` | `GlobalAnchorRecursion.lean:205` | challenge `chal`, poly `poly` (`deg < k`), support `supp` with `D.card ≤ supp.card + e`, witness `wit`; mass `anchorMass A an = windowMass A an.poly` |
| official witness semantics | `IsOfficialWitness`, `officialWitness`, `officialWitness_spec` | `MassDescentRecursion.lean:146–157` | `q.1 ≠ 0 ∧ deg q.1 < k ∧ D.card ≤ q.2.card + e ∧ ∀ x ∈ q.2, lineComb f₀ f₁ γ x = q.1.eval x` |
| official bad-challenge semantics | `IsBad`, `badSet`, `posBadSet` | `MCA.lean:106,115`, `MassDescentRecursion.lean:177` | `posBadSet = badSet \ zeroWitnessBadSet` |
| `residualTransition` | `Absorption.residualTransition` | `LostFiltrationResidualTriple.lean:128` | linear map of the residual triple; **not** part of the deployed cost ledger |

**Deployed quantity required by the final reduction.** `deployed_load_gate`
(`GlobalRecursionLoadGate.lean`) consumes
`LoadGate … := ∀ i ∈ univ \ an.supp, classLoad 1048576 978944 A an.supp f₀ f₁ an.chal i ≤ 19559298652205332`.
The adapter from the ledger sum is `classLoad_le_capturedChildCost` (unconditional), packaged as
`deployed_bound_of_capturedChildCost`:

```
capturedChildCost 1048576 978944 A f₀ f₁ an.chal ≤ 19559298652205332  →  #Bad ≤ 274980728111395087
```

So the remaining target **is** exactly `Σ_R μ_R Φ(R) ≤ T` (no further adapter needed); strictly, the
reduction only needs the weaker per-coordinate quantity `sup_i classLoad(i) ≤ T`. Both are audited
below.

---

## 1. Exact theorem / obstruction

### 1a. Adequacy of the abstracted ledger (so the obstruction is about the *official* data)

`ResidualLedger κ ι` (new) has fields `n k e w`, `classes`, `size`, `mult`, `cost`, `charge`,
`ground` and exactly the exported inequalities:

```
params        : n = k + e + w
ground_le     : ground.card ≤ e
size_le       : ∀ R ∈ classes, size R ≤ k
mult_pos      : ∀ R ∈ classes, 1 ≤ mult R
mult_le_cost  : ∀ R ∈ classes, mult R ≤ cost R
charge_subset : ∀ R ∈ classes, charge R ⊆ ground
width_le      : ∀ R ∈ classes, w ≤ (charge R).card
charge_le_rho : ∀ R ∈ classes, (charge R).card + size R + 1 ≤ n
```

Charge sets are **not** assumed disjoint, and no support-partition identity
(`Σ_R μ_R |C_R| = n − r`) is used anywhere.

`officialLedger hD hA hcard an h0 : ResidualLedger (Finset ↥D) ↥D` builds this structure from the
deployed official data, and

* `officialLedger_sum : (officialLedger …).sum = capturedChildCost 1048576 978944 A f₀ f₁ an.chal`
* `officialLedger_load : (officialLedger …).load i = classLoad 1048576 978944 A an.supp f₀ f₁ an.chal i`

The abstract charging inequality `ResidualLedger.charging : w * L.sum ≤ Σ_{i ∈ ground} L.load i`
reproduces `classLoad_charging`, and `ResidualLedger.load_le_sum` reproduces
`classLoad_le_capturedChildCost`.

### 1b. The independence theorems (the obstruction)

```
ledger_sum_unbounded (T : ℕ) :
  ∃ L : ResidualLedger Unit (Fin 978944),
    L.n = 2097152 ∧ L.k = 1048576 ∧ L.e = 978944 ∧ L.w = 69632 ∧ T < L.sum

ledger_sum_unbounded_with_child_cap :
  ∃ L : ResidualLedger (Fin 978944) (Fin 978944),
    L.n = 2097152 ∧ L.k = 1048576 ∧ L.e = 978944 ∧ L.w = 69632 ∧
      (∀ R ∈ L.classes, L.cost R ≤ 1048576) ∧ 19559298652205332 < L.sum

ledger_load_unbounded_with_child_cap :
  ∃ L : ResidualLedger (Fin 978944) (Fin 978944), … ∧
      ∃ i ∈ L.ground, 19559298652205332 < L.load i
```

Hence no implication "ledger axioms ⇒ `Σ_R μ_R Φ(R) ≤ T`" and no implication
"ledger axioms ⇒ `classLoad(i) ≤ T`" exists, even after adding the per-class child-cost cap
`Φ(R) ≤ 1048576`. Since the official deployed data satisfies exactly these axioms (1a), any proof of
the deployed target must use official semantics *beyond* the exported ledger.

### 1c. The smallest sufficient missing interface

```
deployed_capturedChildCost_le_of_interfaces
  {N B : ℕ}
  (hN : (capturedChallenges 1048576 978944 f₀ f₁ γ₀).card ≤ N)
  (hB : ∀ γ ∈ capturedChallenges 1048576 978944 f₀ f₁ γ₀,
          childCost 1048576 978944 A f₀ f₁ γ ≤ B)
  (hNB : N * B ≤ 19559298652205332) :
  capturedChildCost 1048576 978944 A f₀ f₁ γ₀ ≤ 19559298652205332
```

together with `deployed_bound_of_interfaces`, which chains it to `#Bad ≤ 274980728111395087`.

So exactly two named interfaces are missing at the deployed root:

* **(I1) a root count interface** `card_capturedChallenges_le : #((posBadSet).erase γ₀) ≤ N`, i.e. a
  proximity-gap / list-size statement at `(n,k,e) = (2097152, 1048576, 978944)`;
* **(I2) a child-cost interface** `classCost … R … ≤ B` for *all* captured classes.

`ledger_sum_unbounded_with_child_cap` shows (I2) alone is insufficient; (I1) alone is insufficient
by the same models with `mult` inflated. The strong form shows the missing content is essentially a
bound on `Σ_R μ_R`, which is a `#Bad`-type quantity — it must come from RS semantics, not from the
ledger.

---

## 2. Exact source declarations used

Consumed unchanged (all pre-existing, all `sorry`-free):

`badSet`, `IsBad`, `card_badSet_le` (`MCA.lean`); `resDomain`, `card_resDomain`, `resDim`,
`resRad`, `resWord`, `resBadSet` (`BranchingControl.lean`); `NormalisedWindow`
(`TauWindowClassification.lean`); `officialWitness`, `officialSupport`, `officialClass`,
`posBadSet`, `classCost`, `childCost`, `parentMult`, `parentMult_le_classCost`, `chargeSet`,
`chargeSet_subset`, `card_compl_anchor_le` (`MassDescentRecursion.lean`); `AnchorData`,
`anchorMass`, `capturedChallenges`, `capturedClasses`, `capturedMult`, `anchorMult`,
`capturedMult_add_anchorMult`, `capturedChildCost`, `capturedChildCost_eq_sum_capturedMult`
(`GlobalAnchorRecursion.lean`); `classRep`, `classChargeSet`, `classLoad`, `classLoad_charging`,
`classLoad_bound`, `LoadGate`, `deployed_load_gate` (`GlobalRecursionLoadGate.lean`);
`rhoSlack`, `capturedMult_pos_of_mem`, `capturedClasses_subset_window`,
`deployed_classChargeSet_width`, `deployed_card_classChargeSet_le_rhoSlack`,
`classLoad_le_capturedChildCost`, `deployed_bound_of_capturedChildCost`
(`GlobalLoadComposition.lean`).

New declarations (`ResidualLedgerAudit.lean`): `ResidualLedger`, `ResidualLedger.sum`,
`ResidualLedger.load`, `ResidualLedger.sum_load_eq`, `ResidualLedger.charging`,
`ResidualLedger.load_le_sum`, `ResidualLedger.charging_load_bound`, `capturedMult_le_classCost`,
`officialLedger`, `officialLedger_sum`, `officialLedger_load`, `bigCostLedger`,
`ledger_sum_unbounded`, `cappedLedger`, `cappedLedger_sum`,
`ledger_sum_unbounded_with_child_cap`, `ledger_load_unbounded_with_child_cap`,
`deployed_root_not_unique_decoding`, `deployed_classCost_le_of_small_class`,
`deployed_charging_with_self_load_is_vacuous`, `deployed_self_load_charging`,
`deployed_capturedChildCost_le_of_interfaces`, `deployed_bound_of_interfaces`.

---

## 3. Proof / obstruction

**Why the ledger cannot close the target.** At the deployed parameters the derived charge width is
`w − s − a₀ = 69632` and the anchor complement has at most `e = 978944` coordinates. The only
unconditional exported per-coordinate bound is `classLoad(i) ≤ capturedChildCost`
(`classLoad_le_capturedChildCost`). Substituting it into `classLoad_bound` gives literally

```
69632 · C ≤ 978944 · C ,     C = capturedChildCost,
```

which is true for every `C` (`deployed_charging_with_self_load_is_vacuous`,
`deployed_self_load_charging`): since `w ≤ e`, the charging inequality is *self-satisfying* and
carries no budget. This is an algebraic tautology (evidence class 1), not a bound.

Any residual quantitative content would therefore have to come from a bound on the child costs or
on the number of captured challenges. The exported unconditional bad-set bound is the
unique-decoding row `card_badSet_le` (`#Bad ≤ |D|` under `3e < |D| − k + 1`). At the root this
hypothesis fails: `3·978944 = 2936832 > 1048577` (`deployed_root_not_unique_decoding`). At the
child it holds exactly for small classes, which yields the genuinely new derived bound (evidence
class 4)

```
deployed_classCost_le_of_small_class :
  R.card ≤ 104448  →  classCost 1048576 978944 A R f₀ f₁ ≤ 1048576
```

(child length `n₁ = 1048576`, `k₁ = 1048576 − |R|`, `e₁ = |R| − 69632`, distance `|R| + 1`; the
threshold `104448` is exact for this criterion). Classes of size `> 104448` remain unconstrained,
and even granting the cap to *all* classes the ledger still admits sums above `T`
(`ledger_sum_unbounded_with_child_cap`, evidence class 3/1: an exact model of the interface).

**The models.** `bigCostLedger T`: one class, `μ = 1`, `Φ = T + 1`, charge set the whole ground set
of `978944` coordinates (width `978944 ≥ 69632`). `cappedLedger`: `978944` distinct classes indexed
by `Fin 978944`, `μ_R = Φ(R) = 1048576`, charge sets `univ.erase a` — pairwise distinct, heavily
overlapping, each of width `978943 ≥ 69632`; ledger sum `1076360310941548544`
(`cappedLedger_sum`), and since `69632 · 1076360310941548544 > 978944 · T`, the abstract charging
inequality forces a coordinate of load `> T`.

Both models satisfy every exported ledger axiom, so the ledger interface is consistent with a
violation of the deployed target and of the weaker load gate.

**What is *not* claimed.** Neither model is exhibited as an official Reed–Solomon instance: no
`(F, D, f₀, f₁, A, an)` realising these multiplicities and child costs is constructed. Producing one
would refute the deployed bound; failing to derive the bound does not.

---

## 4. Deployed numerical consequence

At `n = 2097152, k = 1048576, e = 978944, w = 69632, s = 0`:

* the reduction `deployed_bound_of_capturedChildCost` remains exactly as before — the deployed
  conclusion `#Bad ≤ 274980728111395087` follows from `Σ_R μ_R Φ(R) ≤ 19559298652205332` and from
  nothing weaker that is currently available;
* the deployed inequality is **not** proved here, and it is **not** refuted;
* what is now proved at the deployed numbers:
  * `69632·C ≤ 978944·C` for all `C` — the charging step is vacuous at these parameters;
  * `¬(3·978944 < 2097152 − 1048576 + 1)` — the root is outside the exported unique-decoding row;
  * `classCost ≤ 1048576` for every captured class with `R.card ≤ 104448`;
  * ledger models with the deployed parameters and sum `1076360310941548544 > 19559298652205332`,
    one coordinate carrying load `> 19559298652205332`;
  * `#Bad ≤ 274980728111395087` **conditional** on `N·B ≤ 19559298652205332` with the two named
    interfaces (I1), (I2) (`deployed_bound_of_interfaces`).

---

## 5. Status of every load-bearing statement

| statement | kind | status |
|---|---|---|
| `officialLedger`, `officialLedger_sum`, `officialLedger_load` | adequacy of the abstraction to official data | **proved** (Lean, axiom-checked) |
| `ResidualLedger.sum_load_eq`, `.charging`, `.load_le_sum`, `.charging_load_bound` | algebraic rearrangement (evidence class 1) | **proved** |
| `ledger_sum_unbounded`, `ledger_sum_unbounded_with_child_cap`, `ledger_load_unbounded_with_child_cap`, `cappedLedger_sum` | exact models of the interface (obstruction, evidence class 3) | **proved** |
| `deployed_charging_with_self_load_is_vacuous`, `deployed_self_load_charging` | tautological identity exposing circularity (class 1) | **proved** |
| `deployed_root_not_unique_decoding` | finite arithmetic (class 2) | **proved** |
| `deployed_classCost_le_of_small_class` | new implication from official MCA semantics (class 4) | **proved** |
| `deployed_capturedChildCost_le_of_interfaces`, `deployed_bound_of_interfaces` | conditional theorem (class 3) | **proved as stated (conditional)** |
| `Σ_R μ_R Φ(R) ≤ 19559298652205332` at the deployed root | target | **open** — not proved, not refuted |
| `#((posBadSet).erase γ₀) ≤ N` at the deployed root (I1) | missing interface | **absent from source** |
| `classCost … R … ≤ B` for all captured classes (I2) | missing interface | **absent from source** (proved only for `R.card ≤ 104448`) |
| `Σ_R μ_R |C_R| = n − r` | forbidden support-partition identity | **not used anywhere** |
