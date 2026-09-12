# GLOBAL LOAD COMPOSITION — final composition report

Deployed point used throughout:

```
n = 2097152,  k = 1048576,  e = 978944,  w = 69632,  s = 0,
M* = 19559298652205332  (the deployed class-load target),
B* = 274980728111395087 (the deployed bad-set target).
n = k + e + w  is proved (`deployed_parameters`).
```

Everything below is proved **inside the canonical tree**, from the canonical definitions of
`MassDescentRecursion` / `BranchingControl` / `GlobalAnchorRecursion` /
`GlobalRecursionLoadGate` / `GlobalRecursionBranchGaps`. No statement from any external report is
imported, assumed, or re-used as a fact. Prior reports were treated as reports only.

New source added by this mission (only these two files were built):

* `RequestProject/Root/CodingTheory/GlobalLoadComposition.lean`
* `RequestProject/GlobalLoadCompositionAxiomAudit.lean`

Both build; every theorem's axiom list is `⊆ {propext, Classical.choice, Quot.sound}`; no
`sorry`, no `axiom`, no `@[implemented_by]`.

---

## 0. The three quantities, kept separate

| symbol | Lean | what it is | where it can appear |
|---|---|---|---|
| `ρ_R = (n − \|R\|) − 1` | `rhoSlack n R` | geometric slack of a class | only in `deployed_card_classChargeSet_le_rhoSlack`; it never multiplies a cost anywhere in the file |
| `Φ(R)` | `classCost k e A R f₀ f₁` | recursive child cost = `#` of the child's own bad set | the cost factor of the load |
| `μ_R` | `capturedMult k e A R f₀ f₁ γ₀` | canonical class multiplicity = number of **captured** parent challenges with canonical child class `R` | the multiplicity factor of the load |

The three other multiplicities of the layer (`anchorMult`, `parentMult`, and the challenge-level
count) are separated from `μ_R` by `multiplicity_separation`.

---

## 1. Which alternative was delivered

**(B) — priced high-load descent. Delivered, unconditionally, in the abstract presentation.**

The potential is *defined first and independently of the load*: `fuelMajorant` is the
multiplicity-weighted total cost of the truncated recursion tree, and
`cxMajorant children mult Φ cx X = fuelMajorant children mult Φ (cx X) X`. Its defining equations
mention only `children`, `mult`, `Φ`. Then

```
priced_high_load_descent_cxMajorant :
  (∀ X, ∀ Y ∈ children X, cx Y < cx X) →
  S ⊆ children X → X' ∈ children X → 1 ≤ mult X X' →
  capturedLoadOn mult Φ X S + cxMajorant children mult Φ cx X'
    ≤ cxMajorant children mult Φ cx X
```

i.e. exactly `Ψ(X) − Ψ(X') ≥ capturedLoad(X, S)`, with **no** hypothesis on costs, multiplicities
or the load. At the canonical recursion the same pricing is
`priced_high_load_descent_canonical`: a coordinate `i` with `0 < classLoad … i` selects a captured
child class `R'` (`highLoad_selects_child`) and

```
classLoad k e A S0 f₀ f₁ γ₀ i + Ψ R' ≤ Ψ X₀ .
```

**(A) — the unconditional deployed bound `classLoad_X(i) ≤ 19559298652205332` is NOT proved.**
It is not claimed anywhere. `deployed_bound_of_root_majorant` shows the whole deployed conclusion
follows from one numeric input (see §5).

---

## 2. Theorem table

Legend: *cond.* = conditionality; **U** = unconditional (no mathematical hypothesis beyond the
definitions), **H** = holds under the stated hypotheses. All rows: file
`RequestProject/Root/CodingTheory/GlobalLoadComposition.lean`, build ✅, axioms
`⊆ {propext, Classical.choice, Quot.sound}` ✅ (audited in
`RequestProject/GlobalLoadCompositionAxiomAudit.lean`), no `sorry`.

### 2.1 Abstract presentation: the independently defined potential and the pricing

| # | theorem (signature, abbreviated) | assumptions | cond. | numerical consequence |
|---|---|---|---|---|
| 1 | `capturedLoadOn mult Φ X S = ∑ Y ∈ S, mult X Y * Φ Y` (def) | — | — | fixes `capturedLoad` as `Σ μ·Φ`; `ρ` absent |
| 2 | `IsExternalMajorant children mult Φ Ψ ↔ ∀ X, ∑_{Y∈children X} mult X Y * (Φ Y + Ψ Y) ≤ Ψ X` (def) | — | — | the only property of `Ψ` used |
| 3 | `sum_mult_add_eq : ∑ mult*(Φ+Ψ) = ∑ mult*Φ + ∑ mult*Ψ` | — | U | exact split of cost vs potential |
| 4 | `priced_descent_root : (∑_{Y∈C} mult X Y*(Φ Y+Ψ Y) ≤ Ψ X) → S ⊆ C → X' ∈ C → 1 ≤ mult X X' → capturedLoadOn mult Φ X S + Ψ X' ≤ Ψ X` | root majorant inequality only | H | `Ψ(X) − Ψ(X') ≥ capturedLoad` |
| 5 | `load_le_root_majorant : … → capturedLoadOn mult Φ X S ≤ Ψ X` | root majorant inequality | H | uniform load bound from `Ψ` |
| 6 | `priced_high_load_descent : IsExternalMajorant … → …` | external majorant | H | option (B), general `Ψ` |
| 7 | `fuelMajorant` (def, recursion on fuel) | — | — | the potential; definition independent of the load |
| 8 | `fuelMajorant_le_succ`, `fuelMajorant_mono_aux`, `fuelMajorant_mono` | — | U | monotonicity in the fuel |
| 9 | `cxMajorant children mult Φ cx X = fuelMajorant … (cx X) X` (def) | — | — | the canonical potential |
| 10 | `isExternalMajorant_cxMajorant : (∀ X, ∀ Y ∈ children X, cx Y < cx X) → IsExternalMajorant children mult Φ (cxMajorant …)` | complexity drop only | H (drop) | the potential of #9 **is** a majorant |
| 11 | `priced_high_load_descent_cxMajorant : (complexity drop) → S ⊆ children X → X' ∈ children X → 1 ≤ mult X X' → capturedLoadOn mult Φ X S + cxMajorant … X' ≤ cxMajorant … X` | complexity drop only | H (drop) | **option (B), unconditional** |
| 12 | `descent_does_not_bound_load : ∃ presentation, (∀ X, ∀ Y ∈ children X, cx Y < cx X) ∧ ∀ B, ∃ X S, S ⊆ children X ∧ B < capturedLoadOn mult Φ X S` | — | U | audit item 9: termination ⇏ cost bound |

### 2.2 The canonical recursion: separated `ρ`, `μ`, `Φ`, and the audit items 1–4

| # | theorem | assumptions | cond. | numerical consequence |
|---|---|---|---|---|
| 13 | `rhoSlack n R = (n − R.card) − 1` (def), `rhoSlack_antitone` | — | U | geometric slack, isolated |
| 14 | `capturedFibre` (def), `capturedMult_eq_card_capturedFibre : μ_R = #fibre R` | — | U | audit 1: `μ_R` is a fibre count |
| 15 | `capturedFibre_disjoint : R ≠ R' → Disjoint (fibre R) (fibre R')` | — | U | audit 1: **disjoint** child classes |
| 16 | `capturedChallenges_eq_biUnion : capturedChallenges = ⋃_{R ∈ capturedClasses} fibre R` | — | U | audit 1: the fibres exhaust the captured challenges |
| 17 | `mem_capturedClasses_iff_mult_pos : R ∈ capturedClasses ↔ 0 < μ_R`; `capturedMult_pos_of_mem` | — | U | audit 1: the family is a `Finset` of **distinct occupied** classes |
| 18 | `sum_capturedMult_eq_card_capturedChallenges : ∑_R μ_R = #capturedChallenges` | — | U | **audit 2**: `Σ μ_R` = captured parent-challenge count |
| 19 | `multiplicity_separation : μ_R + anchorMult_R = parentMult_R ∧ anchorMult_R ≤ 1` | — | U | **audit 3**: all multiplicities separated |
| 20 | `chargedClasses` (def), `chargedClasses_subset` | — | U | the charged subfamily at a coordinate |
| 21 | `classLoad_eq_sum_chargedClasses : classLoad … i = ∑_{R charged at i} μ_R · Φ(R)` | — | U | exact separated form of the load |
| 22 | `classLoad_eq_capturedLoad : classLoad … i = capturedLoadOn μ Φ X₀ (chargedClasses … i)` | — | U | identifies `classLoad` with the abstract `capturedLoad` |
| 23 | `highLoad_selects_child : 0 < classLoad … i → ∃ R' charged at i, 1 ≤ μ_{R'} ∧ 1 ≤ Φ(R')` | — | U | the `highLoad(X,i) → X'` step |
| 24 | `classLoad_le_root_majorant : (root majorant ineq.) → classLoad … i ≤ Ψ X₀` | root inequality | H | load bound from a majorant |
| 25 | `priced_high_load_descent_canonical : (root ineq.) → 0 < classLoad … i → ∃ R' charged, classLoad … i + Ψ R' ≤ Ψ X₀` | root inequality | H | **option (B) at the canonical recursion** |
| 26 | `classLoad_le_capturedChildCost : classLoad … i ≤ capturedChildCost …` | — | U | one-step majorant `Ψ(root) = Σ_R μ_R·Φ(R)`, no hypothesis |
| 27 | `card_classChargeSet_ge : w − s − a₀ ≤ #classChargeSet R` for `R ∈ capturedClasses` | `NormalisedWindow`, `n = k+e+w`, `\|A\| = k+s` | H | **audit 4**: explicit charge-set width |
| 28 | `card_classChargeSet_le : #classChargeSet R ≤ e` | anchor support threshold | H | width upper bound |
| 29 | `capturedClasses_subset_window : R ∈ capturedClasses → R ⊆ A` | — | U | classes live in the window |

### 2.3 The deployed point

| # | theorem | assumptions | cond. | numerical consequence |
|---|---|---|---|---|
| 30 | `deployed_parameters : 2097152 = 1048576 + 978944 + 69632` | — | U | `n = k + e + w` |
| 31 | `deployed_budget_arithmetic : 978944 + 1 + 978944 * 19559298652205332 / 69632 ≤ 274980728111395087` | — | U | `(e+1) + e·M*/w ≤ B*` (slack 4) |
| 32 | `deployed_classChargeSet_width : 69632 ≤ #classChargeSet R` | deployed `n, k`, `NormalisedWindow`, terminal anchor `q₀ = 0` | H | **audit 4 at the deployed point**: width `= w − s = 69632` |
| 33 | `deployed_card_classChargeSet_le_rhoSlack : #classChargeSet R ≤ rhoSlack 2097152 R` | `\|A\| = 1048576`, `R` captured | H | `ρ_R ≥ 1048575 ≥ e ≥ width`: the slack dominates the width, and is used for nothing else |
| 34 | `deployed_loadGate_of_root_majorant : (root ineq.) → Ψ X₀ ≤ 19559298652205332 → LoadGate 1048576 978944 A an.supp f₀ f₁ an.chal` | root inequality + numeric value | H | the gate from one number |
| 35 | `deployed_bound_of_root_majorant : … → #badSet 1048576 978944 f₀ f₁ ≤ 274980728111395087` | `\|D\| = n`, `NormalisedWindow`, `\|A\| = k`, terminal anchor, root ineq., `Ψ X₀ ≤ M*` | H | **the full composition**: `#Bad ≤ B*` |
| 36 | `deployed_bound_of_capturedChildCost : capturedChildCost … ≤ 19559298652205332 → #badSet … ≤ 274980728111395087` | deployed hypotheses + one numeric bound on `Σ_R μ_R·Φ(R)` | H | the obstruction in its sharpest concrete form |

### 2.4 Branch audit A–D (audit items 5–8)

| # | theorem | assumptions | cond. | content |
|---|---|---|---|---|
| 37 | `official_anchor_semantics : IsOfficialAnchor → officialClass = windowZeros A an.poly ∧ anchorMass = windowMass A (officialWitness …).1 ∧ an.supp = officialSupport … ∧ chargeSet … an.chal = ∅` | `IsOfficialAnchor` | H | **audit 5**: official witness semantics verified for the branch quantities |
| 38 | `branchAB_official_selection : γ ∈ posBadSet → ∃ an, an.chal = γ ∧ IsOfficialAnchor … ∧ officialClass = windowZeros A an.poly` | `NormalisedWindow` | H | audit 5: branches A/B may be run at an official anchor |
| 39 | `branchA_audit : a₀ = 0 → (poly vanishes on all of A) ∧ (\|A\| < k → ∃ nonzero zero-mass codeword) ∧ (∀ captured γ, w − s ≤ #chargeSet γ)` | `NormalisedWindow`, `n = k+e+w`, `\|A\| = k+s`, `a₀ = 0` | H | **audit 6, branch A**: `a₀ = 0` is *not* terminality; full width `w − s` |
| 40 | `branchB_audit : a₀ < w − s → 0 < w − s − a₀ ∧ (w−s−a₀)·capturedChildCost ≤ ∑_{i∉S0} classLoad i` | as above | H | **audit 6, branch B**: positive derived width + class-level charging |
| 41 | `branchC_audit : (∑_R μ_R ≤ 6 ↔ #(posBadSet.erase γ₀) ≤ 6) ∧ (∑_R μ_R ≤ 6 → #posBadSet ≤ 7)` | `γ₀ ∈ posBadSet` | H | **audit 7**: branch C's `m ≤ 6` is *equivalent* to a bad-set cardinality bound — circular, and used nowhere in §2.1–2.3 |
| 42 | `branchD_audit : (∀ γ ∈ badSet, ∃ an, an.chal = γ) ∧ (¬ Nonempty (AnchorData k e f₀ f₁) → badSet = ∅)` | `NormalisedWindow` | H | **audit 8**: the exact anchor quantifier theorem is the one used |

---

## 3. Audit requirements, item by item

1. **Disjoint distinct child classes** — #14–#17. `capturedClasses` is a `Finset` of distinct
   classes; their fibres are pairwise disjoint (#15) and exhaust the captured challenges (#16);
   membership is equivalent to positive multiplicity (#17).
2. **`Σ_R μ_R` = captured parent-challenge count** — #18.
3. **All multiplicities separated** — #19 (`μ_R`, `anchorMult`, `parentMult`); the load (#21) uses
   `μ_R` only, and `ρ_R` never multiplies a cost.
4. **Charge-set width proved explicitly** — #27 (general: `w − s − a₀`) and #32 (deployed:
   `69632`), with the upper bounds #28 and #33.
5. **Official witness semantics verified for every branch** — #37, #38; branch quantities of an
   official anchor coincide on the nose with the official-witness quantities used by `chargeSet`,
   `officialClass`, `childCost`, `classLoad`.
6. **Branches A–D audited separately** — #39, #40, #41, #42.
7. **Branch C's `m ≤ 6` discarded as circular** — #41 proves it is *equivalent* to
   `#(posBadSet \ {γ₀}) ≤ 6`, i.e. a bad-set cardinality bound of the kind the recursion is meant
   to produce. It is not independently proved, so it is **not used**: no theorem in §2.1–2.3
   depends on it.
8. **Exact anchor quantifier theorem for branch D** — #42 uses
   `anchor_at_every_bad_challenge` (every bad challenge *is* an anchor challenge), so the
   hypothesis `¬ Nonempty (AnchorData …)` quantifies over the complete bad family.
9. **Termination is not a cost bound** — #12: an explicit presentation with a strict complexity
   drop on every child edge in which the captured load is unbounded. Consequently every bound in
   this file is a *priced* inequality, never a descent statement.

---

## 4. What is conditional and on what

Only two shapes of hypothesis occur.

* *Deployed geometry*: `|D| = 2097152`, `NormalisedWindow 1048576 f₀ f₁ A`, `|A| = 1048576`, a
  terminal anchor (`an.poly = 0`). These are the standing hypotheses of the deployed layer, not
  new assumptions.
* *A root majorant*: either `∑_R μ_R·(Φ(R) + Ψ R) ≤ Ψ X₀` for an independently defined `Ψ`
  (satisfied by `cxMajorant`, #10), or its unconditional one-step instance
  `Ψ(X₀) = Σ_R μ_R·Φ(R)` (#26).

Nothing in the file assumes a bound on `classLoad`, on `capturedChildCost`, on `#posBadSet` or on
the total child multiplicity.

---

## 5. The single smallest remaining obstruction

> **A numeric value for the external majorant at the deployed root:** exhibit an independently
> defined `Ψ` satisfying the root inequality of #34 with
> `Ψ X₀ ≤ 19559298652205332` — equivalently, by #26/#36, prove
> ```
> capturedChildCost 1048576 978944 A f₀ f₁ an.chal ≤ 19559298652205332
> ```
> for the deployed state, i.e. bound `Σ_R μ_R·Φ(R)` by `M*`.

This is the *only* missing input. With it, #35 (or #36) yields the deployed target
`#Bad ≤ B* = 274980728111395087` immediately, and #25 already supplies the priced descent that
any recursive derivation of that number would have to use.
