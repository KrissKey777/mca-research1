# Global recursion / composition — canonical replay, four-branch audit, and the remaining load gate

Scope: replay of the reported `GlobalAnchorRecursion` layer inside the canonical project, an audit
of the four anchor branches against the four objections raised, and the exact remaining-load gate.
No local projective / ResidualClass geometry was rebuilt.

Historical export: `historical_import/global_anchor_recursion_3ae4247/`
(sources under `src/`, plus `MANIFEST.md`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`,
`GLOBAL_RECURSION_COMPOSITION_REPORT.md`, `REPLAY_BUILD.log`, `REPLAY_AXIOMS.txt`).
No canonical source was overwritten.

Exact commit hash of the exported tree: `3ae4247c000b5609ed0f1b8cab1e710423cdc617`.
Toolchain `leanprover/lean4:v4.28.0`; Mathlib rev `v4.28.0`.

New canonical sources added by this run:

* `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`
* `RequestProject/GlobalRecursionLoadGateAxiomAudit.lean`

---

## 1. Replay / build / axiom / import table

Import closure of the exported layer: **20 project modules** (Mathlib excluded), all present and
all copied into the historical import directory; the full list with line counts and SHA-256 digests
is in `historical_import/global_anchor_recursion_3ae4247/MANIFEST.md`.

| item | command / check in the canonical project | result | status |
|---|---|---|---|
| build of the exact imported modules | `lake build RequestProject.GlobalAnchorRecursionAxiomAudit` (8045 jobs, closes over all 20 modules) | success, no errors | **BANKED** |
| `#print axioms` on every exported theorem | 38 audited declarations in `GlobalAnchorRecursionAxiomAudit.lean` | every list ⊆ `{propext, Classical.choice, Quot.sound}` | **BANKED** |
| transitive import closure audit | recursive scan of project imports from `GlobalAnchorRecursion` | 20 modules, closed, no missing file | **BANKED** |
| `sorry` / `admit` / `axiom` / `implemented_by` scan | `rg` over all 20 modules | 19 textual hits, **all inside doc comments** (“No axioms, no `sorry`”); zero occurrences in code | **BANKED** |
| definitions/constants vs. canonical Grand MCA interfaces | `officialWitness`, `officialSupport`, `officialClass`, `posBadSet`, `classCost`, `childCost`, `parentMult`, `totalChildCost`, `chargeSet`, `chargeLoad`, `resDim`, `resRad`, `instComplexity`, `windowMass`, `windowZeros`, `badSet`, `zeroWitnessBadSet`, `NormalisedWindow` | all imported unchanged from `MCA` / `TauWindowClassification` / `BranchingControl` / `MassDescentRecursion`; no shadowing redefinition in the exported file | **BANKED** |
| new file of this run | `lake build RequestProject.GlobalRecursionLoadGateAxiomAudit` (8046 jobs) | success; 18 audited declarations, all lists = `{propext, Classical.choice, Quot.sound}`; no `sorry` | **BANKED** |

Replay verdict: the exported source layer is **BANKED** at source/build/axiom level. This banks the
*Lean statements as written*; it does not upgrade any clause whose Lean statement is weaker than the
clause claimed in prose — see §2.

---

## 2. The four branches — exact theorem signatures and verdicts

All four branch statements below are the literal canonical statements (file
`RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`, unchanged), followed by the audit
result and, where the objection is sustained, the new theorem in
`RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`.

### Branch A — `a₀ = 0`

```lean
theorem branchA_recurrence {k e w s M : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hAe : A.card + e < D.card)
    (hn : D.card = k + e + w) (hs : A.card = k + s) (hws : 0 < w - s)
    (an : AnchorData k e f₀ f₁) (h0 : an.poly = 0)
    (hload : ∀ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      chargeLoad k e A an.supp f₀ f₁ i ≤ M) :
    (badSet k e f₀ f₁).card ≤ (e + 1) + e * M / (w - s)
```

Objection 3 (“uncaptured cost is zero requires a proof of terminality under official witness
semantics”): **the Lean statement already satisfies it, but the branch label does not.** The
zero-uncaptured lemma `uncapturedChildCost_eq_zero_of_terminal_anchor` has hypothesis
`an.poly = 0`, and terminality is *proved* from it (`an.chal ∈ zeroWitnessBadSet`, hence
`an.chal ∉ posBadSet`). What is **not** true is the branch label `a₀ = 0 ⇒ uncaptured = 0`:

```lean
theorem anchorMass_eq_zero_iff (an : AnchorData k e f₀ f₁) :
    anchorMass A an = 0 ↔ ∀ x ∈ A, an.poly.eval (x : F) = 0

theorem exists_zero_mass_nonzero_poly {k : ℕ} {A : Finset ↥D} (hA : A.card < k) :
    ∃ p : F[X], p ≠ 0 ∧ p.degree < (k : WithBot ℕ) ∧ windowMass A p = 0

theorem uncapturedChildCost_eq_zero_iff :
    uncapturedChildCost k e A f₀ f₁ γ₀ = 0 ↔
      (γ₀ ∉ posBadSet k e f₀ f₁ ∨ childCost k e A f₀ f₁ γ₀ = 0)
```

so for a merely mass-zero anchor the uncaptured term must be kept:

```lean
theorem branchA_massZero_recurrence {k e w s M : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hAe : A.card + e < D.card)
    (hn : D.card = k + e + w) (hs : A.card = k + s) (hws : 0 < w - s)
    (an : AnchorData k e f₀ f₁) (ha0 : anchorMass A an = 0)
    (hload : ∀ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      chargeLoad k e A an.supp f₀ f₁ i ≤ M) :
    (badSet k e f₀ f₁).card
      ≤ (e + 1) + e * M / (w - s) + uncapturedChildCost k e A f₀ f₁ an.chal
```

Verdict: **BANKED for `q₀ = 0` (terminal anchor); the branch label `a₀ = 0` is corrected** — the
closed form is available only under terminality, not under mass zero.

### Branch B — `0 < a₀ < w − s`

```lean
theorem anchor_recurrence {k e w s M : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hAe : A.card + e < D.card)
    (hn : D.card = k + e + w) (hs : A.card = k + s)
    (an : AnchorData k e f₀ f₁) (hd : 0 < w - s - anchorMass A an)
    (hload : ∀ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      chargeLoad k e A an.supp f₀ f₁ i ≤ M) :
    (badSet k e f₀ f₁).card
      ≤ (e + 1) + e * M / (w - s - anchorMass A an)
        + uncapturedChildCost k e A f₀ f₁ an.chal
```

Objection 4 (“strict child decrease must be accompanied by an explicit potential inequality”):
the recurrence is explicit, but its last term is the *full recursive* cost of one child; the
inherited `uncaptured_child_complexity_lt` supplies only strict descent. The explicit potential
inequality that turns a single-child chain into a number is now proved:

```lean
theorem chain_descent_cost_bound (cost localCost rad : σ → ℕ) (children : σ → Finset σ)
    (mult : σ → σ → ℕ) (L : ℕ)
    (hstep : ∀ X, cost X ≤ localCost X + ∑ Y ∈ children X, mult X Y * cost Y)
    (hdrop : ∀ X, ∀ Y ∈ children X, rad Y + 1 ≤ rad X)
    (hmult : ∀ X, ∑ Y ∈ children X, mult X Y ≤ 1)
    (hL : ∀ X, localCost X ≤ L) (X : σ) :
    cost X ≤ L * (rad X + 1)
```

Verdict: **BANKED as a one-step recurrence; the closing potential is available only with the
explicit multiplicity hypothesis `Σ mult ≤ 1` of `chain_descent_cost_bound`.** Strict descent alone
is never used as a cost bound (`strict_descent_not_a_cost_bound`, replayed).

### Branch C — `a₀ ≥ w − s`

```lean
theorem branchC_large_anchor_radius_drop {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (an : AnchorData k e f₀ f₁)
    (hbig : w - s ≤ anchorMass A an) :
    resRad e A (windowZeros A an.poly) + (w - s) ≤ e
```

Objection 1 (“a radius inequality alone does not pay recursive cost”): **sustained.** Proved here:

```lean
theorem radius_drop_not_a_cost_bound (B : ℕ) :
    ∃ (e : ℕ) (cost localCost rad : ℕ → ℕ) (children : ℕ → Finset ℕ) (mult : ℕ → ℕ → ℕ) (X : ℕ),
      (∀ X, cost X ≤ localCost X + ∑ Y ∈ children X, mult X Y * cost Y) ∧
      (∀ X, ∀ Y ∈ children X, rad Y + 1 ≤ rad X) ∧
      (∀ X, rad X ≤ e) ∧ (∀ X, localCost X ≤ 1) ∧ B < cost X
```

The exact price of a radius drop is the multiplicity-bounded terminal bound:

```lean
theorem radius_descent_cost_bound (cost localCost rad : σ → ℕ) (children : σ → Finset σ)
    (mult : σ → σ → ℕ) (L m d : ℕ) (hd : 0 < d)
    (hstep : ∀ X, cost X ≤ localCost X + ∑ Y ∈ children X, mult X Y * cost Y)
    (hdrop : ∀ X, ∀ Y ∈ children X, rad Y + d ≤ rad X)
    (hmult : ∀ X, ∑ Y ∈ children X, mult X Y ≤ m)
    (hL : ∀ X, localCost X ≤ L) (X : σ) :
    cost X ≤ L * ∑ j ∈ Finset.range (rad X / d + 1), m ^ j
```

and at the deployed point (`e = 978944`, `w − s = 69632`, so at most `⌊e/(w−s)⌋ = 14` levels,
`L = e + 1`):

```lean
theorem branchC_deployed_bound_of_branching (cost localCost rad : σ → ℕ) (children : σ → Finset σ)
    (mult : σ → σ → ℕ) (m : ℕ) (hm : m ≤ 6)
    (hstep : ∀ X, cost X ≤ localCost X + ∑ Y ∈ children X, mult X Y * cost Y)
    (hdrop : ∀ X, ∀ Y ∈ children X, rad Y + 69632 ≤ rad X)
    (hmult : ∀ X, ∑ Y ∈ children X, mult X Y ≤ m)
    (hL : ∀ X, localCost X ≤ 978945) (hrad : ∀ X, rad X ≤ 978944) (X : σ) :
    cost X ≤ 274980728111395087

theorem branchC_deployed_seven_exceeds :
    274980728111395087 < 978945 * ∑ j ∈ Finset.range 15, (7 : ℕ) ^ j
```

Verdict: the radius inequality itself is **BANKED**; the branch-C *cost* clause is
**SOURCE_PRESENT_UNREPLAYED → open**: it becomes a terminal bound only under a total child
multiplicity `m ≤ 6` per state, which the layer does not establish (and `m = 7` already breaks it).

### Branch D — no usable anchor

```lean
theorem badSet_eq_empty_of_no_anchor {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (h : ¬ Nonempty (AnchorData k e f₀ f₁)) :
    badSet k e f₀ f₁ = ∅
```

Objection 2 (“valid only if usable-anchor existence was existential over the complete bad family”):
**satisfied.** The hypothesis is `¬ Nonempty (AnchorData k e f₀ f₁)`, i.e. the non-existence of
*any* anchor, and every bad challenge is itself an anchor:

```lean
theorem anchor_at_every_bad_challenge {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) {γ : F} (hγ : γ ∈ badSet k e f₀ f₁) :
    ∃ an : AnchorData k e f₀ f₁, an.chal = γ
```

Verdict: **BANKED.**

---

## 3. The exact load definition

`RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`:

```lean
noncomputable def classRep (k e : ℕ) (A : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F)
    (R : Finset ↥D) : F :=
  if h : ∃ γ ∈ capturedChallenges k e f₀ f₁ γ₀, officialClass k e A f₀ f₁ γ = R then
    h.choose else γ₀

noncomputable def classChargeSet (k e : ℕ) (A S0 : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F)
    (R : Finset ↥D) : Finset ↥D :=
  chargeSet k e A S0 f₀ f₁ (classRep k e A f₀ f₁ γ₀ R)

noncomputable def classLoad (k e : ℕ) (A S0 : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F)
    (i : ↥D) : ℕ :=
  ∑ R ∈ capturedClasses k e A f₀ f₁ γ₀,
    if i ∈ classChargeSet k e A S0 f₀ f₁ γ₀ R then
      capturedMult k e A R f₀ f₁ γ₀ * classCost k e A R f₀ f₁ else 0
```

i.e. exactly

```
load_X(i) = Σ_{R ∈ capturedClasses(X),  i ∈ chargeSet(R)}  μ_R · Φ(R),
μ_R = capturedMult R   (captured fibre multiplicity of the class)
Φ(R) = classCost R     (full recursive bad-cost of the child instance)
```

Canonicity and disjointness: the sum runs over the `Finset` `capturedClasses` of *distinct* child
classes (`(posBadSet.erase γ₀).image officialClass`), the coordinate set of a class is the charge
set of its canonical representative `classRep` (a function of the class), and the multiplicity used
is the class-level `capturedMult`, which satisfies the exact split
`capturedMult R + anchorMult R = parentMult R` (replayed). No support-level or challenge-level
multiplicity is mixed in, and the anchor challenge is never charged against its own support.

Proved consequences (all axiom-audited, no `sorry`):

```lean
theorem sum_classLoad_eq (k e : ℕ) (A S0 : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F) :
    ∑ i ∈ (Finset.univ : Finset ↥D) \ S0, classLoad k e A S0 f₀ f₁ γ₀ i
      = ∑ R ∈ capturedClasses k e A f₀ f₁ γ₀,
          (classChargeSet k e A S0 f₀ f₁ γ₀ R).card *
            (capturedMult k e A R f₀ f₁ γ₀ * classCost k e A R f₀ f₁)

theorem classLoad_charging … :
    (w - s - anchorMass A an) * capturedChildCost k e A f₀ f₁ an.chal
      ≤ ∑ i ∈ (Finset.univ : Finset ↥D) \ an.supp, classLoad k e A an.supp f₀ f₁ an.chal i

theorem classLoad_bound … (hload : ∀ i ∈ univ \ an.supp, classLoad … i ≤ M) :
    (w - s - anchorMass A an) * capturedChildCost k e A f₀ f₁ an.chal ≤ e * M

theorem classLoad_recurrence … :
    (badSet k e f₀ f₁).card
      ≤ (e + 1) + e * M / (w - s - anchorMass A an)
        + uncapturedChildCost k e A f₀ f₁ an.chal
```

No circular assumption of the form `μ_R · C(R) ≤ M` is used: the only scalar hypothesis is the
per-coordinate load bound, and the width factor `w − s − a₀` is the *derived*
`card_chargeSet_ge_anchor`, applied to the canonical representative of each captured class.

---

## 4. The exact remaining load theorem

```lean
def LoadGate (k e : ℕ) (A S0 : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F) : Prop :=
  ∀ i ∈ (Finset.univ : Finset ↥D) \ S0, classLoad k e A S0 f₀ f₁ γ₀ i ≤ 19559298652205332

theorem deployed_load_gate {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hD : D.card = 2097152) (hA : NormalisedWindow 1048576 f₀ f₁ A) (hcard : A.card = 1048576)
    (an : AnchorData 1048576 978944 f₀ f₁) (h0 : an.poly = 0)
    (hgate : LoadGate 1048576 978944 A an.supp f₀ f₁ an.chal) :
    (badSet 1048576 978944 f₀ f₁).card ≤ 274980728111395087
```

Status of the two admissible targets:

* **Target A** — `load_X(i) ≤ 19559298652205332` for every state and coordinate: **OPEN**. It is
  never assumed silently; it appears as the explicit hypothesis `hgate`/`hload` of every theorem
  that consumes it. `deployed_load_gate` is a *reduction* (gate ⇒ deployed budget), not a proof of
  the gate, and the threshold is not called proved merely because it is the required budget.
* **Target B** — over-load produces a paying certificate: the structural half is proved,

```lean
theorem heavy_load_yields_class_family (i : ↥D) :
    ∑ R ∈ (capturedClasses k e A f₀ f₁ γ₀).filter
        (fun R => i ∈ classChargeSet k e A S0 f₀ f₁ γ₀ R),
      capturedMult k e A R f₀ f₁ γ₀ * classCost k e A R f₀ f₁
      = classLoad k e A S0 f₀ f₁ γ₀ i

theorem loaded_class_is_residual_child
    (hA : NormalisedWindow k f₀ f₁ A) (hkA : k ≤ A.card) {R : Finset ↥D}
    (hR : R ∈ capturedClasses k e A f₀ f₁ γ₀) :
    ∃ γ ∈ posBadSet k e f₀ f₁, officialClass k e A f₀ f₁ γ = R ∧
      instComplexity (resDim k R) (resRad e A R) < instComplexity k e
```

  i.e. an over-loaded coordinate is carried by an explicit, canonically assigned family of
  ResidualClass children of strictly smaller complexity, of total weight exactly `load_X(i)`. The
  *paying* half — an explicit potential decrease or certificate cost covering the excess
  `load_X(i) − M` — is **not** proved.

---

## 5. The one minimal obstruction

> **(O)** *Class-level spread of official supports.* For a state `X` with anchor support `S0` and
> derived charge width `d = w − s − a₀ > 0`, and for every coordinate `i ∉ S0`:
>
> ```
> Σ_{R ∈ capturedClasses(X),  i ∈ chargeSet(classRep R)}  capturedMult(R) · classCost(R)
>       ≤ 19559298652205332 .
> ```

This is the single inequality that separates the present state from Target A: by
`classLoad_charging`, `classLoad_bound` and `classLoad_recurrence` it immediately gives
`d · Σ_R μ_R·Φ(R) ≤ e·M` and hence, at the deployed point with a terminal anchor,
`#Bad ≤ 274980728111395087` (`deployed_load_gate`). It is a spread statement about official
supports — no coordinate outside the anchor support may lie in the representative charge sets of
canonically assigned child classes of total recursive weight exceeding `M` — and it is *not*
derivable from the counting already banked: by `anchor_exists_concentrated_coordinate` the double
counting alone yields only a coordinate carrying a `d/e = 69632/978944 ≈ 1/14.06` fraction of the
captured cost, which is a lower bound on the worst load, not an upper bound.

No other obligation of the global layer is open, with two documented exceptions that are *not*
load-gate obstructions but branch-label corrections: the branch-A closed form requires `q₀ = 0`
(not `a₀ = 0`), and the branch-C radius drop pays only under a total child multiplicity `m ≤ 6`.
