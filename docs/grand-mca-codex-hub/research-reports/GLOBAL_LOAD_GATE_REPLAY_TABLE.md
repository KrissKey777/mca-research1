# GlobalLoadGate replay table — all audited declarations

Canonical replay of 2026-09-09: `lake build RequestProject.GlobalAnchorRecursionAxiomAudit RequestProject.GlobalRecursionLoadGateAxiomAudit RequestProject.GlobalRecursionBranchGapsAxiomAudit` — 8049 jobs, success, 67 `#print axioms` lines, every list ⊆ {propext, Classical.choice, Quot.sound}.

Exported tree commit: `3ae4247c000b5609ed0f1b8cab1e710423cdc617`. Package: `package/global_load_gate_replay/`, ZIP `ARISTOTLE_GLOBAL_LOAD_GATE_PACKAGE.zip`.

Legend for `status`: BANKED = replayed, sorry-free, standard axioms only; CONDITIONAL = replayed but the statement carries an unproved hypothesis (the goal named in the cell).
The `hypotheses` column lists the named proof hypotheses of the statement; the complete binder list of every declaration is in the "Exact signatures" section below.

| # | theorem | source file | replay | axioms | hypotheses | status |
|---|---|---|---|---|---|---|
| 1 | `globalCost_eq` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Quot.sound` | — | BANKED — replayed, sorry-free |
| 2 | `capturedCost_add_uncaptured` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA | BANKED — replayed, sorry-free |
| 3 | `capturedCost_union_of_disjoint` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — replayed, sorry-free |
| 4 | `capturedCost_union_le` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 5 | `sound` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — replayed, sorry-free |
| 6 | `strict_descent_not_a_cost_bound` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Quot.sound` | — | BANKED — counterexample |
| 7 | `anchorMass_le` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA | BANKED — replayed, sorry-free |
| 8 | `anchorMass_eq_zero_of_poly_zero` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — replayed, sorry-free |
| 9 | `exists_anchor_of_badSet_nonempty` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, h | BANKED — replayed, sorry-free |
| 10 | `exists_terminal_anchor` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — replayed, sorry-free |
| 11 | `terminal_anchor_or_all_positive_mass` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 12 | `exists_min_mass_anchor` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, h | BANKED — replayed, sorry-free |
| 13 | `badSet_eq_empty_of_no_anchor` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, h | BANKED — replayed, sorry-free |
| 14 | `mem_chargeSet_iff` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 15 | `card_chargeSet_ge_anchor` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hn, hs, hγ, hne | BANKED — replayed, sorry-free |
| 16 | `card_chargeSet_ge_branchA` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hn, hs, ha0, hγ, hne | BANKED — replayed, sorry-free |
| 17 | `chargeWidth_pos_branchB` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Quot.sound` | h | BANKED — replayed, sorry-free |
| 18 | `sum_erase_split` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 19 | `totalChildCost_eq_captured_add_uncaptured` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 20 | `capturedMult_add_anchorMult` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 21 | `capturedChildCost_eq_sum_capturedMult` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 22 | `uncapturedChildCost_eq_zero_of_terminal_anchor` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | h0 | BANKED — replayed, sorry-free |
| 23 | `anchor_charging` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hn, hs | BANKED — replayed, sorry-free |
| 24 | `anchor_load_bound` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hn, hs, hload | CONDITIONAL — load hypothesis `hload` (goal A) unproved |
| 25 | `anchor_recurrence` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hAe, hn, hs, hd, hload | CONDITIONAL — load hypothesis `hload` (goal A) unproved |
| 26 | `uncaptured_child_complexity_lt` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hkA, hmem | BANKED — replayed, sorry-free |
| 27 | `branchA_recurrence` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hAe, hn, hs, hws, h0, hload | CONDITIONAL — load hypothesis `hload` (goal A) unproved |
| 28 | `anchor_exists_concentrated_coordinate` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hn, hs, hd, hpos | BANKED — replayed, sorry-free |
| 29 | `resRad_windowZeros_eq` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 30 | `branchC_large_anchor_radius_drop` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hbig | BANKED — replayed, sorry-free |
| 31 | `branchC_chargeWidth_eq_zero` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hbig | BANKED — replayed, sorry-free |
| 32 | `branchC_all_children_radius_drop` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hbig, hγ | BANKED — replayed, sorry-free |
| 33 | `anchor_branch_exhaustive` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 34 | `globalAnchorMaster` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hn, hs | BANKED — replayed, sorry-free |
| 35 | `deployed_pure_child_mass_number` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext` | — | BANKED — replayed, sorry-free |
| 36 | `deployed_threshold_arith` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 37 | `deployed_safe_local_target` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hD, hA, hcard, h0, hload | CONDITIONAL — load hypothesis `hload` (goal A) unproved |
| 38 | `deployed_global_budget` | `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` | OK | `propext, Classical.choice, Quot.sound` | hD, hA, hcard, h0, hload, hM | CONDITIONAL — load hypothesis `hload` (goal A) unproved |
| 39 | `radius_descent_cost_bound` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hd, hstep, hdrop, hmult, hL | BANKED — general priced descent, multiplicity-bounded |
| 40 | `radius_drop_not_a_cost_bound` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — counterexample (branch-C objection sustained) |
| 41 | `chain_descent_cost_bound` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hstep, hdrop, hmult, hL | BANKED — replayed, sorry-free |
| 42 | `branchC_deployed_bound_of_branching` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hm, hstep, hdrop, hmult, hL, hrad | CONDITIONAL — needs total child multiplicity `m ≤ 6` (goal B) |
| 43 | `branchC_deployed_seven_exceeds` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — sharpness of `m ≤ 6` |
| 44 | `anchor_at_every_bad_challenge` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hγ | BANKED — branch-D quantifier (goal C) closed |
| 45 | `anchorMass_eq_zero_iff` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 46 | `exists_zero_mass_nonzero_poly` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hA | BANKED — separates `a₀ = 0` from `q₀ = 0` |
| 47 | `uncapturedChildCost_eq_zero_iff` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 48 | `branchA_massZero_recurrence` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hAe, hn, hs, hws, ha0, hload | CONDITIONAL — load hypothesis `hload` (goal A) unproved |
| 49 | `classRep_spec` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — replayed, sorry-free |
| 50 | `sum_classLoad_eq` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 51 | `classLoad_charging` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hn, hs | BANKED — replayed, sorry-free |
| 52 | `classLoad_bound` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hn, hs, hload | CONDITIONAL — per-coordinate load hypothesis `hload` (goal A) unproved |
| 53 | `classLoad_recurrence` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hAe, hn, hs, hd, hload | CONDITIONAL — per-coordinate load hypothesis `hload` (goal A) unproved |
| 54 | `deployed_load_gate` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hD, hA, hcard, h0, hgate | CONDITIONAL — reduction only; hypothesis `hgate` (goal A) unproved |
| 55 | `heavy_load_yields_class_family` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — replayed, sorry-free |
| 56 | `loaded_class_is_residual_child` | `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hkA, hR | BANKED — replayed, sorry-free |
| 57 | `sum_capturedMult_eq_card` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — goal B: exact total child multiplicity |
| 58 | `totalCapturedMult_le_iff` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — goal B: `m`-bound ⟺ bad-set bound |
| 59 | `card_posBadSet_le_of_totalCapturedMult_le` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | hγ₀, h | BANKED — goal B |
| 60 | `totalCapturedMult_le_card_posBadSet` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | — | BANKED — goal B |
| 61 | `branchC_multiplicity_six_forces_tiny_badSet` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | hγ₀, h | BANKED — goal B: `m ≤ 6` ⟹ `#posBadSet ≤ 7` (branch-C closure circular) |
| 62 | `anchor_isOfficialWitness` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — goal D |
| 63 | `officialClass_eq_of_officialAnchor` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — goal D (under `IsOfficialAnchor`) |
| 64 | `anchorMass_eq_official_of_officialAnchor` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — goal D (under `IsOfficialAnchor`) |
| 65 | `supp_eq_officialSupport_of_officialAnchor` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — goal D (under `IsOfficialAnchor`) |
| 66 | `chargeSet_anchor_eq_of_officialAnchor` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | h | BANKED — goal D (under `IsOfficialAnchor`) |
| 67 | `exists_official_anchor` | `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` | OK | `propext, Classical.choice, Quot.sound` | hA, hγ | BANKED — goal D: official anchor at every positive-mass challenge |

## Exact signatures

### `globalCost_eq`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem globalCost_eq (localCost : σ → ℕ) (children : σ → Finset σ) (mult : σ → σ → ℕ)
    (Φ : σ → ℕ) (X : σ) :
    globalCost localCost children mult Φ X = localCost X + ∑ R ∈ children X, mult X R * Φ R
```

### `capturedCost_add_uncaptured`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem capturedCost_add_uncaptured (mult : σ → σ → ℕ) (Φ : σ → ℕ) (X : σ) {A children : Finset σ}
    (hA : A ⊆ children) :
    capturedCost mult Φ X A + capturedCost mult Φ X (children \ A)
      = capturedCost mult Φ X children
```

### `capturedCost_union_of_disjoint`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem capturedCost_union_of_disjoint (mult : σ → σ → ℕ) (Φ : σ → ℕ) (X : σ) {A B : Finset σ}
    (h : Disjoint A B) :
    capturedCost mult Φ X (A ∪ B) = capturedCost mult Φ X A + capturedCost mult Φ X B
```

### `capturedCost_union_le`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem capturedCost_union_le (mult : σ → σ → ℕ) (Φ : σ → ℕ) (X : σ) (A B : Finset σ) :
    capturedCost mult Φ X (A ∪ B) ≤ capturedCost mult Φ X A + capturedCost mult Φ X B
```

### `sound`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem GlobalCertificate.sound {cost localCost cx Φ : σ → ℕ} {children : σ → Finset σ}
    {mult : σ → σ → ℕ} {capt : σ → Finset σ}
    (h : GlobalCertificate cost localCost cx Φ children mult capt) (X : σ) : cost X ≤ Φ X
```

### `strict_descent_not_a_cost_bound`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem strict_descent_not_a_cost_bound :
    ∃ (cost localCost cx : ℕ → ℕ) (children : ℕ → Finset ℕ) (mult : ℕ → ℕ → ℕ),
      (∀ X, cost X ≤ localCost X + ∑ Y ∈ children X, mult X Y * cost Y) ∧
      (∀ X, ∀ Y ∈ children X, cx Y < cx X) ∧
      (∀ B : ℕ, ∃ X, B < cost X)
```

### `anchorMass_le`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem anchorMass_le {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (an : AnchorData k e f₀ f₁) : anchorMass A an ≤ e
```

### `anchorMass_eq_zero_of_poly_zero`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem anchorMass_eq_zero_of_poly_zero {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    {an : AnchorData k e f₀ f₁} (h : an.poly = 0) : anchorMass A an = 0
```

### `exists_anchor_of_badSet_nonempty`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem exists_anchor_of_badSet_nonempty {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (h : (badSet k e f₀ f₁).Nonempty) :
    Nonempty (AnchorData k e f₀ f₁)
```

### `exists_terminal_anchor`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem exists_terminal_anchor {k e : ℕ} {f₀ f₁ : ↥D → F}
    (h : (zeroWitnessBadSet e f₀ f₁).Nonempty) :
    ∃ an : AnchorData k e f₀ f₁, an.poly = 0
```

### `terminal_anchor_or_all_positive_mass`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem terminal_anchor_or_all_positive_mass {k e : ℕ} {f₀ f₁ : ↥D → F} :
    (∃ an : AnchorData k e f₀ f₁, an.poly = 0) ∨
      badSet k e f₀ f₁ = posBadSet k e f₀ f₁
```

### `exists_min_mass_anchor`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem exists_min_mass_anchor {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (h : (posBadSet k e f₀ f₁).Nonempty) :
    ∃ an : AnchorData k e f₀ f₁, ∀ γ ∈ posBadSet k e f₀ f₁,
      anchorMass A an ≤ windowMass A (officialWitness k e f₀ f₁ γ).1
```

### `badSet_eq_empty_of_no_anchor`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem badSet_eq_empty_of_no_anchor {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (h : ¬ Nonempty (AnchorData k e f₀ f₁)) :
    badSet k e f₀ f₁ = ∅
```

### `mem_chargeSet_iff`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem mem_chargeSet_iff {k e : ℕ} {A S0 : Finset ↥D} {f₀ f₁ : ↥D → F} {γ : F} {i : ↥D} :
    i ∈ chargeSet k e A S0 f₀ f₁ γ ↔
      i ∈ officialSupport k e f₀ f₁ γ ∧ i ∉ A ∧ i ∉ S0
```

### `card_chargeSet_ge_anchor`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem card_chargeSet_ge_anchor {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hn : D.card = k + e + w) (hs : A.card = k + s)
    (an : AnchorData k e f₀ f₁) {γ : F} (hγ : γ ∈ posBadSet k e f₀ f₁) (hne : γ ≠ an.chal) :
    w - s - anchorMass A an ≤ (chargeSet k e A an.supp f₀ f₁ γ).card
```

### `card_chargeSet_ge_branchA`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem card_chargeSet_ge_branchA {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hn : D.card = k + e + w) (hs : A.card = k + s)
    (an : AnchorData k e f₀ f₁) (ha0 : anchorMass A an = 0)
    {γ : F} (hγ : γ ∈ posBadSet k e f₀ f₁) (hne : γ ≠ an.chal) :
    w - s ≤ (chargeSet k e A an.supp f₀ f₁ γ).card
```

### `chargeWidth_pos_branchB`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem chargeWidth_pos_branchB {w s a₀ : ℕ} (h : a₀ < w - s) : 0 < w - s - a₀
```

### `sum_erase_split`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem sum_erase_split (s : Finset F) (a : F) (g : F → ℕ) :
    ∑ x ∈ s, g x = ∑ x ∈ s.erase a, g x + (if a ∈ s then g a else 0)
```

### `totalChildCost_eq_captured_add_uncaptured`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem totalChildCost_eq_captured_add_uncaptured (k e : ℕ) (A : Finset ↥D) (f₀ f₁ : ↥D → F)
    (γ₀ : F) :
    totalChildCost k e A f₀ f₁
      = capturedChildCost k e A f₀ f₁ γ₀ + uncapturedChildCost k e A f₀ f₁ γ₀
```

### `capturedMult_add_anchorMult`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem capturedMult_add_anchorMult (k e : ℕ) (A R : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F) :
    capturedMult k e A R f₀ f₁ γ₀ + anchorMult k e A R f₀ f₁ γ₀
      = parentMult k e A R f₀ f₁
```

### `capturedChildCost_eq_sum_capturedMult`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem capturedChildCost_eq_sum_capturedMult (k e : ℕ) (A : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F) :
    capturedChildCost k e A f₀ f₁ γ₀
```

### `uncapturedChildCost_eq_zero_of_terminal_anchor`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem uncapturedChildCost_eq_zero_of_terminal_anchor {k e : ℕ} {A : Finset ↥D} {f₀ f₁ : ↥D → F}
    (an : AnchorData k e f₀ f₁) (h0 : an.poly = 0) :
    uncapturedChildCost k e A f₀ f₁ an.chal = 0
```

### `anchor_charging`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem anchor_charging {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hn : D.card = k + e + w) (hs : A.card = k + s)
    (an : AnchorData k e f₀ f₁) :
    (w - s - anchorMass A an) * capturedChildCost k e A f₀ f₁ an.chal
      ≤ ∑ i ∈ (Finset.univ : Finset ↥D) \ an.supp, chargeLoad k e A an.supp f₀ f₁ i
```

### `anchor_load_bound`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem anchor_load_bound {k e w s M : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hn : D.card = k + e + w) (hs : A.card = k + s)
    (an : AnchorData k e f₀ f₁)
    (hload : ∀ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      chargeLoad k e A an.supp f₀ f₁ i ≤ M) :
    (w - s - anchorMass A an) * capturedChildCost k e A f₀ f₁ an.chal ≤ e * M
```

### `anchor_recurrence`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

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

### `uncaptured_child_complexity_lt`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem uncaptured_child_complexity_lt {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hkA : k ≤ A.card) (an : AnchorData k e f₀ f₁)
    (hmem : an.chal ∈ posBadSet k e f₀ f₁) :
    instComplexity (resDim k (officialClass k e A f₀ f₁ an.chal))
        (resRad e A (officialClass k e A f₀ f₁ an.chal)) < instComplexity k e ∧
      resRad e A (officialClass k e A f₀ f₁ an.chal) < e
```

### `branchA_recurrence`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem branchA_recurrence {k e w s M : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hAe : A.card + e < D.card)
    (hn : D.card = k + e + w) (hs : A.card = k + s) (hws : 0 < w - s)
    (an : AnchorData k e f₀ f₁) (h0 : an.poly = 0)
    (hload : ∀ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      chargeLoad k e A an.supp f₀ f₁ i ≤ M) :
    (badSet k e f₀ f₁).card ≤ (e + 1) + e * M / (w - s)
```

### `anchor_exists_concentrated_coordinate`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem anchor_exists_concentrated_coordinate {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hn : D.card = k + e + w) (hs : A.card = k + s)
    (an : AnchorData k e f₀ f₁) (hd : 0 < w - s - anchorMass A an)
    (hpos : 0 < capturedChildCost k e A f₀ f₁ an.chal) :
    ∃ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      (w - s - anchorMass A an) * capturedChildCost k e A f₀ f₁ an.chal
        ≤ e * chargeLoad k e A an.supp f₀ f₁ i
```

### `resRad_windowZeros_eq`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem resRad_windowZeros_eq (e : ℕ) (A : Finset ↥D) (p : F[X]) :
    resRad e A (windowZeros A p) = e - windowMass A p
```

### `branchC_large_anchor_radius_drop`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem branchC_large_anchor_radius_drop {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (an : AnchorData k e f₀ f₁)
    (hbig : w - s ≤ anchorMass A an) :
    resRad e A (windowZeros A an.poly) + (w - s) ≤ e
```

### `branchC_chargeWidth_eq_zero`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem branchC_chargeWidth_eq_zero {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (an : AnchorData k e f₀ f₁) (hbig : w - s ≤ anchorMass A an) :
    w - s - anchorMass A an = 0
```

### `branchC_all_children_radius_drop`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem branchC_all_children_radius_drop {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A)
    (hbig : ∀ γ ∈ posBadSet k e f₀ f₁, w - s ≤ windowMass A (officialWitness k e f₀ f₁ γ).1)
    {γ : F} (hγ : γ ∈ posBadSet k e f₀ f₁) :
    resRad e A (officialClass k e A f₀ f₁ γ) + (w - s) ≤ e
```

### `anchor_branch_exhaustive`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem anchor_branch_exhaustive {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D} :
    ¬ Nonempty (AnchorData k e f₀ f₁) ∨
      ∃ an : AnchorData k e f₀ f₁,
        anchorMass A an = 0 ∨
          (0 < anchorMass A an ∧ anchorMass A an < w - s) ∨ w - s ≤ anchorMass A an
```

### `globalAnchorMaster`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem globalAnchorMaster {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hn : D.card = k + e + w) (hs : A.card = k + s) :
    (¬ Nonempty (AnchorData k e f₀ f₁) → badSet k e f₀ f₁ = ∅) ∧
    (∀ an : AnchorData k e f₀ f₁,
      totalChildCost k e A f₀ f₁
```

### `deployed_pure_child_mass_number`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem deployed_pure_child_mass_number :
    274980728111395087 * 69632 / 978944 = 19559298652274964
```

### `deployed_threshold_arith`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem deployed_threshold_arith :
    978945 + 978944 * 19559298652205332 / 69632 ≤ 274980728111395087
```

### `deployed_safe_local_target`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem deployed_safe_local_target {f₀ f₁ : ↥D → F} {A : Finset ↥D} {M : ℕ}
    (hD : D.card = 2097152) (hA : NormalisedWindow 1048576 f₀ f₁ A) (hcard : A.card = 1048576)
    (an : AnchorData 1048576 978944 f₀ f₁) (h0 : an.poly = 0)
    (hload : ∀ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      chargeLoad 1048576 978944 A an.supp f₀ f₁ i ≤ M) :
    (978944 + 1) + capturedChildCost 1048576 978944 A f₀ f₁ an.chal
        + uncapturedChildCost 1048576 978944 A f₀ f₁ an.chal
      ≤ 978945 + 978944 * M / 69632
```

### `deployed_global_budget`  — `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`

```lean
theorem deployed_global_budget {f₀ f₁ : ↥D → F} {A : Finset ↥D} {M : ℕ}
    (hD : D.card = 2097152) (hA : NormalisedWindow 1048576 f₀ f₁ A) (hcard : A.card = 1048576)
    (an : AnchorData 1048576 978944 f₀ f₁) (h0 : an.poly = 0)
    (hload : ∀ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      chargeLoad 1048576 978944 A an.supp f₀ f₁ i ≤ M)
    (hM : M ≤ 19559298652205332) :
    (badSet 1048576 978944 f₀ f₁).card ≤ 274980728111395087
```

### `radius_descent_cost_bound`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem radius_descent_cost_bound (cost localCost rad : σ → ℕ) (children : σ → Finset σ)
    (mult : σ → σ → ℕ) (L m d : ℕ) (hd : 0 < d)
    (hstep : ∀ X, cost X ≤ localCost X + ∑ Y ∈ children X, mult X Y * cost Y)
    (hdrop : ∀ X, ∀ Y ∈ children X, rad Y + d ≤ rad X)
    (hmult : ∀ X, ∑ Y ∈ children X, mult X Y ≤ m)
    (hL : ∀ X, localCost X ≤ L) (X : σ) :
    cost X ≤ L * ∑ j ∈ Finset.range (rad X / d + 1), m ^ j
```

### `radius_drop_not_a_cost_bound`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem radius_drop_not_a_cost_bound (B : ℕ) :
    ∃ (e : ℕ) (cost localCost rad : ℕ → ℕ) (children : ℕ → Finset ℕ) (mult : ℕ → ℕ → ℕ) (X : ℕ),
      (∀ X, cost X ≤ localCost X + ∑ Y ∈ children X, mult X Y * cost Y) ∧
      (∀ X, ∀ Y ∈ children X, rad Y + 1 ≤ rad X) ∧
      (∀ X, rad X ≤ e) ∧ (∀ X, localCost X ≤ 1) ∧ B < cost X
```

### `chain_descent_cost_bound`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem chain_descent_cost_bound (cost localCost rad : σ → ℕ) (children : σ → Finset σ)
    (mult : σ → σ → ℕ) (L : ℕ)
    (hstep : ∀ X, cost X ≤ localCost X + ∑ Y ∈ children X, mult X Y * cost Y)
    (hdrop : ∀ X, ∀ Y ∈ children X, rad Y + 1 ≤ rad X)
    (hmult : ∀ X, ∑ Y ∈ children X, mult X Y ≤ 1)
    (hL : ∀ X, localCost X ≤ L) (X : σ) :
    cost X ≤ L * (rad X + 1)
```

### `branchC_deployed_bound_of_branching`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem branchC_deployed_bound_of_branching (cost localCost rad : σ → ℕ) (children : σ → Finset σ)
    (mult : σ → σ → ℕ) (m : ℕ) (hm : m ≤ 6)
    (hstep : ∀ X, cost X ≤ localCost X + ∑ Y ∈ children X, mult X Y * cost Y)
    (hdrop : ∀ X, ∀ Y ∈ children X, rad Y + 69632 ≤ rad X)
    (hmult : ∀ X, ∑ Y ∈ children X, mult X Y ≤ m)
    (hL : ∀ X, localCost X ≤ 978945) (hrad : ∀ X, rad X ≤ 978944) (X : σ) :
    cost X ≤ 274980728111395087
```

### `branchC_deployed_seven_exceeds`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem branchC_deployed_seven_exceeds :
    274980728111395087 < 978945 * ∑ j ∈ Finset.range 15, (7 : ℕ) ^ j
```

### `anchor_at_every_bad_challenge`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem anchor_at_every_bad_challenge {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) {γ : F} (hγ : γ ∈ badSet k e f₀ f₁) :
    ∃ an : AnchorData k e f₀ f₁, an.chal = γ
```

### `anchorMass_eq_zero_iff`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem anchorMass_eq_zero_iff {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (an : AnchorData k e f₀ f₁) :
    anchorMass A an = 0 ↔ ∀ x ∈ A, an.poly.eval (x : F) = 0
```

### `exists_zero_mass_nonzero_poly`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem exists_zero_mass_nonzero_poly {k : ℕ} {A : Finset ↥D} (hA : A.card < k) :
    ∃ p : F[X], p ≠ 0 ∧ p.degree < (k : WithBot ℕ) ∧ windowMass A p = 0
```

### `uncapturedChildCost_eq_zero_iff`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem uncapturedChildCost_eq_zero_iff {k e : ℕ} {A : Finset ↥D} {f₀ f₁ : ↥D → F} {γ₀ : F} :
    uncapturedChildCost k e A f₀ f₁ γ₀ = 0 ↔
      (γ₀ ∉ posBadSet k e f₀ f₁ ∨ childCost k e A f₀ f₁ γ₀ = 0)
```

### `branchA_massZero_recurrence`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

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

### `classRep_spec`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem classRep_spec {k e : ℕ} {A : Finset ↥D} {f₀ f₁ : ↥D → F} {γ₀ : F} {R : Finset ↥D}
    (h : ∃ γ ∈ capturedChallenges k e f₀ f₁ γ₀, officialClass k e A f₀ f₁ γ = R) :
    classRep k e A f₀ f₁ γ₀ R ∈ capturedChallenges k e f₀ f₁ γ₀ ∧
      officialClass k e A f₀ f₁ (classRep k e A f₀ f₁ γ₀ R) = R
```

### `sum_classLoad_eq`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem sum_classLoad_eq (k e : ℕ) (A S0 : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F) :
    ∑ i ∈ (Finset.univ : Finset ↥D) \ S0, classLoad k e A S0 f₀ f₁ γ₀ i
```

### `classLoad_charging`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem classLoad_charging {k e w s : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hn : D.card = k + e + w) (hs : A.card = k + s)
    (an : AnchorData k e f₀ f₁) :
    (w - s - anchorMass A an) * capturedChildCost k e A f₀ f₁ an.chal
      ≤ ∑ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
          classLoad k e A an.supp f₀ f₁ an.chal i
```

### `classLoad_bound`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem classLoad_bound {k e w s M : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hn : D.card = k + e + w) (hs : A.card = k + s)
    (an : AnchorData k e f₀ f₁)
    (hload : ∀ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      classLoad k e A an.supp f₀ f₁ an.chal i ≤ M) :
    (w - s - anchorMass A an) * capturedChildCost k e A f₀ f₁ an.chal ≤ e * M
```

### `classLoad_recurrence`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem classLoad_recurrence {k e w s M : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) (hAe : A.card + e < D.card)
    (hn : D.card = k + e + w) (hs : A.card = k + s)
    (an : AnchorData k e f₀ f₁) (hd : 0 < w - s - anchorMass A an)
    (hload : ∀ i ∈ (Finset.univ : Finset ↥D) \ an.supp,
      classLoad k e A an.supp f₀ f₁ an.chal i ≤ M) :
    (badSet k e f₀ f₁).card
      ≤ (e + 1) + e * M / (w - s - anchorMass A an)
        + uncapturedChildCost k e A f₀ f₁ an.chal
```

### `deployed_load_gate`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem deployed_load_gate {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hD : D.card = 2097152) (hA : NormalisedWindow 1048576 f₀ f₁ A) (hcard : A.card = 1048576)
    (an : AnchorData 1048576 978944 f₀ f₁) (h0 : an.poly = 0)
    (hgate : LoadGate 1048576 978944 A an.supp f₀ f₁ an.chal) :
    (badSet 1048576 978944 f₀ f₁).card ≤ 274980728111395087
```

### `heavy_load_yields_class_family`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem heavy_load_yields_class_family {k e : ℕ} {A S0 : Finset ↥D} {f₀ f₁ : ↥D → F} {γ₀ : F}
    (i : ↥D) :
    ∑ R ∈ (capturedClasses k e A f₀ f₁ γ₀).filter
        (fun R => i ∈ classChargeSet k e A S0 f₀ f₁ γ₀ R),
      capturedMult k e A R f₀ f₁ γ₀ * classCost k e A R f₀ f₁
      = classLoad k e A S0 f₀ f₁ γ₀ i
```

### `loaded_class_is_residual_child`  — `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean`

```lean
theorem loaded_class_is_residual_child {k e : ℕ} {A : Finset ↥D} {f₀ f₁ : ↥D → F} {γ₀ : F}
    (hA : NormalisedWindow k f₀ f₁ A) (hkA : k ≤ A.card) {R : Finset ↥D}
    (hR : R ∈ capturedClasses k e A f₀ f₁ γ₀) :
    ∃ γ ∈ posBadSet k e f₀ f₁, officialClass k e A f₀ f₁ γ = R ∧
      instComplexity (resDim k R) (resRad e A R) < instComplexity k e
```

### `sum_capturedMult_eq_card`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem sum_capturedMult_eq_card (k e : ℕ) (A : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F) :
    ∑ R ∈ capturedClasses k e A f₀ f₁ γ₀, capturedMult k e A R f₀ f₁ γ₀
      = ((posBadSet k e f₀ f₁).erase γ₀).card
```

### `totalCapturedMult_le_iff`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem totalCapturedMult_le_iff (k e : ℕ) (A : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F) (m : ℕ) :
    (∑ R ∈ capturedClasses k e A f₀ f₁ γ₀, capturedMult k e A R f₀ f₁ γ₀ ≤ m)
      ↔ ((posBadSet k e f₀ f₁).erase γ₀).card ≤ m
```

### `card_posBadSet_le_of_totalCapturedMult_le`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem card_posBadSet_le_of_totalCapturedMult_le {k e : ℕ} {A : Finset ↥D} {f₀ f₁ : ↥D → F}
    {γ₀ : F} (hγ₀ : γ₀ ∈ posBadSet k e f₀ f₁) (m : ℕ)
    (h : ∑ R ∈ capturedClasses k e A f₀ f₁ γ₀, capturedMult k e A R f₀ f₁ γ₀ ≤ m) :
    (posBadSet k e f₀ f₁).card ≤ m + 1
```

### `totalCapturedMult_le_card_posBadSet`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem totalCapturedMult_le_card_posBadSet (k e : ℕ) (A : Finset ↥D) (f₀ f₁ : ↥D → F) (γ₀ : F) :
    ∑ R ∈ capturedClasses k e A f₀ f₁ γ₀, capturedMult k e A R f₀ f₁ γ₀
      ≤ (posBadSet k e f₀ f₁).card
```

### `branchC_multiplicity_six_forces_tiny_badSet`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem branchC_multiplicity_six_forces_tiny_badSet {k e : ℕ} {A : Finset ↥D} {f₀ f₁ : ↥D → F}
    {γ₀ : F} (hγ₀ : γ₀ ∈ posBadSet k e f₀ f₁)
    (h : ∑ R ∈ capturedClasses k e A f₀ f₁ γ₀, capturedMult k e A R f₀ f₁ γ₀ ≤ 6) :
    (posBadSet k e f₀ f₁).card ≤ 7
```

### `anchor_isOfficialWitness`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem anchor_isOfficialWitness {k e : ℕ} {f₀ f₁ : ↥D → F} (an : AnchorData k e f₀ f₁)
    (h : an.poly ≠ 0) :
    IsOfficialWitness k e f₀ f₁ an.chal (an.poly, an.supp)
```

### `officialClass_eq_of_officialAnchor`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem officialClass_eq_of_officialAnchor {k e : ℕ} {A : Finset ↥D} {f₀ f₁ : ↥D → F}
    (an : AnchorData k e f₀ f₁) (h : IsOfficialAnchor k e f₀ f₁ an) :
    officialClass k e A f₀ f₁ an.chal = windowZeros A an.poly
```

### `anchorMass_eq_official_of_officialAnchor`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem anchorMass_eq_official_of_officialAnchor {k e : ℕ} {A : Finset ↥D} {f₀ f₁ : ↥D → F}
    (an : AnchorData k e f₀ f₁) (h : IsOfficialAnchor k e f₀ f₁ an) :
    anchorMass A an = windowMass A (officialWitness k e f₀ f₁ an.chal).1
```

### `supp_eq_officialSupport_of_officialAnchor`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem supp_eq_officialSupport_of_officialAnchor {k e : ℕ} {f₀ f₁ : ↥D → F}
    (an : AnchorData k e f₀ f₁) (h : IsOfficialAnchor k e f₀ f₁ an) :
    an.supp = officialSupport k e f₀ f₁ an.chal
```

### `chargeSet_anchor_eq_of_officialAnchor`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem chargeSet_anchor_eq_of_officialAnchor {k e : ℕ} {A : Finset ↥D} {f₀ f₁ : ↥D → F}
    (an : AnchorData k e f₀ f₁) (h : IsOfficialAnchor k e f₀ f₁ an) :
    chargeSet k e A an.supp f₀ f₁ an.chal = ∅
```

### `exists_official_anchor`  — `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`

```lean
theorem exists_official_anchor {k e : ℕ} {f₀ f₁ : ↥D → F} {A : Finset ↥D}
    (hA : NormalisedWindow k f₀ f₁ A) {γ : F} (hγ : γ ∈ posBadSet k e f₀ f₁) :
    ∃ an : AnchorData k e f₀ f₁, an.chal = γ ∧ IsOfficialAnchor k e f₀ f₁ an ∧
      an.poly = (officialWitness k e f₀ f₁ γ).1 ∧ an.supp = officialSupport k e f₀ f₁ γ
```
