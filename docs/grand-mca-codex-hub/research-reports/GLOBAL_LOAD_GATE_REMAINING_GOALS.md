# GlobalLoadGate — delivered artifact and the four separated remaining goals

This file records (i) the portable replay package, (ii) the canonical replay result, and
(iii) the four remaining goals, separated, with the exact Lean statement that each one needs.

The per-theorem table (name, exact signature, source file, replay result, axioms, hypotheses,
status) is in `GLOBAL_LOAD_GATE_REPLAY_TABLE.md`.

---

## 0. Artifact

* Portable ZIP: `ARISTOTLE_GLOBAL_LOAD_GATE_PACKAGE.zip`
* Same content as a plain-text tree: `package/global_load_gate_replay/`

Package contents:

| item | path in package |
|---|---|
| exact commit of the exported tree | `COMMIT.txt` (`3ae4247c000b5609ed0f1b8cab1e710423cdc617`) |
| full transitive project-import source closure | `src/RequestProject/…` |
| `GlobalAnchorRecursion.lean` | `src/RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean` |
| `GlobalRecursionLoadGate.lean` | `src/RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` |
| axiom-audit file 1 | `src/RequestProject/GlobalAnchorRecursionAxiomAudit.lean` |
| axiom-audit file 2 | `src/RequestProject/GlobalRecursionLoadGateAxiomAudit.lean` |
| replay report | `GLOBAL_LOAD_GATE_REPLAY_REPORT.md` |
| composition report | `GLOBAL_RECURSION_COMPOSITION_REPORT.md` |
| goals + table | `GLOBAL_LOAD_GATE_REMAINING_GOALS.md`, `GLOBAL_LOAD_GATE_REPLAY_TABLE.md` |
| build log of the canonical replay | `REPLAY_BUILD.log` |
| axiom listing of the canonical replay | `REPLAY_AXIOMS.txt` |
| dependency manifest (modules, line counts, digests) | `MANIFEST.md` |
| SHA-256 digest of every packaged file | `SHA256SUMS.txt` |
| build configuration | `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` |
| replay instructions | `README_REPLAY.md` |

Replay performed in the canonical tree, from the committed sources:

```
lake build RequestProject.GlobalAnchorRecursionAxiomAudit \
           RequestProject.GlobalRecursionLoadGateAxiomAudit
→ Build completed successfully (8047 jobs)
→ 56 `#print axioms` lines, every list ⊆ {propext, Classical.choice, Quot.sound}
→ no `sorry` / `admit` / `axiom` / `implemented_by` in code in the closure
```

Verdict of the replay: **BANKED at source / build / axiom level** for the *Lean statements as
written*. It does not upgrade any clause whose Lean statement is conditional; the conditional
clauses are exactly the four goals below.

---

## A. Full class-level recursive load bound, or a priced high-load descent

**Status: OPEN.** This is the single obstruction of the layer.

What must be proved (either form):

*A1 — the bound.* For every state (window `A`, anchor support `S0 = an.supp`, anchor challenge
`γ₀ = an.chal`) and every coordinate `i ∉ S0`:

```lean
classLoad k e A an.supp f₀ f₁ an.chal i ≤ 19559298652205332
```

i.e. `LoadGate k e A an.supp f₀ f₁ an.chal`, the explicit hypothesis of `deployed_load_gate`.

*A2 — priced high-load descent.* Instead of the uniform bound, a potential/certificate argument
that pays the excess: for `M` as above,

```lean
theorem priced_high_load (…) (i : ↥D)
    (hheavy : M < classLoad k e A S0 f₀ f₁ γ₀ i) :
    ∃ (charge : ℕ), classLoad k e A S0 f₀ f₁ γ₀ i ≤ M + charge ∧ (an explicit paying descent)
```

Available towards it, already banked: `classLoad_charging`, `classLoad_bound`,
`classLoad_recurrence`, `sum_classLoad_eq` (exact double counting),
`heavy_load_yields_class_family` (an over-loaded coordinate is carried by an explicit, canonically
assigned family of captured classes of total weight exactly `classLoad … i`) and
`loaded_class_is_residual_child` (every such class is a residual child of strictly smaller
`instComplexity`). Missing: the *paying* half — a decrease of an explicit potential, or a cost
certificate covering `classLoad … i − M`. `anchor_exists_concentrated_coordinate` gives only a
lower bound on the worst load (a coordinate carrying a `(w−s)/e ≈ 1/14.06` fraction of the captured
cost), never an upper bound, so the bound is not derivable from the counting already banked.

---

## B. Branch-C cost closure, including "total child multiplicity ≤ 6"

**Status: OPEN as a cost closure; the missing multiplicity theorem is now identified exactly and
proved to be equivalent to a bad-set cardinality bound (hence not available from the branch).**

Branch C banks a *radius* inequality only:

```lean
branchC_large_anchor_radius_drop : resRad e A (windowZeros A an.poly) + (w - s) ≤ e
```

and `radius_drop_not_a_cost_bound` shows a radius inequality alone never bounds recursive cost.
The exact price is `radius_descent_cost_bound`; at the deployed parameters
(`e = 978944`, `w − s = 69632`, `L = e + 1`) `branchC_deployed_bound_of_branching` closes the branch
**iff** the total child multiplicity of every state is `≤ 6` (`branchC_deployed_seven_exceeds`:
`m = 7` already exceeds the deployed budget `274980728111395087`).

The missing theorem was "total child multiplicity ≤ 6". In `RequestProject/Root/CodingTheory/
GlobalRecursionBranchGaps.lean` it is settled as follows:

```lean
theorem sum_capturedMult_eq_card :
    ∑ R ∈ capturedClasses k e A f₀ f₁ γ₀, capturedMult k e A R f₀ f₁ γ₀
      = ((posBadSet k e f₀ f₁).erase γ₀).card

theorem totalCapturedMult_le_iff (m : ℕ) :
    (∑ R ∈ capturedClasses k e A f₀ f₁ γ₀, capturedMult k e A R f₀ f₁ γ₀ ≤ m)
      ↔ ((posBadSet k e f₀ f₁).erase γ₀).card ≤ m

theorem card_posBadSet_le_of_totalCapturedMult_le (hγ₀ : γ₀ ∈ posBadSet k e f₀ f₁) (m : ℕ)
    (h : ∑ R ∈ capturedClasses k e A f₀ f₁ γ₀, capturedMult k e A R f₀ f₁ γ₀ ≤ m) :
    (posBadSet k e f₀ f₁).card ≤ m + 1
```

Consequence, stated plainly: *the branch-C multiplicity hypothesis `m ≤ 6` is not a structural
branching fact but exactly the statement that the state has at most `7` positive-mass bad
challenges.* Assuming it at every state therefore assumes a bad-set cardinality bound of the same
kind that the recursion is meant to prove, so branch C cannot be closed this way. Closing branch C
requires either

* a genuine bound `m` on the number of *distinct captured classes with multiplicity* that is
  independent of the bad-set size (then `radius_descent_cost_bound` applies with that `m`, giving
  `cost ≤ L · Σ_{j ≤ 14} m^j`, useful only for `m ≤ 6`), or
* a different pricing of the radius drop (amortised / potential based), not covered by any theorem
  in the layer.

---

## C. Branch-D quantifier proof

**Status: CLOSED (banked).**

```lean
badSet_eq_empty_of_no_anchor (hA : NormalisedWindow k f₀ f₁ A)
    (h : ¬ Nonempty (AnchorData k e f₀ f₁)) : badSet k e f₀ f₁ = ∅

anchor_at_every_bad_challenge (hA : NormalisedWindow k f₀ f₁ A)
    {γ : F} (hγ : γ ∈ badSet k e f₀ f₁) : ∃ an : AnchorData k e f₀ f₁, an.chal = γ
```

The quantifier of the branch-D hypothesis is `¬ ∃` over *all* anchors, and the second theorem shows
the anchor family is indexed by the complete bad family: every bad challenge is itself an anchor.
Hence "no usable anchor" is genuinely existential over the complete bad family and branch D is
sound. Both replayed with axioms `{propext, Classical.choice, Quot.sound}`.

---

## D. Exact compatibility of branches A/B with official witness semantics

**Status: PARTIALLY CLOSED.** What is proved, and what is not, is now explicit.

Proved (`RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean`):

```lean
theorem anchor_isOfficialWitness (an : AnchorData k e f₀ f₁) (h : an.poly ≠ 0) :
    IsOfficialWitness k e f₀ f₁ an.chal (an.poly, an.supp)

theorem exists_official_anchor (hA : NormalisedWindow k f₀ f₁ A)
    (hγ : γ ∈ posBadSet k e f₀ f₁) :
    ∃ an : AnchorData k e f₀ f₁, an.chal = γ ∧ IsOfficialAnchor k e f₀ f₁ an ∧
      an.poly = (officialWitness k e f₀ f₁ γ).1 ∧ an.supp = officialSupport k e f₀ f₁ γ

theorem officialClass_eq_of_officialAnchor (an : AnchorData k e f₀ f₁)
    (h : IsOfficialAnchor k e f₀ f₁ an) :
    officialClass k e A f₀ f₁ an.chal = windowZeros A an.poly

theorem anchorMass_eq_official_of_officialAnchor (an : AnchorData k e f₀ f₁)
    (h : IsOfficialAnchor k e f₀ f₁ an) :
    anchorMass A an = windowMass A (officialWitness k e f₀ f₁ an.chal).1

theorem supp_eq_officialSupport_of_officialAnchor (an : AnchorData k e f₀ f₁)
    (h : IsOfficialAnchor k e f₀ f₁ an) :
    an.supp = officialSupport k e f₀ f₁ an.chal

theorem chargeSet_anchor_eq_of_officialAnchor (an : AnchorData k e f₀ f₁)
    (h : IsOfficialAnchor k e f₀ f₁ an) :
    chargeSet k e A an.supp f₀ f₁ an.chal = ∅
```

so branches A and B may be run **without loss of generality at an official anchor**: at every
positive-mass bad challenge there is an anchor whose data *is* the canonical official witness, and
for such an anchor the branch quantities (`anchorMass`, the branch-C class `windowZeros A an.poly`)
agree on the nose with the official-witness quantities used by `chargeSet`, `officialClass`,
`childCost` and `classLoad`.

Not proved (remaining part of D):

1. `AnchorData` does **not** require `an.chal ∈ badSet` (badness additionally requires
   `¬ LineCloseOn k S f₀ f₁`), and does not require `(an.poly, an.supp)` to be *the canonical*
   official witness. For a non-official anchor the identities above may fail, and no theorem in
   the layer forces the anchor selected by `exists_min_mass_anchor` to be official.
2. Consequently the deployed statements `deployed_safe_local_target`, `deployed_global_budget`,
   `deployed_load_gate` are stated for an arbitrary `an : AnchorData …` with `an.poly = 0`; the
   compatibility upgrade needed is a canonical-selection lemma
   `∃ an, IsOfficialAnchor … an ∧ (branch condition)` for each of the branches A and B, i.e.
   selection of the minimal-mass anchor *inside* the official family.

Until 1–2 are proved, branches A/B are exactly compatible with official witness semantics **only
under the hypothesis `IsOfficialAnchor`**.

---

## Summary of statuses

| goal | content | status |
|---|---|---|
| A | full class-level recursive load bound, or priced high-load descent | OPEN (single obstruction) |
| B | branch-C cost closure; "total child multiplicity ≤ 6" | multiplicity theorem RESOLVED (equivalent to `#posBadSet ≤ 7`, hence unavailable); cost closure OPEN |
| C | branch-D quantifier proof | CLOSED |
| D | branches A/B vs official witness semantics | CLOSED under `IsOfficialAnchor` (proved, with existence at every positive-mass challenge); canonical selection of an official anchor for the min-mass branch OPEN |
