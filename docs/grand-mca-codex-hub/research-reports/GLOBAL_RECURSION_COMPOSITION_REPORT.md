# Global recursion / composition layer — anchors of arbitrary mass

Lean source: `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`
Axiom audit: `RequestProject/GlobalAnchorRecursionAxiomAudit.lean` (38 declarations; only
`propext`, `Classical.choice`, `Quot.sound`).

**Replay status of the inherited layer.** Every claim used from the previous work was re-checked in
this session, not taken on report:

* source replay + build: `lake build RequestProject.Root.CodingTheory.MassDescentRecursion` — clean;
* axiom audit: `RequestProject/MassDescentRecursionAxiomAudit.lean` re-run — only the three standard
  axioms;
* dependency audit: the transitive project-import closure of the new file is 19 modules, and none
  of them contains `sorry`, `admit`, `axiom` or `@[implemented_by]`.

Accordingly the inherited interfaces below are marked **BANKED**. No statement in this report is
marked BANKED without a replayed, sorry-free, axiom-audited Lean source.

Nothing in the local projective / ResidualClass geometry was rebuilt; the canonical residual child,
exact fibre, RS-closure, official witness transport and strict-decrease interfaces are imported
unchanged from `BranchingControl` / `MassDescentRecursion`.

---

## 0. Global cost and potential (explicit definitions)

```
Cost(X)          = localCost(X) + Σ_R μ_R · Φ(R)                     globalCost
capturedCost(A)  = Σ_{R ∈ A} μ_R · Φ(R)                              capturedCost
```

terminal states carrying `localCost` alone (here `localCost(X) = e + 1`, the zero-witness branch).

| clause | Lean | status |
|---|---|---|
| `Cost(X) = localCost(X) + Σ_R μ_R Φ(R)` | `globalCost`, `globalCost_eq` | **BANKED** |
| captured/uncaptured split is exact (no double counting) | `capturedCost_add_uncaptured` | **BANKED** |
| two priced families may be added only when disjoint | `capturedCost_union_of_disjoint` | **BANKED** |
| overlapping families only give `≤` | `capturedCost_union_le` | **BANKED** |
| safe local target ⇒ `cost ≤ Φ` (the only composition rule) | `GlobalCertificate`, `GlobalCertificate.sound` | **BANKED** |
| strict well-founded descent does **not** bound cost | `strict_descent_not_a_cost_bound` | **BANKED** |

`GlobalCertificate` bundles exactly four obligations: the one-step recursion with the *full
recursive* child cost, the strict decrease, the canonical captured family `A(X) ⊆ children(X)`, and
the explicit numerical target

```
localCost X + capturedCost(A) + Σ_{R ∉ A} μ_R·Φ(R)  ≤  Φ(X).
```

`strict_descent_not_a_cost_bound` exhibits a state space with strictly decreasing complexity on
every child edge and an exact one-step recursion whose cost is `2^depth`, hence unbounded:
termination is not amortisation. Every branch below therefore supplies a numerical decrease.

## 1. Anchors — no zero-mass assumption

`AnchorData k e f₀ f₁` = a challenge `γ₀`, a codeword `q₀` with `deg q₀ < k`, and a support `S0`
with `|S0| ≥ t = |D| − e` on which `f₀ + γ₀f₁ = q₀`. Its mass is `a₀ = windowMass A q₀`
(`anchorMass`), which is **not** assumed to be `0`; the previously used terminal anchor is the
special case `q₀ = 0`.

Charge width is *derived*, never postulated. From the official support definitions only:

```
|S_γ ∖ A|        ≥ (w − s) + a          card_sdiff_window_ge         (BANKED, inherited)
|(S_γ ∩ S0) ∖ A| ≤ a + a₀               card_inter_sdiff_window_le   (BANKED, inherited)
⇒ |D_γ| = |(S_γ ∖ A) ∖ S0| ≥ w − s − a₀                              card_chargeSet_ge_anchor
```

The proved formula is `w − s − a₀` (truncated in `ℕ`); it agrees with the shape
`max(0, w−s−a₀)` but is obtained as a consequence, and the hypothesis `γ ≠ γ₀` is genuinely needed
(the transport lemma requires distinct challenges), which is what forces the captured/uncaptured
split below.

## 2. The four anchor branches

Exhaustiveness: `anchor_branch_exhaustive`; all four collected in `globalAnchorMaster`.

### Branch A — `a₀ = 0`

1. *anchor existence*: `exists_anchor_of_badSet_nonempty` (every bad challenge is an anchor);
   a terminal anchor exists as soon as the zero-witness branch is occupied
   (`exists_terminal_anchor`, `terminal_anchor_or_all_positive_mass`). **BANKED**
2. *exact charge set*: `D_γ = (S_γ ∖ A) ∖ S0`, membership `mem_chargeSet_iff`. **BANKED**
3. *charge-width lower bound*: `w − s ≤ |D_γ|` (`card_chargeSet_ge_branchA`). **BANKED**
4. *canonical child classes*: `officialClass`, `occupiedClasses`, `capturedClasses`. **BANKED**
5. *exact fibre multiplicities*: `parentMult`, and
   `capturedMult R + anchorMult R = parentMult R` (`capturedMult_add_anchorMult`). **BANKED**
6. *full recursive child weight*: `classCost R = #Bad(child R)`, `childCost`. **BANKED**
7. *disjoint captured/uncaptured partition*:
   `totalChildCost = capturedChildCost + uncapturedChildCost`
   (`totalChildCost_eq_captured_add_uncaptured`), and for a terminal anchor the uncaptured term is
   *proved* zero (`uncapturedChildCost_eq_zero_of_terminal_anchor`). **BANKED**
8. *recurrence*: `(w−s)·capturedCost ≤ Σ_{i∉S0} load(i) ≤ e·M` and
   `#Bad ≤ (e+1) + e·M/(w−s)` (`anchor_charging`, `anchor_load_bound`, `branchA_recurrence`),
   with `M` the single remaining hypothesis. **BANKED (conditional on `M`)**

### Branch B — `0 < a₀ < w − s`

1. anchor existence: `exists_min_mass_anchor` supplies the canonical minimal-mass anchor. **BANKED**
2. exact charge set: as above. **BANKED**
3. charge width: `w − s − a₀ ≤ |D_γ|` with `0 < w − s − a₀` (`card_chargeSet_ge_anchor`,
   `chargeWidth_pos_branchB`). **BANKED**
4.–6. as in branch A. **BANKED**
7. captured family `posBadSet.erase γ₀`, uncaptured family `posBadSet ∩ {γ₀}` — a genuine
   partition at challenge level; the anchor challenge may itself carry positive mass and is never
   charged against its own support. **BANKED**
8. recurrence
   ```
   (w−s−a₀)·capturedCost ≤ Σ_{i∉S0} load(i) ≤ e·M                (anchor_charging, anchor_load_bound)
   #Bad ≤ (e+1) + e·M/(w−s−a₀) + uncapturedCost                  (anchor_recurrence)
   ```
   The uncaptured term is one residual state, strictly smaller in the imported complexity order
   (`uncaptured_child_complexity_lt`), so the recurrence has the admissible shape
   `localCost + capturedCost(A) + Σ_j μ_j Φ(X'_j)`. **BANKED (conditional on `M`)**
   Concentration is derived by double counting from the actual weighted charge sets and only under
   a positive proved width (`anchor_exists_concentrated_coordinate`): with fraction
   `(w−s−a₀)/e`. **BANKED**

### Branch C — `a₀ ≥ w − s`

The derived charge width is literally `0` (`branchC_chargeWidth_eq_zero`); **no** concentration
statement is available and none is applied. The independent large-anchor theorem is exposed
instead: the mass has already been spent inside the window, so the residual radius drops by at
least the full charge width,

```
resRad e A (windowZeros A q₀) + (w − s) ≤ e          branchC_large_anchor_radius_drop
```

and in the global large-mass regime the same drop holds for every canonical child
(`branchC_all_children_radius_drop`), bounding the descent depth by `e/(w−s)`. **BANKED**

### Branch D — no usable anchor

`badSet_eq_empty_of_no_anchor`: if no `AnchorData` exists the state is terminal, `#Bad = 0`. No
concentration is applied. **BANKED**

## 3. Deployed constants

```
n = 2097152    k = 1048576    e = 978944    w = 69632    s = 0
B* = 274980728111395087
```

| clause | Lean | status |
|---|---|---|
| `⌊B*·w/e⌋ = 19559298652274964` — *arithmetic only*, a conditional budget for pure child mass, **not** a congestion theorem, and nothing is derived from it | `deployed_pure_child_mass_number` | **BANKED (arithmetic)** |
| safe local target at the deployed state: `978945 + capturedCost + uncapturedCost ≤ 978945 + 978944·M/69632` | `deployed_safe_local_target` | **BANKED (conditional on `M`)** |
| `M ≤ 19559298652205332 ⇒ #Bad ≤ B*` (exact deployed threshold) | `deployed_global_budget`, `deployed_threshold_arith` | **BANKED (conditional on `M`)** |

No circular congestion cap of the form `μ_R·C(R) ≤ M` is used anywhere: the only scalar hypothesis
is a uniform bound on the *per-coordinate charge load* `load(i) = Σ_{γ : i ∈ D_γ} C(class γ)`,
which is an explicit hypothesis of every theorem that uses it, and no separate load term is added
on top of `capturedCost(A)`.

## 4. Verdict

The requested return is **case 2: exactly one remaining inequality.**

Everything else is closed and banked: the global cost/potential definitions, the composition rule,
the exhaustive four-branch anchor split with derived (not assumed) charge widths, the disjoint
captured/uncaptured assignment with exact fibre multiplicities, the branch recurrences, the
independent branch-C and branch-D theorems, and the deployed arithmetic.

The single remaining inequality is **structural**:

> **(R1)** There is a uniform bound `M` on the per-coordinate charge load
> `load(i) ≤ M` for all `i ∉ S0`, with `M ≤ 19559298652205332` at the deployed point.

Equivalently, by `anchor_exists_concentrated_coordinate`, one must exclude the concentration
alternative: no single coordinate outside the anchor support may carry a `(w−s−a₀)/e` fraction of
the whole captured recursive cost (at the deployed point with a terminal anchor,
`69632/978944 = 1/14.06`). This is a spread statement about official supports, not a counting
statement, and it is **not** claimed here — it is the one open obligation, marked
**SOURCE_PRESENT_UNREPLAYED** nowhere and **REPORTED_NOT_REPLAYED** nowhere: it is simply *open*,
and appears as an explicit hypothesis in every theorem that consumes it.

## 5. Non-claims

* No unconditional bound on `#Bad` is claimed in the positive-mass branch.
* `#children × max child cost` is never used; no assumption that `e` drops by `w`.
* `d_X = max(0, w−s−a₀)` is not assumed; `w − s − a₀ ≤ |D_γ|` is proved from the official support
  definitions, and it is a *lower* bound on the charge width, not an identity.
* The number `19559298652274964` is arithmetic only and carries no congestion content.
* Nothing was reopened in Johnson bounds, sunflower arguments, quotient plumbing, FFT optimisation
  or M31 theory.
