# `PIVOT_STRATIFIED_CHALLENGE_IMAGE` — the canonical pivot theory of the challenge image

**Primary status returned: `PIVOT_STRATIFIED_CHALLENGE_IMAGE`.**

Continuation of `SupportTailChallenge.lean`, `SupportTailMoments.lean` and
`EXACT_SUPPORT_TAIL_IMAGE`, all used as black boxes.  Nothing earlier is modified, nothing earlier
is replayed, and none of the excluded topics (maximal-erasure normalization, quotient plumbing, raw
support counting, `rsList`, Johnson/list-size, sunflower, cross-challenge replacement,
Fourier/CRT/Newton, generic probability) is reopened.

New modules (additive, `sorry`-free):

* `RequestProject/Root/CodingTheory/PivotCore.lean` — the model-independent pivot machinery;
* `RequestProject/Root/CodingTheory/SupportTailPivot.lean` — Phases A–D in the tail model and the
  transport to the moment model;
* `RequestProject/SupportTailPivotAxiomAudit.lean` — `#print axioms` for every user-facing
  declaration.

Throughout, `F` is an arbitrary field, `D : Finset F`, `T₀(S) = tail k w S f₀`,
`T₁(S) = tail k w S f₁ : Fin w → F`, and the deployed row is `|D| = 2097152`, `k = 1048576`,
`e = 978944`, `w = 69632`.

---

## 1. Exact Lean definition of `pivot`

Tail coordinates are first repackaged with a natural-number index (junk value `0` outside the
window), so that pivots, strata and ratios can all be indexed uniformly:

```lean
noncomputable def tailCoord (k w : ℕ) (S : Finset ↥D) (f : ↥D → F) (a : ℕ) : F :=
  if h : a < w then tail k w S f ⟨a, h⟩ else 0

noncomputable def tailFam (k w : ℕ) (f : ↥D → F) : Finset ↥D → ℕ → F :=
  fun S a => tailCoord k w S f a
```

The abstract core (`PivotCore`) is

```lean
def pivotSet (w : ℕ) (c : V → ℕ → F) (S : V) : Set ℕ := {a | a < w ∧ c S a ≠ 0}
noncomputable def pivot (w : ℕ) (c : V → ℕ → F) (S : V) : ℕ := sInf (pivotSet w c S)
```

and the concrete pivot is

```lean
noncomputable def pivot (k w : ℕ) (f₁ : ↥D → F) (S : Finset ↥D) : ℕ :=
  Root.CodingTheory.PivotCore.pivot w (tailFam k w f₁) S
```

i.e. `pivot(S) = min {a < w : T₁(S)_a ≠ 0}`.  No coordinate is chosen noncanonically: this is a
minimum, not a choice.  Its identification with the *finite* ordering on `Fin w` is proved:

```lean
theorem pivot_eq_min' (hS : S ∈ supportLocus k w e f₀ f₁) (hne : … .Nonempty) :
    pivot k w f₁ S = ((Finset.univ.filter fun a : Fin w => tail k w S f₁ a ≠ 0).min' hne : Fin w)
```

## 2. Existence proof

`pivotSet_nonempty_of_mem_supportLocus` : on `supportLocus` the index set is nonempty (from
`T₁(S) ≠ 0` via `tail_ne_zero_iff_tailCoord`).  Hence

* `pivot_lt_width` : `pivot(S) < w`;
* `tailCoord_pivot_ne_zero` : `T₁(S)_{pivot(S)} ≠ 0`;
* `tailCoord_eq_zero_of_lt_pivot` : `T₁(S)_b = 0` for every `b < pivot(S)`;
* `pivot_eq_of`, `pivot_eq_iff` : the pivot is the *unique* index with these two properties.

## 3. Partition / disjointness theorem

```lean
noncomputable def pivotStratum (k w e : ℕ) (f₀ f₁ : ↥D → F) (a : ℕ) : Set (Finset ↥D)
```

* `pivotStratum_disjoint`, `pivotStratum_pairwise_disjoint` : `a ≠ b → Disjoint L_a L_b`;
* `pivotStratum_eq_empty_of_le` : `w ≤ a → L_a = ∅`;
* `iUnion_pivotStratum` : `⋃_{a : ℕ} L_a = supportLocus`;
* **`biUnion_pivotStratum`** : `⋃_{a < w} L_a = supportLocus`.

Membership is fully explicit (`mem_pivotStratum_iff`): `S ∈ L_a` iff `S ∈ supportLocus`, `a < w`,
`T₁(S)_a ≠ 0` and `T₁(S)_b = 0` for all `b < a`; the `Fin w` forms are
`tail_pivot_ne_zero_of_mem_stratum` and `tail_eq_zero_of_lt_pivot_of_mem_stratum`.

## 4. Fixed-coordinate ratio theorem

```lean
theorem gammaSupp_eq_pivot_ratio (hS : S ∈ pivotStratum k w e f₀ f₁ a) :
    gammaSupp k w f₀ f₁ S = -(tailCoord k w S f₀ a / tailCoord k w S f₁ a)
```

and, at the level of interpolants, `gammaSupp_eq_coeff_ratio`:
`γ_S = −[X^{k+a}]P_{f₀,S} / [X^{k+a}]P_{f₁,S}`.  After this theorem the coordinate is *the* pivot
of the stratum; no "for some coordinate" phrasing is used anywhere below it.

## 5. Exact image-union theorem

With `rho k w f₀ f₁ a S = −T₀(S)_a / T₁(S)_a`:

* `image_gammaSupp_eq_biUnion` : `image(γ_supp) = ⋃_{a<w} image(rho_a | L_a)`;
* `badSet_eq_biUnion_image_rho` : the same for the official bad set;
* `ncard_image_gammaSupp_le_sum`, `badSet_ncard_le_sum_ncard_image_rho` :
  `|Bad| ≤ Σ_{a<w} |image(rho_a | L_a)|`;
* `deployed_pivot_stratified_image` : both statements for the deployed row (`w = 69632`).

The official-vs-image relation used is the *equality* already available from the current source
(`exact_support_tail_challenge_image`); no unproved semantic converse is assumed, and no
support-count bound is used as a substitute for an image bound.

## 6. Fibre characterization

```lean
noncomputable def pivotFibre (k w e : ℕ) (f₀ f₁ : ↥D → F) (a : ℕ) (γ : F) : Set (Finset ↥D)
```

* `mem_pivotFibre_iff` : `S ∈ fibre a γ ↔ S ∈ L_a ∧ rho_a(S) = γ`;
* **`mem_pivotFibre_iff_explicit`** : `S ∈ fibre a γ` iff `S ∈ supportLocus`, `a < w`,
  `T₁(S)_a ≠ 0`, `T₁(S)_b = 0` for `b < a`, and `T₀(S)_a + γ·T₁(S)_a = 0`;
* `mem_image_rho_iff` : `γ ∈ image(rho_a | L_a)` iff the fibre is nonempty;
* `gammaSupp_eq_of_mem_pivotFibre`, `pivotFibre_eq_stratum_inter` : the fibre is exactly the part
  of `L_a` where the official challenge equals `γ`;
* `mem_pivotFibre_iff_lineComb` : the fibre equation is the vanishing of one tail coordinate of
  `f₀ + γ·f₁`.

Fibres are *not* identified with supports anywhere: they remain sets of supports cut out by the
listed equations.

## 7. Moment transport status

Transport, not duplication: both models are instances of the same `PivotCore` theory.

* `momentPivot`, `momentStratum`, `rhoMom`, `momentFibre` with
  `mem_momentStratum_iff`, `momentStratum_disjoint`, `biUnion_momentStratum`,
  `gammaMom_eq_momentPivot_ratio`, `image_gammaMom_eq_biUnion`, `ncard_image_gammaMom_le_sum`,
  `mem_momentFibre_iff`, `mem_momentFibre_iff_explicit`;
* **challenge compatibility** `rho_pivot_eq_rhoMom_momentPivot` : on the common locus the
  tail-pivot ratio and the moment-pivot ratio produce the *same* scalar (the official challenge),
  through the already proved `momentLocus_eq_supportLocus` and `gammaMom_eq_gammaSupp`;
* `badSet_eq_biUnion_image_rhoMom`, `badSet_ncard_le_sum_ncard_image_rhoMom`,
  `momentStratum_subset_supportLocus`.

Note the honest caveat: the tail pivot and the moment pivot are computed in different coordinate
systems and are in general *different indices*; what is proved equal are the challenge values and
the resulting image decompositions.  No triangular change-of-coordinates beyond the already proved
kernel identity is used or claimed.

## 8. Phase D — exact structural information (no numerical closure)

* **Rank-one relation in coordinates** `tailCoord_zero_eq_neg_rho_mul` : on `L_a`,
  `T₀(S)_b = −rho_a(S)·T₁(S)_b` for every `b < w`; the pair is determined by `T₁(S)` and one
  scalar;
* **Induced vanishing prefix for `T₀`** `tailCoord_zero_eq_zero_of_lt_pivot`;
* **Determinantal identity** `tailCoord_det_eq_zero` : all `2×2` minors of `(T₀(S); T₁(S))`
  vanish (ℕ-coordinate form of `tailPair_rank_one`);
* **Compatibility between tail coordinates** `tailCoord_ratio_indep` : the ratio is the same at
  every coordinate where `T₁(S)` is nonzero;
* **Polynomial form of the prefix** `coeff_interpOn_eq_zero_of_lt_pivot`,
  `coeff_interpOn_pivot_ne_zero` : on `L_a` both interpolants have no coefficient in the degree
  range `[k, k+a)`, and `[X^{k+a}]P_{f₁,S} ≠ 0`;
* **One scalar equation controls the whole support** `mem_pivotFibre_iff_isCloseOn` : for
  `S ∈ L_a` the single pivot equation `T₀(S)_a + γ·T₁(S)_a = 0` is *equivalent* to the full
  official closeness of `f₀ + γ·f₁` on `S`; the other `w − 1` tail equations are automatic;
* **Projective/fibre compression** `rho_eq_of_proportional`, `PivotCore.ratio_eq_of_proportional` :
  the ratio only sees the pivot pair up to a common nonzero scalar.

No numerical bound is invented, and none of these restrictions is claimed to imply `|Bad| ≤ B*`.

## 9. Reusable declarations for the next agent

| role | declaration |
|---|---|
| ℕ-indexed tail coordinate | `tailCoord`, `tailCoord_eq_coeff`, `tailCoord_lineComb` |
| pivot | `pivot`, `pivot_lt_width`, `tailCoord_pivot_ne_zero`, `pivot_eq_iff`, `pivot_eq_min'` |
| pivot stratum | `pivotStratum`, `mem_pivotStratum_iff`, `biUnion_pivotStratum` |
| scalar ratio map | `rho`, `rho_apply`, `gammaSupp_eq_pivot_ratio`, `gammaSupp_eq_coeff_ratio` |
| image decomposition | `image_gammaSupp_eq_biUnion`, `badSet_eq_biUnion_image_rho`, `badSet_ncard_le_sum_ncard_image_rho` |
| fibre predicate | `pivotFibre`, `mem_pivotFibre_iff`, `mem_pivotFibre_iff_explicit`, `mem_image_rho_iff`, `mem_pivotFibre_iff_isCloseOn` |
| tail/moment equivalence | `momentPivot`, `momentStratum`, `rhoMom`, `image_gammaMom_eq_biUnion`, `badSet_eq_biUnion_image_rhoMom` |
| challenge compatibility | `rho_pivot_eq_rhoMom_momentPivot`, `momentStratum_subset_supportLocus` |
| abstract reuse | the whole `Root.CodingTheory.PivotCore` namespace (any second pair of coordinate families can be plugged in) |

## 10. `lake build`

```
lake build RequestProject.Root.CodingTheory.PivotCore
lake build RequestProject.Root.CodingTheory.SupportTailPivot
lake build RequestProject.SupportTailPivotAxiomAudit
```

all succeed, with no warnings, no errors and no `sorry`.

## 11. `#print axioms`

Every declaration listed in `RequestProject/SupportTailPivotAxiomAudit.lean` prints exactly

```
[propext, Classical.choice, Quot.sound]
```

(the purely definitional `PivotCore.ratio` prints `[propext, Quot.sound]`).

---

## The remaining mathematical gate

For each `a < w` (deployed: `a < 69632`) the remaining problem is *entirely scalar*:

> **bound `|image(rho_a | L_a)|`** — i.e. bound the number of distinct values
> `−T₀(S)_a / T₁(S)_a` taken by supports `S` whose pivot is exactly `a` — **or exhibit a
> structural obstruction / counterexample showing that no useful bound holds coordinatewise.**

Equivalently, for each `a` and each `γ`, decide when the fibre
`{S ∈ supportLocus : T₁(S)_a ≠ 0, T₁(S)_b = 0 (b < a), T₀(S)_a + γ·T₁(S)_a = 0}` is nonempty.

This theory does **not** close the Grand MCA theorem, and the pivot theory being complete must not
be read as such.  Nothing above assumes a globally fixed pivot coordinate, injectivity of
`S ↦ γ_supp(S)`, that support counts bound challenge counts, that large fibres are impossible, or
any generic-subspace probability.
