# PIVOT FILTRATION AND RESIDUAL-DESCENT AUDIT

**Status returned: `PIVOT_DESCENT_OBSTRUCTION`.**

Phases A–E produced genuine extra structure (an exact nested filtration, an exact first-layer
projective theorem, a valid successive-quotient formulation, an exact cross-pivot compatibility
theorem, and the exact triangular relation to the moments).  Phase F was therefore run, and it
terminated with a **precise obstruction**: the residual object exists, the map exists, the
challenge is preserved and the width strictly decreases, but the *official witness semantics* is
not preserved — the residual instance is the Reed–Solomon problem of dimension `k + a`, i.e. the
depth `a` bought in width is paid for exactly in dimension.  By the stop rule the run stops here;
no global recurrence and no numerical bound is claimed.

New files (all additive, all `sorry`-free):

* `RequestProject/Root/CodingTheory/PivotFiltration.lean` — Phases A–D
* `RequestProject/Root/CodingTheory/PivotResidual.lean` — Phases E–F
* `RequestProject/PivotFiltrationAxiomAudit.lean` — `#print axioms`

`PivotCore.lean`, `SupportTailChallenge.lean`, `SupportTailMoments.lean`, `SupportTailPivot.lean`
were used as black boxes and are unmodified.

---

## 1. Exact definition of `F_ge(a)`

Abstractly (`Root.CodingTheory.PivotCore`):

```lean
def geFiltration (c : V → ℕ → F) (L : Set V) (a : ℕ) : Set V :=
  {S | S ∈ L ∧ ∀ b < a, c S b = 0}
```

Concretely, with the deployed tail coordinates:

```lean
noncomputable def tailFge (k w e : ℕ) (f₀ f₁ : ↥D → F) (a : ℕ) : Set (Finset ↥D) :=
  PivotCore.geFiltration (tailFam k w f₁) (supportLocus k w e f₀ f₁) a
-- mem_tailFge : S ∈ tailFge k w e f₀ f₁ a ↔
--   S ∈ supportLocus k w e f₀ f₁ ∧ ∀ b < a, tailCoord k w S f₁ b = 0
```

## 2. Nestedness and successive difference (Phase A)

| Claim | Theorem |
|---|---|
| `F_ge(0) = supportLocus` | `tailFge_zero` |
| `F_ge(a+1) ⊆ F_ge(a)`, and `a ≤ b → F_ge(b) ⊆ F_ge(a)` | `tailFge_succ_subset`, `tailFge_antitone` |
| `S ∈ F_ge(a) ↔ a ≤ pivot(S)` | `mem_tailFge_iff_le_pivot` |
| `L_a = F_ge(a) \ F_ge(a+1)` | `pivotStratum_eq_sdiff` |
| `F_ge(w) = ∅` | `tailFge_width_eq_empty` |
| locus = disjoint union of the `L_a` | `supportLocus_eq_disjoint_iUnion` |
| on `F_ge(a)` also `T₀(S)_b = 0` for `b < a` | `tailFge_tail_zero_prefix`, `tailFge_prefix_eq_zero` |

The `T₀` prefix vanishing is **derived**, not assumed: it comes from the already proved exact
relation `T₀(S)_b + γ_S·T₁(S)_b = 0` (`supportLocus_rel`) together with `T₁(S)_b = 0`; outside the
window the coordinate is `0` by definition of `tailCoord`.  The abstract step is
`PivotCore.geFiltration_other_prefix_eq_zero`.

So the pivot is a **genuine nested filtration**, not merely a labelling of coordinates.

## 3. First-nonzero-layer projective theorem (Phase B)

`first_nonzero_layer`: for `S ∈ L_a`,

* `a < w`;
* `T₁(S)_a ≠ 0`;
* `∀ b < a, T₀(S)_b = 0 ∧ T₁(S)_b = 0`;
* `(T₀(S)_a, T₁(S)_a) = T₁(S)_a · (−γ_S, 1)`, i.e. `[T₀(S)_a : T₁(S)_a] = [−γ_S : 1]`;
* `γ_S = −T₀(S)_a / T₁(S)_a`.

`first_nonzero_layer_proportional` states the same as: there is `μ ≠ 0` with
`(T₀(S)_a, T₁(S)_a) = μ·(−γ_S, 1)`.

The challenge is therefore the affine projective direction of the first nonzero tail layer.  This
is deliberately **not** called intrinsic: the coordinate filtration has not been shown invariant
under changes of representation, and Phase E shows that a different natural coordinate system (the
barycentric moments) produces a *different* pivot.

## 4. Successive-quotient formulation (Phase C) — valid

The tail codomain `F^w = (Fin w → F)` does support the construction.

```lean
def prefixSub (F) (w a : ℕ) : Submodule F (Fin w → F) :=
  {v | ∀ b : Fin w, (b : ℕ) < a → v b = 0}
```

* `prefixSub w 0 = ⊤`, `prefixSub w w = ⊥`, `prefixSub w (a+1) ≤ prefixSub w a`
  (`prefixSub_zero`, `prefixSub_width`, `prefixSub_succ_le`, `prefixSub_antitone`);
* `prefixSub w (a+1) = prefixSub w a ⊓ ker(layerProj a)` (`prefixSub_succ_eq_inf_ker`);
* the `a`-th successive quotient **is** the `a`-th coordinate:

```lean
noncomputable def layerQuotEquiv (F) (a : ℕ) (h : a < w) :
    (prefixSub F w a ⧸ (prefixSub F w (a+1)).comap (prefixSub F w a).subtype) ≃ₗ[F] F
```

* `mem_tailFge_iff_mem_prefixSub` identifies `F_ge(a)` with `T₁(S) ∈ G_a`;
* the exact equivalence (`pivot_eq_iff_layer`): for `S` in the locus and `a < w`,

  `pivot(S) = a` **iff** `T₀(S), T₁(S) ∈ G_a` (vanishing in all earlier quotients),
  the image of `T₁(S)` in the `a`-th quotient is nonzero, and the image of the pair is rank one
  with `layer_a T₀(S) = layer_a T₁(S)·(−γ_S)`.

## 5. Interpolation interpretation (Phase E.1)

`prefix_eq_zero_iff_coeff_window` (and `tailFge_coeff_window` on the locus): for `a ≤ w`,

```
(∀ b < a, T(S)_b = 0)  ↔  ∀ i, k ≤ i < k + a → coeff_i P_{f,S} = 0.
```

The interpolant loses exactly the coefficient window `[k, k+a)`.  The coefficients of degree `< k`
are untouched, so this is a codimension-`a` linear condition *inside* the tail window and **not** a
degree bound; it is not the support locus of a shorter Reed–Solomon problem with the same
dimension.

## 6. Moment interpretation (Phase E.2–E.3) — exact triangular relation, and a mismatch

With `λ_m = Σ_{x∈S} x^m·λ_x` (`lamPow`) one has `λ_m = 0` for `m < |S|−1` and `λ_{|S|−1} = 1`
(`lamPow_of_lt`).  Then, for `k + w = |S|` and `b < w`:

* `moment_eq_sum_tailCoord`: `M_{S,b}(f) = Σ_{j<w} T(S)_j·λ_{k+j+b}`;
* `moment_eq_tailCoord_add_higher`:
  `M_{S,b}(f) = T(S)_{w−1−b} + Σ_{j ≥ w−b} T(S)_j·λ_{k+j+b}`;
* `tailCoord_eq_moment_sub` (the exact triangular inversion):
  `T(S)_{w−1−b} = M_{S,b}(f) − Σ_{j ≥ w−b} T(S)_j·λ_{k+j+b}`.

So the change of coordinates tail → moments is **unitriangular in the reversed order**.
Consequently:

* `momentPivot_eq_of_top` / `momentPivot_eq_sub_tailTop`: the moment pivot is `w − 1 − d`, where
  `d = tailTop` is the **largest** index with `T₁(S)_d ≠ 0`;
* `momentPivot_eq_pivot_iff`: the moment pivot equals the tail pivot **iff**
  `pivot(S) + tailTop(S) = w − 1`.

Therefore the tail pivot must **not** be identified with the moment pivot: they are different
invariants of the same tail object (only the challenge *value* is common, as already known from
`rho_pivot_eq_rhoMom_momentPivot`).  In particular the prefix filtration `F_ge(a)` does not
transport to the moment prefix filtration; in moment coordinates the tail prefix condition is the
triangular relation above, not the vanishing of a moment prefix.

## 7. Cross-pivot compatibility (Phase D) — proved, plus two explicit non-consequences

1. `pivotStratum_subset_tailFge`: `a ≤ b → L_b ⊆ F_ge(a)`. **Proved.**
2. `pivotStratum_prefix_eq_zero`: the equations defining `F_ge(a)` are inherited by every deeper
   stratum, for both `T₀` and `T₁`. **Proved.**
3. `rho_eq_gammaSupp_of_coord_ne_zero`: for *any* coordinate `a < w` with `T₁(S)_a ≠ 0`,
   `ρ_a(S) = γ_S`.  The level-`b` challenge datum is thus a deeper coordinate of the *same* tail
   object, and the pivot coordinate is only the first coordinate where the ratio is defined.
   **Proved.**
4. `rho_eq_rho_iff_gammaSupp_eq`: for `S ∈ L_a`, `S' ∈ L_b`, `ρ_a(S) = ρ_b(S') ↔ γ_S = γ_{S'}`.
   That is the exact compatibility available across strata. **Proved.**

Two things explicitly *not* obtained, and one of them refuted:

* `deeper_stratum_layer_a_zero`: for `a < b` and `S ∈ L_b`, the level-`a` layer of the pair is
  identically zero and `ρ_a(S) = 0`.  A deeper support carries **no** additional level-`a`
  equation content; nestedness alone yields no numerical gain.
* Disjointness of the strata images is **false in general**:
  `Root.CodingTheory.PivotFiltrationExample.images_not_disjoint` exhibits a concrete instance of
  the abstract pivot theory (two points, `w = 2`, over `ℚ`) with two nonempty strata whose ratio
  images are *equal*.  So the union in `image(γ) = ⋃_{a<w} image(ρ_a | L_a)` may not be replaced by
  a maximum on formal grounds, and no bound was inferred from nestedness.

## 8. Residual descent (Phase F) — constructed, then obstructed

What *does* hold:

1. **Residual object** (`residual_tailCoord`):
   `tailCoord (k+a) (w−a) S f j = tailCoord k w S f (a+j)` — the residual tail is literally the
   deeper part of the same tail, i.e. the Reed–Solomon instance with parameters `(k+a, w−a)`.
2. **Map** (`tailFge_subset_residual_supportLocus`):
   `F_ge(a) ⊆ supportLocus (k+a) (w−a) e f₀ f₁`, with the same erasure budget `e`; the residual
   rank-one relation is `residual_rel`, the nonvanishing is `residual_tail_one_ne_zero`.
3. **Challenge preservation** (`gammaSupp_residual_eq`):
   `γ^{(k+a, w−a)}(S) = γ^{(k,w)}(S)` on `F_ge(a)`; moreover `residual_pivot_eq_zero`: on `L_a`
   the residual pivot is `0`, so the descent normalises the pivot away.
5. **Strict decrease** (`residual_width_lt`): `0 < a → w − a < w`.

What **fails** — item 4, preservation of the official witness semantics:

* `residual_tail_eq_zero_iff_isCloseOn`: `tail (k+a) (w−a) S f = 0 ↔ IsCloseOn (k+a) S f`.
  The residual witness predicate is closeness to the code of degree `< k + a`.
* `isCloseOn_mono` / `isCloseOn_strict_mono`: that code contains the original one and is
  **strictly** larger whenever `0 < a` and `k < |S|` (witness: `x ↦ x^k`).
* `residual_descent_semantics_obstruction` packages the failure, together with the bookkeeping
  identity `(k+a) + (w−a) = k + w`: the descent keeps the total window and the erasure budget
  fixed and trades width for dimension one-for-one.
* `image_rho_subset_residual_image`: `ρ_a '' L_a ⊆ γ^{(k+a,w−a)} '' supportLocus (k+a) (w−a) e`.
  The stratum image is contained in the bad set of a *weaker* (higher-dimension, same-erasure)
  instance, so the containment gives no contraction: the residual problem is at least as hard as
  the original one.

Conclusion: prefix vanishing is a real filtration but it is **not** a challenge-preserving residual
descent in the required sense.  Pivot depth has no residual meaning beyond re-indexing the same
instance at a larger dimension.

## 9. Build status

```
lake build RequestProject.Root.CodingTheory.PivotFiltration
lake build RequestProject.Root.CodingTheory.PivotResidual
lake build RequestProject.PivotFiltrationAxiomAudit
```

all succeed with no errors, no warnings and no `sorry`.

## 10. `#print axioms`

Every one of the 76 audited declarations prints

```
[propext, Classical.choice, Quot.sound]
```

(the purely arithmetic `residual_width_lt` prints `[propext, Quot.sound]`).  No other axiom is used.

## Not claimed

No quantitative bound `|Bad| ≤ B*` was derived; the Grand-MCA numerical gate is untouched by this
task, and nothing here should be read as progress on it.
