# `EXACT_SUPPORT_TAIL_IMAGE` — fixed-codomain exact challenge representation

**Primary status returned: `EXACT_SUPPORT_TAIL_IMAGE`.**

The official bad set is exactly the image of the support challenge map in fixed tail coordinates.
In addition — and this is recorded separately, not instead — a *second* exact fixed-codomain
model (barycentric moments) is proved equivalent to it, and two structural theorems about the
image are proved (factorization through the fixed codomain, rank-one determinantal identity).

New modules (all additive; nothing earlier was modified; no `sorry`):

* `RequestProject/Root/CodingTheory/SupportTailChallenge.lean` — interpolation tails, the tail
  theorem, the official condition in tail coordinates, the support locus and challenge map, the
  exact image theorem, the commuting theorem with `gammaL`, fixed-codomain structure, explicit
  Lagrange coordinates, deployed row;
* `RequestProject/Root/CodingTheory/SupportTailMoments.lean` — barycentric moments, the
  top-coefficient functional, the kernel identity between the two models, the official condition
  and exact image theorem in moment coordinates, the explicit ratio formula;
* `RequestProject/SupportTailChallengeAxiomAudit.lean` — `#print axioms` for every user-facing
  declaration.

Reused as black boxes, **not** reproved: `MAXIMAL_ERASURE_NORMALIZATION`
(`isBad_iff_exists_exact_erasure`, `isBad_exact_window`, `challenge_unique`) and
`EXACT_CHALLENGE_IMAGE_THEOREM` (`candidateLocus`, `gammaL`, `gammaL_eq_of_isCloseOn`,
`mem_candidateLocus_iff`).

Throughout, `F` is an arbitrary field, `D : Finset F` an arbitrary domain, `t = |D| − e`,
`w = t − k`, and official badness is the project's own `Root.CodingTheory.IsBad`.

---

## 1. Exact support-side official equivalence

`isBad_iff_exists_support_tail` (hypotheses `k ≤ |D|`, `e < |D| − k`, `e < |D|`, `k + w = |D| − e`):

```
IsBad k e f₀ f₁ γ  ↔  ∃ S, |S| = |D| − e ∧ Tail_S(f₁) ≠ 0 ∧ Tail_S(f₀) + γ·Tail_S(f₁) = 0.
```

Both directions are checked against the official clauses (agreement window + noncontainment)
through the already proved exact-window normalization, with `S = Eᶜ`.  `γ = 0` is allowed; no
projective convention is used.

The nonzero clause is *proved*, not assumed, and isolated as

`lineCloseOn_of_tail_one_eq_zero` :  `Tail_S(f₁) = 0 ∧ Tail_S(f₀) + γ·Tail_S(f₁) = 0 →
Tail_S(f₀) = 0 ∧ LineCloseOn k S f₀ f₁`,

i.e. both coefficient words would be jointly explained on the same support, contradicting official
noncontainment.

## 2. Exact fixed-codomain representation

`interpOn S f = P_{f,S}` is Mathlib's `Lagrange.interpolate` on the nodes of `S`; degree `< |S|`
(`degree_interpOn_lt`), interpolating (`eval_interpOn`), unique (`interpOn_unique`,
`existsUnique_interpOn`) and linear in `f` (`interpOn_add`, `interpOn_smul` — it is literally the
application of Mathlib's linear map).

```lean
noncomputable def tail (k w : ℕ) (S : Finset ↥D) (f : ↥D → F) : Fin w → F      -- Tail_S(f) ∈ F^w
```

is defined as the application of a genuine linear map `tailLin k w S : (↥D → F) →ₗ[F] (Fin w → F)`,
so `tail_add`, `tail_smul` and `tail_lineComb` hold by construction.

**The load-bearing equivalence** (`tail_eq_zero_iff`, `k + w = |S|`):

```
Tail_S(f) = 0  ↔  IsCloseOn k S f      (f|_S explained by a polynomial of degree < k)
```

Both directions are proved: `←` by uniqueness of the interpolant, `→` by
`degree_lt_iff_coeff_zero` applied to `P_{f,S}` (degrees `≥ t` are killed by the interpolation
degree bound, degrees in `[k, t)` by the vanishing tail).  No dimension count is used.

Companion: `tail_pair_eq_zero_iff_lineCloseOn` — both tails vanish iff the *line* is close on `S`.

## 3. Exact challenge map

```lean
noncomputable def supportLocus (k w e) (f₀ f₁) : Set (Finset ↥D) :=
  {S | |S| = |D| − e ∧ T₁(S) ≠ 0 ∧ ∃ γ, T₀(S) + γ·T₁(S) = 0}
```

`exists_unique_gammaSupp` — existence and uniqueness of `γ_S` on the locus (uniqueness because
`T₁(S) ≠ 0` in the `F`-module `F^w`).  `gammaSupp` is an actual function `Finset ↥D → F` (junk
value `0` off the locus) with `gammaSupp_spec` and the functional uniqueness
`gammaSupp_eq_of_tail`.

## 4. Exact image equality

`exact_support_tail_challenge_image`:

```
{γ | IsBad k e f₀ f₁ γ}  =  γ_supp '' supportLocus.
```

Grand-MCA target: `ncard_badSet_le_of_ncard_image_gammaSupp_le` — `|im γ_supp| ≤ B*` implies
`|Γ(L)| ≤ B*`.  No counting of supports is substituted for it.

## 5. Relation to the erasure-side `gammaL`

An actual commuting theorem, not a cardinality coincidence:

* `compl_mem_candidateLocus` / `compl_mem_supportLocus` — `S ↦ Sᶜ` maps each locus into the other;
* `compl_bijOn_supportLocus` — it is a bijection `supportLocus ≃ candidateLocus`;
* **`gammaL_compl_eq_gammaSupp`** — `γ_L(Sᶜ) = γ_supp(S)` for every `S` in the support locus
  (`E = D \ S`);
* `image_gammaSupp_eq_image_gammaL` — hence the two exact images coincide.

## 6. Explicit coordinate formulas actually proved

* `tail_apply_eq_sum_basis` — `Tail_S(f)_a = ∑_{x∈S} f(x)·[X^{k+a}] ℓ_x`, `ℓ_x` the Lagrange basis;
* `tail_apply_eq_sum_nodal` (Route A) — with `Q_S = ∏_{x∈S}(X−x)` and `λ_x = 1/Q_S'(x)`
  (`nodalWeight`, cf. `nodalWeight_eq_inv_deriv`):

  ```
  Tail_S(f)_a = ∑_{x∈S} f(x)·λ_x·[X^{k+a}] ( Q_S(X)/(X−x) );
  ```

* `gammaSupp_eq_ratio_coord` — `γ_S = −T₀(S)_a / T₁(S)_a` for any coordinate with `T₁(S)_a ≠ 0`;
* `tail_top_eq_moment` — the top tail coordinate is the zeroth barycentric moment
  `∑_{x∈S} f(x)·λ_x`.

### Barycentric moments (optional §7 of the brief — carried out)

`moment S f b = ∑_{x∈S} f(x)·λ_x·x^b`, `moments w S f = (M_{S,b}(f))_{b<w} ∈ F^w`, linear in `f`.

* `coeff_top_interpOn` — `[X^{|S|−1}] P_{f,S} = ∑_{x∈S} f(x)·λ_x`;
* `sum_lam_eval_eq_coeff_top` — the top-coefficient functional: for `deg g < |S|`,
  `∑_{x∈S} g(x)·λ_x = [X^{|S|−1}] g`;
* **`moments_eq_zero_iff_tail_eq_zero`** — the two fixed-codomain models have the *same kernel*:
  `M_{S,·}(f) = 0 ↔ Tail_S(f) = 0`.  The nontrivial direction is a downward induction: once the
  top `b` coefficients of `P_{f,S}` are known to vanish, `deg(P·X^b) < |S|` and the `b`-th moment
  *is* the coefficient `[X^{|S|−1−b}] P_{f,S}`, which the moment therefore kills.  This is exactly
  the (uni)triangularity of the moment ↔ tail change of coordinates, in kernel form; the
  triangular matrix itself is not needed anywhere;
* `moments_eq_zero_iff`, `isBad_iff_exists_support_moment`, `momentLocus_eq_supportLocus`,
  `gammaMom`, `gammaMom_eq_gammaSupp`, `exact_support_moment_challenge_image`,
  `image_gammaMom_eq_image_gammaSupp` — the whole chain again in moment coordinates, with the
  *same* locus and the *same* challenge values;
* `gammaMom_eq_ratio_moment`, `exists_moment_ratio` — the challenge is *always* an explicit ratio
  of two weighted power sums:  `γ_S = − M_{S,b}(f₀) / M_{S,b}(f₁)` for some `b < w`.

No Newton identity, symmetric function, Toeplitz/Hankel, convolution, CRT/Fourier or cyclic
structure is assumed or claimed anywhere; none was needed.

## 7. Stronger image/fibre theorems actually proved

* **Fixed codomain** (`tailPair`, `tailPair_codomain`) — all pairs `(T₀(S), T₁(S))` live in the
  same `F^w × F^w`, independently of `S`.  This is the structural output of the mission.
* **Factorization through the fixed codomain** (`gammaSupp_eq_of_tailPair_eq`) — `γ_S` depends
  *only* on the point `(T₀(S), T₁(S)) ∈ F^w × F^w`; two supports with equal tail pairs have equal
  challenges.  Consequence (`ncard_image_gammaSupp_le_ncard_image_tailPair`):

  ```
  |im γ_supp| ≤ |{ (T₀(S), T₁(S)) : S ∈ S_L }|,
  ```

  a bound *inside the fixed codomain*, not a count of supports.
* **Rank-one/determinantal identity** (`tail_zero_eq_neg_smul`, `tailPair_rank_one`) — on the
  locus `T₀(S) = −γ_S·T₁(S)`, hence every `2×2` minor vanishes:
  `T₀(S)_a·T₁(S)_b = T₀(S)_b·T₁(S)_a`.  The image of the pair map therefore lies in the
  determinantal rank-one locus of `F^{2×w}`; this identity is *derived*, not assumed.

No numerical bound on `|im γ_supp|` is claimed: no heuristic counting was used, and no exact
consequence of this mission produced one.

## 8. Deployed row

`deployed_support_tail_image` and `deployed_support_moment_image`: for `|D| = 2097152`,
`k = 1048576`, `e = 978944`,

```
t = |D| − e = 1118208,      w = t − k = 69632,
```

and the exact image theorem holds in both coordinate systems with these parameters.

## 9. `lake build`

```
lake build RequestProject.Root.CodingTheory.SupportTailChallenge
lake build RequestProject.Root.CodingTheory.SupportTailMoments
lake build RequestProject.SupportTailChallengeAxiomAudit
```

all succeed, with no warnings and no `sorry`.

## 10. `#print axioms`

Every declaration listed in `RequestProject/SupportTailChallengeAxiomAudit.lean` prints exactly

```
[propext, Classical.choice, Quot.sound]
```
