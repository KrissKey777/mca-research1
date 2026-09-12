# `EXACT_CHALLENGE_IMAGE_THEOREM`

Status returned: **`EXACT_CHALLENGE_IMAGE_THEOREM`** (with the optional coefficient bridge and the
rational challenge formula also obtained — see §7 below).

New module: `RequestProject/Root/CodingTheory/ExactChallengeImage.lean`
Axiom audit: `RequestProject/ExactChallengeImageAxiomAudit.lean`
All changes are additive; no earlier file was modified; nothing uses `sorry`.

---

## 1. Exact source types (frozen before anything new was defined)

All from `RequestProject/Root/CodingTheory/{MCA,ProximityGapLines,ErasureSpanPolynomial,
MaximalErasureNormalization}.lean`, with `F` a field, `D : Finset F`, `k e : ℕ`:

| object | source-native type |
|---|---|
| `s₀, s₁` | `f₀ f₁ : ↥D → F` (word-space vectors; the line is `lineComb f₀ f₁ γ = fun x => f₀ x + γ * f₁ x`) |
| `V_E` | `vSpace (k : ℕ) (E : Finset ↥D) : Submodule F (↥D → F)` = `reedSolomonCode F D k ⊔ positionSpace F E` |
| `W_E` | `wSpace k E : Submodule F (↥D → F)` = `dualCode (vSpace k E)` |
| `Ψ` | `psi (D : Finset F) : F[X] →ₗ[F] (↥D → F)`, `psi D p a = lam D a * p.eval a` |
| `wModel` | `wModel k E = Submodule.map (psi D) (qModule (dval D) E (D.card - k - E.card))` |
| `Λ` | `lambdaMap (f₀ f₁ : ↥D → F) : (↥D → F) →ₗ[F] F × F`, `y ↦ (∑ a, f₀ a * y a, ∑ a, f₁ a * y a)` |
| `lamRestrict` | `lamRestrict k E f₀ f₁ : ↥(wSpace k E) →ₗ[F] F × F` = `(lambdaMap f₀ f₁).comp (wSpace k E).subtype` |
| `range_lamRestrict` | `LinearMap.range (lamRestrict k E f₀ f₁) = lamImage k E f₀ f₁` |
| `isBad_exact_window` | `IsBad k e f₀ f₁ γ → ∃ S, S.card = D.card - e ∧ IsCloseOn k S (lineComb f₀ f₁ γ) ∧ ¬ LineCloseOn k S f₀ f₁` |
| `isBad_of_exact_window` | same window, packaged with `D.card ≤ S.card + e` and `IsBad` |
| `isBad_iff_exists_exact_erasure` | `IsBad k e f₀ f₁ γ ↔ ∃ E', E'.card = e ∧ IsCloseOn k E'ᶜ (lineComb f₀ f₁ γ) ∧ ¬ LineCloseOn k E'ᶜ f₀ f₁` |
| `challenge_unique` | two agreeing challenges on the same `E` with noncontainment are equal |

Note the two sanity points the brief asked for: `s₀, s₁` are **word-space vectors** (`↥D → F`), not
syndromes in a separate space, and `Λ` is the *ambient* pairing map on `↥D → F` — so no formula of
the shape `⟨s_i, Ψ(Q_E h)⟩` was assumed; it was *derived* (see §7) by composing the existing maps.

## 2. Candidate locus

```lean
noncomputable def candidateLocus (k e : ℕ) (f₀ f₁ : ↥D → F) : Set (Finset ↥D) :=
  {E | E.card = e ∧ f₁ ∉ vSpace k E ∧ f₀ ∈ vSpace k E ⊔ Submodule.span F {f₁}}
```

`mem_candidateLocus_iff` proves it equivalent to the source-native pair

```
E.card = e ∧ (∃ γ, IsCloseOn k Eᶜ (lineComb f₀ f₁ γ)) ∧ ¬ LineCloseOn k Eᶜ f₀ f₁,
```

so the locus is *not* identified with official badness by definition.

## 3. Unique challenge map

* `exists_unique_challenge` — for `E ∈ candidateLocus` there is exactly one `γ_E` with
  `lineComb f₀ f₁ γ_E ∈ vSpace k E`. Existence from `s₀ ∈ V_E + F·s₁`; uniqueness is the existing
  `challenge_unique` (not reproved), which needs `s₁ ∉ V_E`. `γ_E = 0` is allowed.
* `gammaL k f₀ f₁ : Finset ↥D → F` is an actual function (junk value `0` off the locus), with
  `gammaL_spec`, `gammaL_mem_vSpace`, and the functional uniqueness `gammaL_eq_of_isCloseOn`.

## 4. Both inclusions

* `badSet_subset_image_gammaL` — forward, via `isBad_iff_exists_exact_erasure` (normalization).
* `image_gammaL_subset_badSet` — reverse: for `E` in the locus, `s₀ + γ_E s₁ ∈ V_E` and
  `L ⊄ V_E` (from `s₁ ∉ V_E`), composed with the same exact-window bridge. Official
  agreement/noncontainment were **not** reconstructed by hand.

## 5. Image equality

```lean
theorem exact_challenge_image (hk : k ≤ D.card) (he : e < D.card - k) (heD : e < D.card) :
    {γ : F | IsBad k e f₀ f₁ γ} = gammaL k f₀ f₁ '' candidateLocus k e f₀ f₁
```

Cardinality consequence (`ncard_badSet_le_ncard_candidateLocus`):

```
|Γ(L)| = |im γ_L| ≤ |E_L|,
```

with `ncard_badSet_le_of_ncard_image_le` (the exact Grand-MCA target `|im γ_L| ≤ B*`) and
`ncard_badSet_le_of_ncard_candidateLocus_le` (the stronger sufficient route `|E_L| ≤ B*`) recorded
separately; different exact-size erasure sets may map to the same challenge. Over a finite field
the official finset version is `card_badSet_le_ncard_candidateLocus`.

## 6. Exact `Λ` representation

`range_lamRestrict_eq_span_gammaL`:

```
LinearMap.range (lamRestrict k E f₀ f₁) = Submodule.span F {(-(gammaL k f₀ f₁ E), 1)}
```

for `E` in the locus (via the existing `lamImage_eq_span` and `range_lamRestrict`), in the
project's own sign/order convention `(-γ, 1)`. Labels determine challenges
(`gammaL_eq_of_lamImage_eq`).

## 7. Coefficient bridge and challenge formula

`lamTilde f₀ f₁ E := (lambdaMap f₀ f₁) ∘ (psi D) ∘ (LinearMap.mulLeft F (qPoly (dval D) E))`,
i.e. `Λ` pulled back along the proved model `W_E = Ψ(Q_E · F[X]_{<w})`; `map_lamTilde_degreeLT`
shows `Λ̃_E (F[X]_{<w}) = Λ(W_E)` with `w = |D| − k − |E|`. Its two coordinates are honest linear
functionals `lamTilde₀, lamTilde₁ : F[X] →ₗ[F] F` and expand on monomials as

```
lamTilde_i (X^a) = ∑_{j<|E|+1} q_j(E) · ∑_{x ∈ D} f_i x · (λ_x · x^{j+a}),   q_j(E) = (Q_E).coeff j.
```

Consequences: `gammaL_eq_ratio` — for any `g` in the model width with `lamTilde₁ g ≠ 0`,

```
γ_E = − lamTilde₀ (g) / lamTilde₁ (g),
```

`ratio_indep_of_choice` (independence of the chosen `g`), and `exists_model_witness` (such a `g`
always exists on the locus, realising `(−γ_E, 1)` exactly).

## 8. Deployed row

`deployed_exact_challenge_image`: for `r = |D| − k = 1048576` and `e = 978944` (hence dual width
`w = r − e = 69632`), the image equality and `|Γ(L)| ≤ |E_L|` hold.

## 9. Build

`lake build RequestProject.Root.CodingTheory.ExactChallengeImage` and
`lake build RequestProject.ExactChallengeImageAxiomAudit` both succeed with no warnings and no
`sorry`.

## 10. `#print axioms`

Every declaration listed in the audit file prints exactly
`[propext, Classical.choice, Quot.sound]`.

## Not done (explicitly out of scope per the brief)

No counting of erasure sets, no Plücker minors, no Fourier/CRT decomposition of `W_E`, no
Newton/power-sum parametrization, no Toeplitz/Hankel structure, and no claim about the fibres of
`E ↦ γ_E`.
