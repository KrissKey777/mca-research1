# MAXIMAL-ERASURE NORMALIZATION — status report

**Status: `MAXIMAL_ERASURE_NORMALIZATION` (full official theorem proved).**

Everything below is additive: no existing declaration, file or submission root was modified.
Two new source files and one new axiom-audit file:

* `RequestProject/Root/CodingTheory/ErasureSpanPolynomial.lean` — the pure polynomial
  extension-span theorem (no coding theory at all);
* `RequestProject/Root/CodingTheory/MaximalErasureNormalization.lean` — the common ambient
  dual-polynomial adapter, the span theorem for the dual spaces, the noncontainment /
  rank-one / label theorems, the official normalization theorem, the deployed row and the
  normalized extremal locus;
* `RequestProject/MaximalErasureNormalizationAxiomAudit.lean` — `#print axioms` for every
  user-facing declaration.

Scope notes, as instructed:

* the `rsList(f₁, 2e)` route is not used anywhere and is not revisited;
* no operator `Φ_S(Q₀,Q₁)`, no rank claim `2n − z₁`, no condition `z₁ > w` is formalized;
* **no** bound on `|Γ|` is claimed or derived; normalization only replaces variable-size
  witnesses by exact-size witnesses.

Throughout, `F` is an arbitrary field, `D ⊆ F` an arbitrary evaluation domain, `n = |D|`,
`r = n − k`, and official badness is the project's existing predicate
`Root.CodingTheory.IsBad` (`MCA.lean`):

```
IsBad k e f₀ f₁ γ  ↔  ∃ S, |D| ≤ |S| + e ∧ IsCloseOn k S (f₀ + γ·f₁) ∧ ¬ LineCloseOn k S f₀ f₁.
```

Erasure sets are the complements of windows: `E = Sᶜ`, `|E| = n − |S| ≤ e`.

---

## 1. Exact polynomial span theorem

`Root.CodingTheory.ErasureSpan.span_qPoly_eq_degreeLT`

```
Function.Injective v → ∀ s, s + 1 ≤ |Ω| →
  span_F { Q_A : A ⊆ Ω, |A| = s } = F[X]_{<s+1}
```

proved by induction on `s` from the difference identity
`qPoly_insert_sub_insert : Q_{B∪{a}} − Q_{B∪{b}} = (v b − v a)·Q_B`, plus the one-step lemma
`degreeLT_succ_le_of_monic`.

`Root.CodingTheory.ErasureSpan.iSup_qModule_eq_degreeLT`

```
d ≥ w ≥ 1,  s = d − w,  s + 1 ≤ |Ω|  →
  ⨆_{A ⊆ Ω, |A| = s} Q_A · F[X]_{<w} = F[X]_{<d}
```

No dimension argument is used: `⊆` is a degree bound, `⊇` exhibits every monomial `X^m`,
`m < d`, as `X^{min(m,s)} · X^{m − min(m,s)}`.

Boundary cases recorded explicitly:

* `d = w` (hence `d − w = 0`, family `{∅}`): `iSup_qModule_eq_degreeLT_of_eq`;
* `w = 1`: `iSup_qModule_eq_degreeLT_of_w_eq_one`.

## 2. Common ambient dual-polynomial adapter

One fixed, **`E`-independent** linear map with the GRS multiplier built in:

```
lam D a = (∏_{b ∈ D, b ≠ a} (a − b))⁻¹                      (`MaxErasure.lam`, never zero)
Ψ = psi D : F[X] →ₗ (↥D → F),  Ψ(p) a = lam D a · p(a)      (`MaxErasure.psi`)
```

The ambient pairing is the project's existing one, `⟨x,y⟩ = ∑ a, x a * y a`, together with the
existing `Absorption.dualCode` and its biduality `dualCode_dualCode`.

```
V_E = RS_k ⊔ positionSpace F E                              (`MaxErasure.vSpace`)
W_E = dualCode V_E                                          (`MaxErasure.wSpace`)
```

* `mem_vSpace_iff : f ∈ V_E ↔ IsCloseOn k Eᶜ f` — the dictionary with official closeness;
* `mem_vSpace_iff_pairing` — biduality, `f ∈ V_E ↔ ∀ y ∈ W_E, ⟨y,f⟩ = 0`;
* `coeff_top_eq_sum_lam`, `sum_lam_eval_eq_zero` — `∑_{a∈D} λ_a h(a) = 0` for `deg h < n − 1`
  (the top Lagrange coefficient);
* `dualCode_reedSolomon : dualCode RS_k = Ψ(F[X]_{<r})` for `k ≤ n`;
* **`wSpace_eq_wModel`** — for every `E` with `|E| ≤ r`

  ```
  W_E = Ψ ( Q_E · F[X]_{<r − |E|} ).
  ```

  The multiplier `λ` and the map `Ψ` are the same for all `E`; the family of identifications is
  therefore compatible, not a collection of unrelated isomorphisms.

## 3. Exact `W_E = span W_{E'}` theorem

`Root.CodingTheory.MaxErasure.wSpace_eq_iSup_wSpace`

```
k ≤ n,  |E| ≤ e,  e < r,  e < n  →
  W_E = ⨆ { W_{E ∪ A} : A ⊆ Eᶜ, |A| = e − |E| }
```

an equality of project subspaces, obtained by transporting §1 along the single `Ψ` with
`d = r − |E|`, `w = r − e`, `Ω = Eᶜ` (`|Ω| = n − |E| ≥ e − |E| + 1`), using
`map_mulLeft_qModule : Q_E · (Q_A · F[X]_{<w}) = Q_{E∪A} · F[X]_{<w}` for `E`, `A` disjoint.

## 4. Noncontainment / nonzero-restriction theorem

One common map, restricted:

```
Λ = lambdaMap f₀ f₁ : (↥D → F) →ₗ F × F,  y ↦ (⟨f₀,y⟩, ⟨f₁,y⟩)
Λ|W_E = lamRestrict k E f₀ f₁,   range (Λ|W_E) = lamImage k E f₀ f₁   (`range_lamRestrict`)
```

* **`lamImage_eq_bot_iff`** — from the ambient pairing alone, with *no* agreement hypothesis:

  ```
  Λ(W_E) = ⊥  ↔  LineCloseOn k Eᶜ f₀ f₁  ( ↔ L = span{f₀,f₁} ⊆ V_E ).
  ```

* only then, with agreement, `lamImage_le_line : Λ(W_E) ≤ F·(−γ,1)`, and
  `lamImage_eq_span`, `finrank_lamImage` give `rank (Λ|W_E) = 1` with image exactly `F·(−γ,1)`.

## 5. Same finite-label theorem

* `lamImage_eq_span` — the label of the enlarged witness is again `F·(−γ,1)`;
* `lamImage_ne_infinity` — the label is finite: it is not `[1 : 0]`;
* `challenge_eq_of_span_eq` — the label determines the challenge;
* `maximal_erasure_normalization` returns, besides `E ⊆ E'` and `|E'| = e`, the two equalities
  `Λ(W_{E'}) = Λ(W_E)` and `Λ(W_{E'}) = F·(−γ,1)`.

## 6. Official normalization theorem

`Root.CodingTheory.MaxErasure.maximal_erasure_normalization` (abstract form) and

`Root.CodingTheory.MaxErasure.isBad_exact_window`

```
k ≤ n,  e < r,  e < n,  IsBad k e f₀ f₁ γ  →
  ∃ S, |S| = n − e ∧ IsCloseOn k S (f₀ + γ·f₁) ∧ ¬ LineCloseOn k S f₀ f₁
```

with `isBad_of_exact_window` recording that official badness of the *same* `γ` is retained, and

`isBad_iff_exists_exact_erasure`

```
IsBad k e f₀ f₁ γ  ↔  ∃ E', |E'| = e ∧ IsCloseOn k E'ᶜ (f₀ + γ·f₁) ∧ ¬ LineCloseOn k E'ᶜ f₀ f₁.
```

The hypothesis `e < n` is stated as required; over `ℕ` it is in fact implied by `e < r = n − k`.
No challenge-count consequence is drawn anywhere.

## 7. Deployed row `w = 69632`

`Root.CodingTheory.MaxErasure.deployed_maximal_erasure_normalization`

```
k ≤ n,  r = n − k = 1048576,  e = 978944,  IsBad k 978944 f₀ f₁ γ  →
  (n − k) − 978944 = 69632  ∧  978944 < n  ∧
  ∃ E', |E'| = 978944 ∧ agreement ∧ noncontainment
```

so every official bad challenge admits an exact-`e` representation through a nonzero rank-one
restriction of `Λ` on a dual space of the common fixed dimension `w = r − e = 69632`.

## 8. Normalized locus inclusion

```
normalizedLocus k e f₀ f₁ = { E : |E| = e ∧ rank (Λ|W_E) = 1 }
```

`badSet_subset_label_image` — `Γ ⊆ ℓ(E_Λ)` with the finite-label qualification: every officially
bad `γ` is the label `F·(−γ,1)` of a point of the locus.  The converse inclusion is **not**
asserted.

`challenge_unique` — for a fixed `E`, at most one finite `γ` can satisfy agreement together with
noncontainment (direct proof: `(γ−δ)·f₁ ∈ V_E` forces `f₁ ∈ V_E`, then `f₀ ∈ V_E`).

### Degenerate-line guard

The normalization theorem carries **no** hypothesis on `dim L`; its proof never uses one, so the
case `dim span{f₀,f₁} < 2` is covered.  In addition `degenerate_line_challenge` shows that in the
degenerate case `f₁ = c • f₀` badness is rigid: the only possible challenge satisfies
`1 + γ·c = 0`.

## 9. `lake build`

`lake build RequestProject.MaximalErasureNormalizationAxiomAudit` (and the two source modules)
completes successfully; the files are part of the default `RequestProject` library target.
No `sorry` occurs in either new source file.

## 10. `#print axioms`

`RequestProject/MaximalErasureNormalizationAxiomAudit.lean` prints, for every user-facing
declaration listed above,

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```
