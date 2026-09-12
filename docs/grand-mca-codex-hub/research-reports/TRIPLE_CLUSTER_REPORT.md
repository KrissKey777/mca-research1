# The triple-cluster proximity gap for Reed–Solomon lines

*Files: `RequestProject/Root/CodingTheory/TripleEnergy.lean`,
`RequestProject/Root/CodingTheory/TripleClusterProximity.lean`.  Everything below is
Lean-checked, `sorry`-free, and uses only `propext`, `Classical.choice`, `Quot.sound`.*

## 1. What is proved

Notation: `D ⊆ F` the evaluation set, `n = |D|`, `C = RS[D,k]`, error budget `e`, relative
rate `ρ = k/n`, relative radius `δ = e/n`.  For a line `γ ↦ f₀ + γ·f₁`,

* `goodZ k e f₀ f₁ = { γ : d(f₀+γ·f₁, C) ≤ e }` — the close challenges, `N = |goodZ|`;
* `HasCorrelatedAgreement k e f₀ f₁` — there are codewords `q₀, q₁` of degree `< k` and a
  window of **at least `n − e`** positions on which `f₀ = q₀` *and* `f₁ = q₁`.

**Main theorem** (`card_goodZ_mul_pow_three_le`).  For every line, if
`¬ HasCorrelatedAgreement k e f₀ f₁` then

```
N · (n − e)³  ≤  N · (k−1) · n²  +  (e+2) · n³ .
```

**Division form** (`card_goodZ_le_of_gap`).  If `(k−1)n² + c·n² ≤ (n−e)³` for some `c ≥ 1`
then `N · c ≤ (e+2) · n`.

**Far centre** (`card_badSet_le_of_far_of_gap`, `epsMCA_le_of_far_of_gap`).  If
`e < d(f₀, C)` then correlated agreement is impossible
(`not_hasCorrelatedAgreement_of_far`), so the bound is unconditional; and by
`FarCenterProximity.badSet_eq_goodZ_of_far` the MCA bad set *equals* `goodZ`, so

```
#Bad · c ≤ (e+2)·n ,        ε_mca ≤ (e+2)·n / (c·|F|) .
```

The direction `f₁` is completely arbitrary: this is a **far–far** statement.

**Explicit constant-gap regime** (`gap_of_rate_radius`,
`card_badSet_le_of_far_of_rate_radius`).  At `k ≤ 3n/10` and `e ≤ 3n/10` one may take any
`c ≤ n/25`, so with `c = ⌊n/25⌋`

```
#Bad ≤ 25·(e+2) = O(n)   and   ε_mca = O(n/|F|).
```

**The regime** is `(n−e)³ > (k−1)·n²`, i.e. in relative terms

```
δ  <  1 − ρ^{1/3}.
```

`gap_of_three_mul_lt` proves `3e < n − k + 1  ⟹  (k−1)n² < (n−e)³`: the new regime
**strictly contains** the unique-decoding regime that carried the previous certified MCA row
(`MCA.card_badSet_le`), and it also contains the pair-split ceiling
`δ < (3 − √(5+4ρ))/2` of the earlier work — that ceiling comes from `(1−δ)² > ρ + δ`, which
is weaker than `(1−δ)³ > ρ` for every `ρ ∈ [0,1]`.  Numerically at `ρ = 1/4`: `0.25`
(unique decoding), `0.275` (pair split), **`0.370` (here)**, `0.5` (Johnson).
`regime_example_1000_251_300` certifies one such point: `n = 1000, k = 251, e = 300` is
outside `3e < n−k+1` and inside the new regime with gap `c = 93`.

## 2. Why it escapes the pairwise barrier

Two close challenges `γ₁ ≠ γ₂` with witnesses `p₁, p₂` always produce an affine pair
`q₁ = (p₁−p₂)/(γ₁−γ₂)`, `q₀ = p₁ − γ₁q₁` (`exists_affine_pair`) and correlated agreement on
`A₁ ∩ A₂`, a window of size only `≥ n − 2e`.  Since correlated agreement is required on
`n − e` positions, no pairwise argument can conclude outside `2e < n − k + 1`.  The three
new ingredients:

1. **Local → global (the triple step, `eq_add_smul_of_card_inter_ge`).**  If a *third*
   challenge's agreement set meets `A₁ ∩ A₂` in `≥ k` positions, then
   `p₃ = q₀ + γ₃·q₁` **as polynomials**: on the common window `f₀ = q₀`, `f₁ = q₁`, so
   `p₃ − (q₀+γ₃q₁)` is a polynomial of degree `< k` with `k` roots.  A local hypothesis of
   size `k` yields a global identity.

2. **Cluster → full window (`card_cluster_le`).**  Let `K` be the set of challenges whose
   witness is exactly `q₀ + γ·q₁`.  For `γ ≠ γ'` in `K`, every common agreement position
   lies in `T = {f₀ = q₀} ∩ {f₁ = q₁}`, so the sets `A_γ \ T` are pairwise disjoint, each of
   size `≥ n − e − |T|`, inside a set of size `n − |T|`.  If `|T| < n − e` this forces
   `|K| ≤ e + 1`.  Contrapositive: **a cluster of `e+2` challenges gives correlated
   agreement on a full `n − e` window** — the pairwise `2e` loss is amortised away by the
   *number* of challenges, not by the radius.

3. **A global invariant: third-moment energy (`TripleEnergy.lean`).**  With
   `mult x = #{γ ∈ goodZ : x ∈ A_γ}`,

   ```
   ∑ₓ mult(x)³ = ∑_{γ₁,γ₂,γ₃} |A_{γ₁} ∩ A_{γ₂} ∩ A_{γ₃}|   (identity)
   (∑ₓ mult x)³ ≤ n² · ∑ₓ mult(x)³                          (Jensen / power mean)
   ∑ₓ mult x ≥ N · (n − e)                                   (each set is large).
   ```

   If there is no correlated agreement, then by 1.–2. every ordered pair has at most `e+1`
   partners with a triple intersection `≥ k`, and all other triples intersect in `≤ k−1`
   positions.  Feeding that into the energy identity gives the main inequality.  This is
   exactly the *invariant of the whole close-challenge set* that pairwise and
   near-direction methods lacked: the hypothesis constrains triples, the conclusion bounds
   the cardinality of the entire set.

## 2b. The pair-energy companion

The same cluster step also upgrades the classical second moment
(`card_goodZ_pair_dichotomy`).  Without correlated agreement, either `N ≤ e+1`, or **every**
pairwise intersection satisfies `|A_γ ∩ A_δ| < k + e` — a pair meeting in `k+e` positions
would put every close challenge into one cluster, since the triple intersection then loses
at most `e` positions — and Cauchy–Schwarz
(`TripleEnergy.card_mul_pow_two_le`) gives

```
N · (n − e)²  ≤  N · (k+e−1) · n  +  n² ,
```

hence `N ≤ max(e+1, n/c)` whenever `(k+e−1)n + c·n ≤ (n−e)²`
(`card_goodZ_le_of_pair_gap`, `card_badSet_le_of_far_of_pair_gap`).  Its regime
`(1−δ)² > ρ + δ` is the earlier pair-split ceiling `δ < (3−√(5+4ρ))/2`, contained in the
cubic regime; where both apply the pair bound has the smaller constant, and where only the
cubic one applies it is the only bound available.

## 3. Consistency checks

* **The subspace pencil is not contradicted.**  For `n = p^m+1`, `k = p^{ℓ−1}+1`,
  `e = n − p^ℓ − 1` one has `(n−e)³ ≈ p^{3ℓ}` and `(k−1)n² ≈ p^{ℓ−1+2m}`, so the hypothesis
  `(k−1)n² < (n−e)³` needs `2ℓ > 2m − 1`, i.e. `ℓ ≥ m` — precisely where the family becomes
  trivial.  The superpolynomial counterexample lives exactly outside the new regime (and,
  with the same computation, exactly outside the Johnson regime).
* **Sharpness of the far-centre hypothesis.**  If `f₀` and `f₁` are codewords then
  `goodZ = F` while `badSet = ∅`; the theorem's first alternative (correlated agreement) is
  what holds there.
* **Non-vacuity.**  `card_badSet_le_of_polynomial_center` instantiates the bound at every
  centre given by a polynomial of degree `≥ k` with `deg P + e < n`, with an arbitrary
  direction.

## 4. What remains open

The regime `1 − ρ^{1/3} ≤ δ` is untouched; in particular the Johnson band
`1 − ρ^{1/3} ≤ δ < 1 − √ρ` and everything up to capacity `1 − ρ`.  Two structural remarks
from this work:

* The method's ceiling is set by the exponent in the moment inequality: `w`-fold
  intersections average `n·(1−δ)^w` and the triple step needs `≥ k = ρn`, so `w = 3` is the
  optimum (`w = 2` cannot force a polynomial identity, `w ≥ 4` needs `(1−δ)^w > ρ`, which is
  worse).  Reaching `1 − √ρ` therefore requires a step that turns a *pairwise* window of
  size `(1−δ)²n` into a global identity, not merely correlated agreement.
* Assuming `N ≥ e+2`, the argument also certifies that **all** pairwise intersections satisfy
  `|A_γ ∩ A_δ| ≤ k + e − 1` (otherwise every challenge joins one cluster); combining this
  with the energy bound improves the constant in the conclusion but not the radius.
* For lines that *do* have correlated agreement the MCA bad set is still uncontrolled
  outside unique decoding: two distinct correlated pairs `(q₀,q₁) ≠ (q₀',q₁')` can coexist
  once `n − 2e < k`, and each window may be witnessed by a different pair.  This is why the
  far-centre hypothesis (equivalently, the exact reduction of `FarCenterProximity.lean`) is
  the right frame for the remaining question.
