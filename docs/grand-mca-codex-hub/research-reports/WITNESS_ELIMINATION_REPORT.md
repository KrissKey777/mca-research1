# Witness elimination for far-centred Reed–Solomon lines

Module: `RequestProject/Root/CodingTheory/WitnessElimination.lean` (no axioms, no `sorry`).

## 0.  Where this sits

For a line `γ ↦ f₀ + γ·f₁` of words over `D ⊆ F`, `n = |D|`, and the code `RS[D,k]`,
`FarCenterProximity.badSet_eq_goodZ_of_far` reduces the mutual-correlated-agreement question
to the proximity question whenever the centre is *far*, `e < d(f₀, RS[D,k])`:

```
#Bad = #goodZ = #{ γ : d(f₀ + γ f₁, RS[D,k]) ≤ e }.
```

Every close challenge `γ` carries a **witness** `p_γ ∈ F[X]`, `deg p_γ < k`, agreeing with
`f₀ + γ f₁` on `≥ n − e` positions.  The certified unconditional frontier of the project is
still the unique-decoding window (`Subresultant.card_badSet_le_unconditional`,
`#Bad ≤ (k+1)e+1` for `k + 2e ≤ n`, i.e. `δ ≤ (1−ρ)/2 = 1/4` at rate `1/2`) together with the
third-moment regime `δ < 1 − ρ^{1/3}`.  This module isolates and formalises the *algebraic*
mechanism that a Guruswami–Sudan style attack on the region above `1/4` must use, and proves
the two ends of that chain unconditionally.

Nothing here yet certifies a new radius; §5 states exactly what is missing and why the
obvious ways of closing the gap fail.

## 1.  Elimination (`card_le_natDegree_of_yfree_combination`)

Work in `F[Z][X][Y]`.  For a challenge `γ` and a witness `p` let `subst γ p` be the
substitution ring homomorphism `Z ↦ γ, Y ↦ p`, valued in `F[X]`.

> **Theorem.**  Let `Q₁, Q₂ ∈ F[Z][X][Y]` and suppose `C R = U·Q₁ + V·Q₂` for some
> `R ∈ F[Z][X]` — a `Y`-free element of the ideal `(Q₁, Q₂)`.  If every `γ` in a finite set
> `G` admits a `p_γ` with `subst γ p_γ Q₁ = subst γ p_γ Q₂ = 0`, then every `X`-coefficient
> of `R` vanishes at every `γ ∈ G`; in particular `#G ≤ deg_Z (R.coeff j)` for any `j` with
> `R.coeff j ≠ 0`.

The proof is one line of algebra: apply the substitution homomorphism to the identity.  It
is the exact, hypothesis-free form of "eliminate the challenge variable": no genericity, no
field-size condition, no radius condition.  `R` plays the role of `Res_Y(Q₁, Q₂)`, but the
statement does not need resultant machinery — any explicit `Y`-free combination will do, and
`R ≠ 0` is precisely the non-degeneracy that has to be supplied.

Note that the two spike-line families that refuted the earlier existential hypotheses
(`ND_EXISTS_MISSION_REPORT.md`) all have `d(f₀, RS) = 1 ≤ e`: they are **near**-centred, so
they say nothing about the far-centred instances that are the only remaining case.

## 2.  The incidence count (`card_mul_le_of_lineResidual`)

For `W ∈ F[Z][X][Y]` and `x ∈ D` put

```
lineResidual W f₀ f₁ x  =  W(Z, x, f₀ x + Z·f₁ x)  ∈ F[Z],
```

of degree `≤ deg_Z W + deg_Y W` (`natDegree_lineResidual_le`), and let `lineSupport W f₀ f₁`
be the set of positions at which this residual vanishes identically.

> **Theorem.**  If all line residuals have degree `≤ d`, if `|lineSupport| + e + s ≤ n`, and
> if every `γ ∈ G` has a witness `p_γ` with `subst γ p_γ W = 0` agreeing with the line on
> `≥ n − e` positions, then `#G · s ≤ n · d`.

This is the "syndrome-line incidence" count in exact form: each agreement position of each
close challenge is an incidence, each position with a nonzero residual absorbs at most `d` of
them.

**A warning that this formalisation makes precise.**  The count is *vacuous* for the
Guruswami–Sudan interpolant itself.  If `W` interpolates the line points
`(x, f₀ x + Z f₁ x)` with any multiplicity `≥ 1` — which is exactly what the root step needs —
then `lineResidual W f₀ f₁ x = 0` for **every** `x`, so `lineSupport = D` and the hypothesis
`|lineSupport| + e + s ≤ n` forces `s = 0`.  The count is therefore only usable on a proper
factor of an interpolant, or on a witness family such as the one in §3.  This kills the
otherwise natural plan of applying support counting directly to the interpolant.

## 3.  Polynomial witness families over a far centre

Let `P ∈ (F[X])[Z]`, `P(Z,X) = Σᵢ Pᵢ(X) Zⁱ`, and `familyWitness P γ = P(γ, ·)`.

> **Theorem** (`card_le_of_polynomial_witness_family`).  Let `e < d(f₀, RS[D,k])` and let the
> constant `Z`-coefficient `P₀` have degree `< k`.  Then at most `n · max (deg_Z P) 1`
> challenges can be `e`-close with witness `P(γ, ·)`.

The far centre is exactly what pays for the degenerate branch here.  The residual
`Z ↦ P(Z,x) − f₀ x − Z·f₁ x` vanishes identically precisely at positions where
`f₀ x = P₀(x)`; if there were `≥ n − e` of them, `f₀` would be `e`-close to the code.  Hence
at least `e+1` positions carry a nonzero residual of degree `≤ max (deg_Z P) 1`, and the
double count of §2 applies.  Only the constant coefficient of the family is required to be a
codeword polynomial; higher coefficients are unrestricted.

Corollaries: `card_goodZ_le_of_polynomial_witness_family`,
`card_badSet_le_of_polynomial_witness_family`, and the union version
`card_goodZ_le_of_witness_families`: if the close challenges are covered by `t` polynomial
families of `Z`-degree `≤ d`, then `#goodZ ≤ t · n · max d 1`.  This is the shape in which the
degenerate branch has to be paid for — *bound the number of families*.

### 3b.  Scaled (rational) witness families

> **Theorem** (`card_le_of_scaled_polynomial_witness_family`,
> `card_goodZ_le_of_scaled_witness_family`).  Let `e < d(f₀, RS[D,k])`, let `a ∈ F[Z]` be
> nonzero and `B ∈ (F[X])[Z]`, and suppose the coefficient of `B` at the order of `a`,
> rescaled by the trailing coefficient of `a`, has degree `< k`.  Then at most
> `n · max (deg_Z B) (deg a + 1)` challenges are `e`-close with witness `a(γ)⁻¹·B(γ,·)`, and
> at most `deg a + n · max (deg_Z B) (deg a + 1)` close challenges in total if every other
> close challenge is a root of `a`.

This is the case the `Y`-degree-one factor of a Guruswami–Sudan interpolant actually
produces: the witnesses are polynomial *up to a scalar depending on the challenge*.  The
far-centre kill now happens at the **trailing** coefficient of `a`: if the residual
`B(Z,x) − a(Z)·(f₀ x + Z f₁ x)` vanishes identically, then reading off the coefficient of
`Z^{ord a}` gives `f₀ x = (a_{ord a})⁻¹·B_{ord a}(x)`, so more than `n − e` such positions
would put `f₀` within `e` of the code.

## 4.  The chain, and the exact remaining gap

The Guruswami–Sudan attack on `δ > 1/4` at rate `1/2` runs:

1. interpolate over `F[Z]`: a nonzero `Q ∈ F[Z][X][Y]`, `deg_Y ≤ L`,
   `wdeg_{1,k−1} < b`, with multiplicity `≥ m` at all `n` line points
   (`GS.exists_line_interpolating` in `TrivariateInterpolation.lean`);
2. root step: for each close `γ`, `(Y − p_γ) | Q(γ,X,Y)`, i.e. `subst γ p_γ Q = 0`,
   as soon as `(n−e)·m > b`;
3. factor `Q` over `F(Z,X)[Y]`; each close `γ` is carried by one irreducible factor `G`
   (there are `≤ L` of them, plus `≤ deg_Z(content)` exceptional challenges);
4. for a factor `G` with `deg_Y G ≥ 1`: either some module element is coprime to `G`, in
   which case §1 gives `#G ≤ deg_Z R = poly(n)`, or `G` divides everything.

The Johnson-radius arithmetic is: the GS radius is `α > √(ρ(1+1/m))`, so at `ρ = 1/2` one
needs `m ≥ 9` to beat `α = 3/4` (`m = 9` gives `δ < 0.2546`, `m = 16` gives `δ < 0.271`), and
the resulting bound is `#Bad = O(n · L · deg_Z) = O(n²)` for fixed gap — far below the
`O(n^2.8966)` needed for the prize row.  So the arithmetic is not the obstruction.

**What is missing** is step 4's degenerate branch:

* `deg_Y G = 1`, i.e. `G = A(Z,X)·Y − B(Z,X)`.  **This case is now settled analytically**
  (§3b).  Take `G` primitive, so `gcd(A,B) = 1` in `F[Z][X]`.  Pseudo-dividing `B` by `A` in
  `F(Z)[X]` gives `lc_X(A)^s·B = Q·A + R` with `deg_X R < deg_X A`; a close challenge `γ`
  with `lc_X(A)(γ) ≠ 0` forces `A^γ | B^γ` (its witness `p_γ` is a *polynomial*) and hence
  `R^γ = 0`.  Either `R ≠ 0`, and then all such `γ` are roots of a fixed nonzero coefficient
  of `R`, so their number is at most `deg_Z R`; or `R = 0`, and then `A | B` in `F(Z)[X]`,
  which together with `gcd(A,B) = 1` forces `deg_X A = 0`, i.e. `A = a(Z)`.  The witnesses
  are then the **scaled family** `p_γ = a(γ)⁻¹·B(γ,·)`, and
  `card_goodZ_le_of_scaled_witness_family` bounds the close set by
  `deg a + n·max(deg_Z B, deg a + 1)`.  (Coefficients of `B` of `X`-degree `≥ k` are killed
  first: they vanish at every close challenge, since `p_γ` has degree `< k`.)  What is *not*
  formalised here is the factorisation bookkeeping — the passage from an interpolant to a
  primitive factor and the pseudo-division — only the analytic core, which is the part the
  far centre pays for.
* `deg_Y G ≥ 2` and `G` irreducible over `F(Z,X)`.  Then `G(γ,X,Y)` must acquire a linear
  factor for every close `γ`.  Over a finite field this cannot be excluded by degree
  arguments alone (a degree-`ℓ` cover of the `Z`-line splits over a positive fraction of the
  field), so the extra input has to be the metric one — that the root `p_γ` has degree `< k`
  *and* agrees with the line on `≥ n − e` positions.

**A quantitative remark on "G divides everything"** (computed here informally, not
formalised).  Write `S(b,L)` for the `F(Z)`-dimension of the space of `W` with
`wdeg_{1,k−1} W < b`, `deg_Y W ≤ L`.  The interpolation module has dimension
`≥ S(b,L) − n·m(m+1)/2`, and the multiples of a fixed `G` with `deg_Y G = ℓ` span
`S(b − wdeg G, L − ℓ)`.  Using `wdeg G ≥ ℓ(k−1)` the difference is
`≥ ℓ·[b − (k−1)(ℓ−1)/2]`, so `G` can divide the whole module only if

```
ℓ · [ b − (k−1)(ℓ−1)/2 ]  ≤  n·m(m+1)/2 .
```

With `ρ = 1/2`, `b ≈ αmn`, `m = 9`, `α = 3/4` this fails for `ℓ ≥ 11` but holds for small
`ℓ`.  So the degenerate branch is confined to common factors of *small* `Y`-degree — exactly
the two cases listed above — and, dually, a common factor of large `Y`-degree is impossible.
This is the sharpest structural statement currently available on the branch; it is recorded
here as analysis, not as a Lean theorem.

## 5.  Approaches ruled out (with reasons)

* **Support counting on the interpolant** — vacuous, see §2.
* **Higher moments** — `w = 3` is optimal for the TripleEnergy architecture
  (`w=2 : 0.29289` as a bare threshold, `w=3 : 0.20630`, `w=4 : 0.15910`).
* **Counting affine witness-pair clusters** — a cluster has size `≤ e+1`
  (`card_cluster_le`), but a cluster is determined by a pair `(q₀,q₁)` agreeing with
  `(f₀,f₁)` on `≥ n − 2e` positions, i.e. by a list-decoding of the *interleaved* code at
  radius `2δ`; the Johnson condition `2δ < 1 − √ρ` gives only `δ < 0.1464` at `ρ = 1/2`,
  worse than the existing `1/4`.
* **Dimension counting to force a coprime module element** — fails for small `ℓ` (§4).
* **Bounds depending on `√|F|`** (Weil/Bertini–Noether control of the reducible
  specialisations) — mathematically available, but useless in the intended STARK regime,
  where the soundness error must be `poly(n)/|F|`, not `|F|^{-1/2}`.

## 6.  Status

* Formalised and unconditional: §1, §2, §3, §3b and the corollaries of §4 in
  `WitnessElimination.lean`.
* Not formalised, and open: the second degenerate branch of §4 (an irreducible common factor
  of `Y`-degree `≥ 2`), together with the purely algebraic factorisation bookkeeping of the
  first branch.  Closing them, with
  the GS parameters `m ≥ 9`, `L ≈ 12`, `b < (n−e)m`, would give a far-centred `O(n²)`
  proximity bound at `ρ = 1/2` for `δ < 0.2546`, the first crossing of the classical `1/4`
  line, and with `m → ∞` the whole Johnson region.
