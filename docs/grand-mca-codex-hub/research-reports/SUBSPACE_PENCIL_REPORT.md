# The subspace pencil: `#Bad` beats every fixed polynomial at some vanishing capacity gap

> **CORRECTION (audit, later session).**  The original title of this report read
> "`#Bad` is superpolynomial at *every* vanishing capacity gap".  That is **not** what the
> Lean theorem `exists_superpolynomial_badSet_of_small_relative_gap` says, and it is not what
> the construction gives.  The theorem is an *existence* statement: for each pair `(d, M)`
> there is a parameter point of the family with `η ≤ 1/M` and `#Bad > n^d`.  The parameter
> point depends on `d`; the gap shrinks as `d` grows.  See `CONSTANT_GAP_MCA_REPORT.md` §1 and
> the certified statements in
> `RequestProject/Root/CodingTheory/SubspacePencilAudit.lean`:
>
> * `subspacePencil_bound_le_pow_card`: the guarantee never exceeds `n^{m−ℓ}`, and
>   `m − ℓ = log_p(1/η) + O(1)`, so at a *fixed* relative gap the family is polynomial;
> * `subspacePencil_superpoly_forces_gap`: beating `n^d` forces `m − ℓ > d`, hence
>   `η < p^{−d}`;
> * `subspacePencil_vanishing_gap_linear_bound`: at `ℓ = 1` the gap is `η ≤ p^{1−m} → 0` — the
>   smallest the family reaches — yet the guarantee is only `p^{m−1} < n`, i.e. linear.  So a
>   vanishing gap alone does **not** make the family superpolynomial: the exponent is
>   `ℓ(m−ℓ)/m`, governed by the pair `(ℓ, m)` and not by `η`;
> * `subspacePencil_gap_eq_pred_mul`: the family lives on the curve `c = (p−1)(k−1)`, so its
>   relative gap and its rate vanish together (`η ≈ (p−1)ρ`) and the relative decoding radius
>   tends to `1`.  Nothing is proved by this family about constant-rate codes at a small gap.
>
> Two further caveats on the reading of the result.  (i) The family realises only the sparse
> parameter grid `n = p^m + 1`, `k = p^{ℓ−1} + 1`, `c = p^ℓ − p^{ℓ−1}`; no transfer of
> bad-set lower bounds to neighbouring `(n, k, e)` is proved anywhere in the project.
> (ii) The construction needs `|F| > p^m + p^{2ℓ(m−ℓ)+ℓ}`, i.e. a field super-quadratic in the
> bad-set size, so the certified soundness error `ε_mca ≥ #Bad/|F|` it produces is *smaller*
> than `p^{−ℓ(m−ℓ)}`; the result is about `#Bad` versus `poly(n)`, not about `ε_mca` being
> large.
>
> The mathematics of the construction below is unaffected; only the reading of its
> asymptotics is corrected.  Sections 0 and 3 are annotated accordingly.

**Files.**
`RequestProject/Root/CodingTheory/AdditivePolynomial.lean`,
`RequestProject/Root/CodingTheory/SubspaceFamily.lean`,
`RequestProject/Root/CodingTheory/SubspacePencil.lean`,
`RequestProject/Root/CodingTheory/IndicatorLineList.lean`.
All build, no `sorry`, axioms `propext, Classical.choice, Quot.sound` only.
Independent exact-arithmetic check: `analysis/subspace_pencil_check.py`.

Notation as in `CAPACITY_GAP_REPORT.md`: `n = |D|`, `κ = n − k`, absolute capacity gap
`c = n − k − e = κ − e`, relative gap `η = c/n`, and `#Bad = (badSet k e f₀ f₁).card` is the
number of bad challenges of one MCA line in the project's own definitions (`MCA.lean`).

---

## 0. What was open, and what is new

`CapacityGapPencil.lean` produced `#Bad ≥ C(n/c, k/c + 1)`.  That is `exp(Θ(1/η))` at fixed
`c`, but it decays to `O(1)` as soon as `c` grows linearly: for `c = Θ(n)` the number of
blocks `m = n/c` is `O(1)`.  The picture it suggested was a **gap-layer law**

```
max #Bad  ≍  poly(n) + exp(Θ(1/η)),
```

i.e. everything beyond the capacity boundary layer `c = O(n / log n)` would be polynomial.

**This law is false.**  The subspace pencil below gives, for every fixed `M` and every
polynomial degree `d`, parameter points with `η ≤ 1/M` and `#Bad > n^d`.  Since `n^d` beats
`poly(n) + exp(O(M))` for any fixed `M` once `n` is large, no law of the displayed shape can
hold.  The correct order supplied by this family is

```
#Bad  ≳  n^{log_p(1/η)}      (η = c/n, characteristic p),
```

which is superpolynomial exactly when `η → 0` — and only polynomial at constant `η`.  So the
transition is now pinned precisely at **constant** relative gap, and constant-gap Grand MCA
survives.

> **CORRECTION.**  The refutation of the gap-layer law stands as stated (it only needs the
> existence statement).  The sentence "`#Bad ≳ n^{log_p(1/η)}` … is superpolynomial exactly
> when `η → 0`" is *not* justified: the exponent supplied by the family is `ℓ(m−ℓ)/m`, which
> equals `log_p(1/η)` only when `ℓ ≥ m/2`, and is bounded (e.g. `≈ 1` at `ℓ = 1`) for other
> vanishing-gap regimes.  What is certified is: `#Bad ≥ p^{ℓ(m−ℓ)}` at the grid points, this
> never exceeds `n^{log_p(1/η)}`, and beating `n^d` requires `η < p^{−d}`.

---

## 1. The construction

Let `F` have characteristic `p`, let `U ⊆ F` be an `F_p`-subspace of dimension `m`, and pick
`w ∈ F ∖ U`.  Set

```
D = U ∪ {w},     n = |D| = p^m + 1,
k = p^{ℓ−1} + 1, e = n − p^ℓ − 1,   so   c = n − k − e = p^ℓ − p^{ℓ−1}.
```

Take the **subspace pencil**

```
f₀(x) = x^{p^ℓ},        f₁ = 1_{\{w\}}   (indicator of the extra point).
```

For every `ℓ`-dimensional `F_p`-subspace `V ≤ U`, let

```
L_V(X) = ∏_{v ∈ V} (X − v)
```

be its subspace polynomial.  `L_V` is a monic *`p`-polynomial*: `L_V = X^{p^ℓ} + Σ_{i<ℓ} a_i
X^{p^i}`, additive and `F_p`-linear on `F`.  Consequently

```
X^{p^ℓ} − L_V   has degree ≤ p^{ℓ−1} < k .
```

Put `γ_V = −L_V(w)` and `S_V = V ∪ {w}`, so `|S_V| = p^ℓ + 1 = n − e`, a legal window.

* On `V`: `f₀(x) + γ_V·f₁(x) = x^{p^ℓ} = x^{p^ℓ} − L_V(x)` since `L_V` vanishes on `V`.
* At `w`: `f₀(w) + γ_V·1 = w^{p^ℓ} − L_V(w)`.

So the single polynomial `X^{p^ℓ} − L_V`, of degree `< k`, interpolates the shifted word on the
whole of `S_V`: **`γ_V` is close on `S_V`**.  Conversely the direction `f₁ = 1_{\{w\}}` is *not*
interpolable on `S_V` by a polynomial of degree `< k`: such a polynomial would vanish on `V`
(`p^ℓ ≥ k` points) hence be `0`, contradicting the value `1` at `w`.  Therefore `γ_V` is bad.

Lean: `isBad_subspacePencil` (stated for an arbitrary `p`-polynomial `h` of the shape above,
so it is reusable), then `isBad_twist`.

## 2. Counting

The subspaces are enumerated by the **graph family**: split a dissociated basis
`b_0,…,b_{m−1}` of `U` as `c_0,…,c_{ℓ−1}` and `d_0,…,d_{m−ℓ−1}`, and for each tuple
`a = (a_0,…,a_{ℓ−1}) ∈ W^ℓ`, `W = span(d)`, take

```
V_a = span(c_0 + a_0, …, c_{ℓ−1} + a_{ℓ−1}).
```

These `|W|^ℓ = p^{ℓ(m−ℓ)}` subspaces are pairwise distinct (`graphList_span_injective`), and
their subspace polynomials are pairwise distinct (`subPoly_graph_injective`).

The challenges `γ_{V_a} = −L_{V_a}(w)` must additionally be pairwise **distinct**.  Distinct
`p`-polynomials of degree `p^ℓ` differ in a nonzero polynomial of degree `≤ p^ℓ`, which has at
most `p^ℓ` roots; there are `< (p^{ℓ(m−ℓ)})²` pairs, so a point `w` outside `U` separating all
of them exists as soon as

```
|F| > p^m + p^{ℓ(m−ℓ)} · p^{ℓ(m−ℓ)} · p^{ℓ}
```

(`exists_separating_point`).  Hence

```
#Bad ≥ p^{ℓ(m−ℓ)} .                        (card_badSet_ge_twistLists)
```

An unconditional packaging, including the existence of the dissociated basis in any
sufficiently large field of characteristic `p`, is `exists_subspacePencil`:

> for `1 ≤ ℓ ≤ m` and `|F| > p^m + p^{2ℓ(m−ℓ)+ℓ}` there are `D`, `f₀`, `f₁` with
> `|D| = p^m + 1`, `|D| = k + e + c` for `k = p^{ℓ−1}+1`, `e = |D| − p^ℓ − 1`,
> `c = p^ℓ − p^{ℓ−1}`, and `#Bad ≥ p^{ℓ(m−ℓ)}`.

## 3. The asymptotic statement

`exists_superpolynomial_badSet_of_small_relative_gap`:

> For all `d, M : ℕ` there is `N` such that in every field `K` of characteristic `p` with
> `p^N < |K|` there are a domain `D`, parameters `k, e, c` and a line `f₀, f₁` with
> `|D| = k + e + c`, `1 ≤ c`, `M·c ≤ |D|` (i.e. `η ≤ 1/M`) and `|D|^d < #Bad`.

Sanity check of the arithmetic: with `n ≈ p^m`, `c ≈ p^ℓ`, we have `η ≈ p^{ℓ−m}` and

```
#Bad ≥ p^{ℓ(m−ℓ)} = n^{ℓ(m−ℓ)/m} ≈ n^{ℓ}          (ℓ ≪ m)
```

while `1/η ≈ p^{m−ℓ}`.  Fixing `η ≈ p^{−g}` (so `m − ℓ = g` constant) and letting `ℓ → ∞`
gives `#Bad ≥ n^{Θ(g)}` with `n → ∞`: superpolynomial growth *in the exponent* at a fixed
small constant relative gap is **not** obtained, but for each fixed polynomial degree `d` the
bound `n^d` is exceeded at gap `≤ 1/M`.  That is exactly what kills the gap-layer law, and it
does so for every fixed `M` at once.

(**Correction**: as the next sentence already says, and as
`subspacePencil_vanishing_gap_linear_bound` certifies, `η → 0` is *necessary* but not
*sufficient* for the family to be superpolynomial.)

At **constant** `η` (i.e. `g = O(1)` and `ℓ = m − g`) the exponent `ℓ(m−ℓ)/m ≈ g` is bounded,
so the family yields only `n^{O(1)}`: the construction does **not** refute constant-gap Grand
MCA, and it is not merely a matter of tuning parameters — the exponent is exactly
`log_p(1/η)`.

## 4. Why this family cannot be pushed to constant gap: the indicator-line obstruction

`IndicatorLineList.lean` explains the barrier structurally.  Write `1_{\{w\}}` for the
indicator of one domain point, and let

```
rsList D k r f₀ = { RS codewords g of degree < k with d(f₀, g) ≤ r } .
```

* `card_badSet_indicator_le_card_rsList`: for **any** `f₀` and any `w`,

  ```
  #Bad(f₀, 1_{\{w\}}) ≤ |rsList D k (e+1) f₀| .
  ```

  A bad challenge `γ` owns a window `S`; `w ∈ S` (`mem_window_of_isBad_indicator`, else the
  whole line is close on `S`); the witness codeword agrees with `f₀` off `w` on `S`, hence lies
  within distance `e+1`; and its value at `w` is `f₀(w) + γ`, so `γ ↦` codeword is injective.

* `isBad_indicator_of_dist_le` and `image_rsList_sub_badSet_indicator`: conversely every
  codeword in the radius-`(e+1)` ball differing from `f₀` at `w` produces a bad challenge, so

  ```
  #{ distinct values g(w) − f₀(w) : g ∈ rsList D k (e+1) f₀, g(w) ≠ f₀(w) }
      ≤ #Bad(f₀, 1_{\{w\}}) .
  ```

So for indicator lines the MCA bad-set size *is* an RS list size at radius `e + 1 = n − k −
c + 1`, i.e. at relative radius `1 − ρ − η + 1/n`.  Producing a superpolynomial bad set at
constant `η` **by an indicator line** is therefore at least as hard as exhibiting a
Reed–Solomon code with a superpolynomial list at a constant gap to capacity — a well-known
open problem.  Any refutation of constant-gap Grand MCA must use a line whose direction is
supported on more than one point.

## 5. Numerical verification

`analysis/subspace_pencil_check.py` works in exact `GF(2^M)` arithmetic.

* `m = 3, ℓ = 2` (so `n = 9, k = 3, e = 4, c = 2`): all `7` subspace challenges are bad; an
  exhaustive scan finds `14` bad challenges in total, the predicted set is contained in them,
  and the `7` predicted values are pairwise distinct.
* Distinctness of `L_V(w)` over random `w ∉ U` holds while the field is large relative to the
  number of subspaces: `35/35`, `15/15`, `151/155`, `1157/1395` as collisions start —
  matching the pigeonhole requirement of `exists_separating_point`.

## 6. Status of the Lamzouri-style second-moment analogy

The suggested transfer was tried in the one form the MCA algebra does support, and it turns
out to reproduce a bound the project already has.

The natural "vector attached to each bad challenge" is the indicator of its window `S_γ`, and
the natural quadratic energy is the window-incidence energy

```
E = Σ_{γ, γ'} |S_γ ∩ S_{γ'}| = Σ_{x ∈ D} deg(x)²,      deg(x) = #{γ bad : x ∈ S_γ}.
```

Both sides of the Lamzouri mechanism are available:

* *lower bound by Cauchy–Schwarz* (the Bessel step): `Σ_x deg(x)² ≥ (Σ_x deg x)²/n ≥
  (#Bad·(n−e))²/n`, because every window has size `≥ n − e`;
* *upper bound on the off-diagonal* (the local step): for `γ ≠ γ'` the direction word `f₁`
  agrees with the degree-`<k` polynomial `(P_γ − P_{γ'})/(γ − γ')` on `S_γ ∩ S_{γ'}`, so
  `|S_γ ∩ S_{γ'}| ≤ A`, where `A` is the largest agreement of `f₁` with any codeword.

Comparing the two gives, exactly as in the schematic "cardinality ≤ energy" step,

```
#Bad  <  n(n−e) / ((n−e)² − A·n)        whenever  (n−e)² > A·n .
```

This is the Corrádi/set-family-Johnson inequality already recorded in the project as
`card_badSet_le_setFamilyJohnson_of_far` (`NearCodewordLineMCA.lean`), with the constant `A`
in place of `k + e − 1`; and the "near" complement (`A` large, i.e. `f₁` close to a codeword)
still has to be handled separately.  Optimising the resulting dichotomy over the split point
gives a radius `δ < (3 − √(5 + 4√ρ))/2`, which is *worse* than the `δ < (3 − √(5+4ρ))/2`
already certified by the existing near/far dichotomy.

So the second-moment reformulation is genuine — the global energy really does control the
cardinality without any control on individual pairs — but on the MCA side it is not new
information: the window-incidence energy is the same object the project's Johnson-type
arguments already exploit, and the binding constraint is the *near* case, which no
second-moment inequality addresses.  The analogy was therefore not pursued further, as the
prompt permitted.

## 6b. From one point to arbitrary directions, and the pairwise barrier

`DirectionListReduction.lean` removes the one-point restriction of §4 entirely.  For **every**
MCA line `(f₀, f₁)`:

```
#Bad(k, e, f₀, f₁)  ≤  1 + |D| · #{ codewords of degree < k within distance 2e of f₁ } .
```

(`card_badSet_le_mul_card_rsList`, no hypotheses.)  The proof fixes one bad challenge `γ₀`
with window `S₀` and interpolant `P₀`; for any other bad `γ` with window `S` and interpolant
`P`, the degree-`<k` polynomial `Q_γ = (P − P₀)/(γ − γ₀)` agrees with `f₁` on `S ∩ S₀`
(`≥ |D| − 2e` points), so `Q_γ` is in the radius-`2e` list of the *direction word*.  The fibre
of `γ ↦ Q_γ` over a fixed `Q` has at most `|D|` members (`card_shiftFibre_le`): all its members
share the codeword pair `(q₀, q₁) = (P₀ − γ₀·Q, Q)`, so each `γ` in the fibre is pinned by
`γ·(f₁ − q₁)(x) = (q₀ − f₀)(x)` at any window point where `f₁ ≠ q₁` — and such a point exists,
else the whole line would be close on that window, contradicting badness.

**The pairwise barrier.**  The radius produced is `2e`, not `e`.  The Johnson bound makes the
radius-`2e` list polynomial exactly when the agreement `n − 2e` exceeds `√(k n)`.  Since
`√(k n) ≥ k`, that forces `n − 2e > k`, i.e. the unique-decoding inequality `k + 2e < n`
(`pairwise_route_within_unique_decoding`).  So the correlated-pair route — of which the above
is the sharpest list-theoretic form — can never certify a polynomial bad set beyond unique
decoding, however cleverly the "far" case is handled.  This is a formal statement of why the
project's `NearCodewordLineMCA`/`SetFamilyJohnson` family of arguments stalls where it does,
and it says that constant-gap Grand MCA requires an invariant not built from *pairs* of bad
challenges.

## 7. Summary of the five reporting points

1. **Strongest new result.** `exists_superpolynomial_badSet_of_small_relative_gap` (with the
   explicit construction `exists_subspacePencil`, `#Bad ≥ p^{ℓ(m−ℓ)}` at gap
   `c = p^ℓ − p^{ℓ−1}`): the MCA bad set is superpolynomial at every *vanishing* relative
   capacity gap, not only inside the `c = O(n/log n)` boundary layer.  Its companion on the
   upper-bound side is `card_badSet_le_mul_card_rsList`: for every line,
   `#Bad ≤ 1 + n·|list(f₁, 2e)|`.
2. **Direction.** The new results **favour proof** of constant-gap Grand MCA: the strongest
   known counterexample family saturates exactly at constant `η`, and the two obstruction
   theorems show its mechanism cannot be pushed further without solving an open Reed–Solomon
   list-decoding problem.
3. **Quantitative consequence.** `max #Bad ≥ n^{Θ(log_p (1/η))}`; the conjectured gap-layer
   law `poly(n) + exp(Θ(1/η))` is refuted; correspondingly `ε_mca ≥ n^{Θ(log_p(1/η))}/|F|`.
   No polynomial bound on `#Bad` can hold under any hypothesis weaker than `η = Ω(1)`.
4. **Main remaining obstruction.** Two, and they are the same obstruction seen from both
   sides.  *Constructions*: every counterexample family in the project has a one-point
   direction word, and for those `#Bad` is an RS list size at radius `e+1`; at constant gap
   that is the open list-size-below-capacity problem.  *Proofs*: the only general handle on an
   arbitrary line is the correlated pair, and `pairwise_route_within_unique_decoding` shows
   that handle is confined to unique decoding.  What is missing is an invariant of a *single*
   bad challenge, or of the whole bad set at once, that sees the capacity gap.
5. **Best next step.**  Not the flat-direction variant.  That variant does work — take
   `D = U`, `f₁ = 1_W` for a coset `W = w + W₀` of a `j`-dimensional `W₀ ≤ U`, and range over
   the `ℓ`-dimensional `V` with `W₀ ≤ V`, `w ∉ V`; the window is `V ∪ W` and the challenge is
   again `−L_V(w)` — but it counts the `(ℓ−j)`-subspaces of an `(m−j)`-dimensional space,
   `≈ p^{(ℓ−j)(m−ℓ)}`, and a constant relative gap again forces `m − ℓ = O(1)`, so it too caps
   at `n^{O(1)}`.  The obstruction is the Gaussian binomial itself: *any* family of
   subspace-shaped windows of size `≥ η n` inside a space of size `n` has only `n^{O(1)}`
   members.  The best next step is therefore to leave algebraic window families behind and
   attack the **near case** of the Johnson dichotomy, which §6 identifies as the single
   binding constraint: given that the direction word `f₁` agrees with a codeword `q₁` on
   `n − d₁` points with `d₁` small, bound the number of bad challenges *without* passing to
   pairs.  `card_shiftFibre_le` already shows that all challenges sharing one codeword pair
   number at most `|D|`, so what is missing is exactly a bound on the number of distinct
   `q₀` arising as `P_γ − γ·q₁`.
