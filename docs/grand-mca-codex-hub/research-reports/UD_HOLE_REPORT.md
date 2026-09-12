# The strict unique-decoding hole (UD-hole): resolved, and quantified

## 0. Verdict

The project's open item **(UD-hole)** (recorded in `MCA_ROUTE_DECISION.md` §0) asked:

> does strict unique decoding `k + 2e < |D|` — together with a totally degenerate
> Welch–Berlekamp pencil — already force `#bad ≤ e + 1`?

**The answer is no, and it fails as badly as it possibly can.**

1. `#bad ≤ e + 1` is false under strict unique decoding: an explicit line over `ZMod 13`
   with `|D| = 8`, `k = 3`, `e = 2` has four bad parameters
   (`Root.CodingTheory.not_forall_card_badSet_le_succ_radius_of_strict_ud`), and it also has a
   totally degenerate Welch–Berlekamp pencil
   (`…_of_strict_ud_degenerate_pencil`).
2. More: **no** bound `#bad ≤ g(e)` in terms of the radius alone can hold under strict unique
   decoding.  At the *fixed* radius `e = 2` the number of bad parameters grows linearly in the
   block length: `Root.CodingTheory.CosetFamily.exists_strictUD_badSet_ge`.
3. The anchor theorem `Root.CodingTheory.card_badSet_le_succ_radius` needs
   `3e < |D| − k + 1`, i.e. `k + 3e ≤ |D|`; the new family lives exactly at
   `k + 3e = |D| + 1`, one step outside.  So the anchor hypothesis is **sharp**, and the
   unconditional dichotomy `Root.CodingTheory.card_badSet_le_or_card_lt`
   (`#bad ≤ e + 1` **or** `|D| < k + 3e`) is the exact shape of the truth.

Everything asserted as a theorem below is Lean-checked and `sorry`-free, with axioms
`propext`, `Classical.choice`, `Quot.sound` only.  Statements labelled *measurement* are
exact finite computations performed in `analysis/`, not Lean-verified.

## 1. The reformulation that drives everything

Write `C = RS_k(D)`.  Unfolding `Root.CodingTheory.IsBad`:

> `γ` is bad ⟺ there is `E ⊆ D` with `|E| ≤ e` such that `(f₀ + γ f₁)|_{D∖E}` is a codeword
> restriction while `f₁|_{D∖E}` is not.

(The branch "`f₀|_S` is not a codeword restriction" is subsumed: if `f₁|_S` and
`(f₀+γf₁)|_S` are codeword restrictions then so is `f₀|_S`.)  For each `E` the set of `γ`
that works is empty or a single point, because `γ ↦ syndrome((f₀+γf₁)|_{D∖E})` is affine with
nonzero linear part exactly when `f₁|_{D∖E}` is not a codeword restriction.  Hence

> **the bad set is computed exactly by looping over the `≤ Σ_{r≤e} C(|D|,r)` sets `E`.**

This is the routine `analysis/ud_hole_syndrome.py::Inst.bad_set`; it was cross-checked against
the literal Lean definition on 100 random lines with zero mismatches, and independently
re-verified for the `ZMod 13` witness by `analysis/ud_hole_witness_check.py`.

A normalisation is also available: any line with at least two bad parameters can be moved, by
subtracting a codeword pair, an affine reparametrisation of `γ` and a scaling, into the shape
`f₀ = u₁`, `f₁ = u₂ − u₁` with `u₁, u₂` of weight `≤ e`.  Every construction below is in that
normal form.

## 2. The counterexample (Lean)

`RequestProject/Root/CodingTheory/UniqueDecodingHoleWitness.lean`.

* `F = ZMod 13`, `D = {0,…,7}`, `k = 3`, `e = 2`.  `k + 2e = 7 < 8 = |D|` (strict unique
  decoding) and `3e = 6 = |D| − k + 1` (just outside the anchor hypothesis).
* `h₀ = 1·1_{0} + 6·1_{2}`, `h₁ = 12·1_{0} + 1·1_{1} + 7·1_{2} + 5·1_{4}`.
* Bad parameters `{0, 1, 5, 9}`, with error sets `{0,2}, {1,4}, {5,7}, {3,6}` — pairwise
  disjoint and covering `D`.
* `HoleWitness.wbDet_eq_zero_hole`: the Welch–Berlekamp pencil is totally degenerate, so the
  refutation applies to the pencil-strengthened form of the question too.

## 3. The general mechanism (Lean)

`RequestProject/Root/CodingTheory/CosetBadFamily.lean`.  Fix two disjoint nonempty blocks
`E₀, E₁ ⊆ D` and take the seed line

  `f₀ = 1_{E₀}`,   `f₁ = 1_{E₁} − 1_{E₀}`.

* `isBad_zero_of_seed`, `isBad_one_of_seed`: `γ = 0` and `γ = 1` are bad as soon as
  `|E₀|,|E₁| ≤ e` and `k ≤ |D| − |E₀| − |E₁|`.
* `isBad_of_block`: given a further block `E` (disjoint from `E₀ ∪ E₁`, `|E| ≤ e`) and a
  codeword `A` of degree `< k` which vanishes off `E₀ ∪ E₁ ∪ E`, is constant `= a` on `E₀`
  and `= b` on `E₁` with `a + b ≠ 0`, the parameter `b/(a+b)` is bad.

So each extra block equipped with such a polynomial buys one extra bad parameter.  The only
question is where such polynomials come from in abundance.

## 4. The multiplicative coset family (Lean) — the decisive result

`RequestProject/Root/CodingTheory/CosetBadFamilyMul.lean`.

Let `ω` be a primitive `e·m`-th root of unity in a finite field `F`, put

  `D = μ_{e·m}`,  `η = ω^e` (a primitive `m`-th root of unity),
  `E_j = { x ∈ D : x^e = η^j }` for `j < m`  (the cosets of `μ_e`),
  `k = |D| − 3e + 1`.

The key identity is that `∏_{x ∈ E_j}(X − x) = X^e − η^j` is **constant on every other
block**, because its value at `x` depends on `x` only through `x^e`.  Therefore

  `A_i = ∏_{j ∉ {0,1,i}} (X^e − η^j)`

has degree `e(m−3) = k − 1`, vanishes off `E₀ ∪ E₁ ∪ E_i`, and is constant on `E₀` (value
`a_i = ∏_{j∉{0,1,i}}(1 − η^j)`) and on `E₁` (value `b_i = ∏_{j∉{0,1,i}}(η − η^j)`).

Writing `P = ∏_{j∉{0,1}}(1−η^j)`, `Q = ∏_{j∉{0,1}}(η−η^j)` and `d_j = (1−η^j)/(η−η^j)`:

* `a_i, b_i, P, Q ≠ 0`;
* `a_i + b_i = 0 ⟺ d_i = −(P/Q)^{-1}…` — concretely `a_i + b_i ≠ 0` for **all but at most one**
  index `i`, because degeneracy pins `η^i = (Pη + Q)/(P + Q)` (and `P + Q ≠ 0` whenever a
  degenerate index exists);
* the parameters `γ_i = b_i/(a_i+b_i)` are pairwise distinct — `d_j` is a Möbius function of
  `η^j`, hence injective — and never `0` or `1`.

Theorem (`card_badSet_mulDomain_ge`, `sorry`-free):

> `IsPrimitiveRoot ω (e·m)`, `0 < e`, `3 ≤ m` ⟹
> `m − 1 ≤ #badSet (|D| − 3e + 1) e f₀ f₁` for the coset line on `E₀, E₁`.

Since `k + 2e = |D| − e + 1 < |D|` for `e ≥ 2`, **every** member of this family is strictly
uniquely decodable.  Concrete instantiations:

* `card_badSet_zmod13_ge`: `F = ZMod 13`, `D = μ₁₂`, `k = 7`, `e = 2` ⟹ `#bad ≥ 5`.
* `exists_strictUD_badSet_ge N`: for every `N` there is a prime `p`, `D = μ_{p−1}` of size
  `p − 1`, `k = p − 6`, radius `e = 2`, with `#bad ≥ N`.  (Take `p ≥ 2N+7`, `m = (p−1)/2`.)
  This uses only "there are infinitely many primes"; no Dirichlet input is needed because
  `2 ∣ p − 1` for every odd prime.

### Measurements supporting the family

`analysis/ud_hole_family.py`, `analysis/ud_hole_syndrome.py`.  The **exact** bad set of the
coset line was computed for

| `(q, e, m)` | `n = em` | `k` | `#bad` |
|---|---|---|---|
| (13,2,3) | 6 | 1 | 3 |
| (17,2,4) | 8 | 3 | 4 |
| (11,2,5) | 10 | 5 | 4 (one degenerate index) |
| (13,2,6) | 12 | 7 | 6 |
| (29,2,7) | 14 | 9 | 7 |
| (17,2,8) | 16 | 11 | 8 |
| (31,3,5) | 15 | 7 | 5 |
| (19,3,6) | 18 | 10 | 6 |
| (41,4,5) | 20 | 9 | 5 |
| (19,2,9) | 18 | 13 | 8 (one degenerate index) |

In every case the predicted set `{0, 1} ∪ {γ_i}` equalled the exact bad set.  A separate cheap
scan over 927 configurations (`q < 400`, `e ≤ 8`, `3 ≤ m < 30`) confirmed that `a_i, b_i ≠ 0`,
that the `γ_i` are always pairwise distinct and never `0` or `1`, and that **at most one**
index degenerates — exactly the structure the Lean proof exploits.

## 5. What is now known about the size of the bad set

*Upper bounds (Lean).*

* `card_badSet_le`: `#bad ≤ |D|` unconditionally.
* `card_le_of_pencil` (`BadSetPencilBound.lean`): **radius-free and relative** — if one single
  polynomial pencil `q₀ + γ q₁` explains every parameter of an arbitrary set `B` on a witness
  set that fails for the whole line, then `#B ≤ e + 1`, with no hypothesis relating `k`, `e`
  and `|D|`.  This bounds one *pencil class* of bad parameters; `card_badSet_le_of_pencil` is
  the special case `B = badSet k e f₀ f₁`.
* `card_badSet_le_or_card_lt`: unconditionally, `#bad ≤ e + 1` **or** `|D| < k + 3e`.
* `card_badSet_le_succ_radius_of_le`: hence `k + 3e ≤ |D| ⟹ #bad ≤ e + 1`.

*Lower bounds (Lean).*

* `card_badSet_mulDomain_ge`: `#bad ≥ |D|/e − 1` at `k = |D| − 3e + 1`, i.e. exactly at
  `|D| = k + 3e − 1`, the first place where the dichotomy allows failure.

So the transition is completely located: at `|D| ≥ k + 3e` the bad set has at most `e + 1`
elements; one step earlier it can already have `≈ |D|/e`.

*Exact maxima over all lines (measurement, `analysis/ud_hole_exhaustive.py`, `p = 13`,
`e = 2`, `c = |D| − k = 5`).*

| `|D|` | `k` | exact max `#bad` | `⌊|D|/e⌋` |
|---|---|---|---|
| 6 | 1 | 3 | 3 |
| 7 | 2 | 3 | 3 |
| 8 | 3 | 4 | 4 |
| 9 | 4 | 4 | 4 |
| 10 | 5 | 5 | 5 |

## 6. Smallest remaining obstruction

The natural guess for a matching upper bound is **false**, and cheap experiments killed it
before any formalisation effort was spent.

> **Refuted (measurement).** `#bad ≤ ⌊|D|/e⌋` fails, and so does `#bad ≤ ⌈|D|/e⌉`.
> Over `F = ZMod 13`, `D = {0,…,7}`, `k = 1`, `e = 3` — strict unique decoding, since
> `k + 2e = 7 < 8` — the line
> `f₀ = (4,7,7,4,8,7,8,7)`, `f₁ = (11,0,0,1,6,0,2,0)`
> has bad set `{2,3,5,6}`, i.e. `#bad = 4 > 3 = ⌈8/3⌉`.  The four error sets are
> `{0,3,6}, {0,4,6}, {3,4,6}, {0,3,4}` — the four 3-subsets of `{0,3,4,6}`.
> A second violation of the floor form: `q = 11`, `D = μ₁₀`, `k = 3`, `e = 3`, `#bad = 4 > 3`.
> (`analysis/ud_hole_cap_probe.py` and the verification in this report's §5 tooling.)

**What the two extremes actually are.**  The refuting example is a *single pencil class* of the
maximal size `e + 1 = 4`; the coset family of §4 is `m` classes of size `1` each.  That
suggests the correct statement, which is the real remaining obstruction:

Fix `c = |D| − k` and write `s = 3e − c − 1`.  Let `γ₁` be bad with error set `E₁` and, for
each other bad `γ`, put `v_γ = (u_γ − u_{γ₁})/(γ − γ₁)`, a weight-`≤ 2e` representative of
`f₁ mod C`.  Then:

* `v_γ = v_{γ'}` ⟹ `γ` and `γ'` are explained by *one* polynomial pencil `q₀ + γ q₁` with
  `q₀, q₁ ∈ C`; by `card_badSet_le_of_pencil` a whole such class has at most `e + 1` members.
* `v_γ ≠ v_{γ'}` ⟹ `v_γ − v_{γ'}` is a nonzero codeword supported in `E_γ ∪ E_{γ'} ∪ E₁`,
  so `|E_γ ∪ E_{γ'} ∪ E₁| ≥ c + 1`, hence `|E_γ ∩ E_{γ'}| ≤ s`.

> **Conjecture (class–packing bound).**  In strict unique decoding,
> `#bad ≤ (e + 1) · M(|D|, e, 3e − c − 1)`,
> where `M(n, e, s)` is the largest number of `e`-subsets of an `n`-set with pairwise
> intersections of size at most `s` (and `M(n, e, s) = 1` when `s < 0`).

This is consistent with everything known: for `c ≥ 3e` it gives `s < 0`, `M = 1`, and recovers
the anchor bound `#bad ≤ e + 1`; for `c = 3e − 1` it gives `s = 0`, `M = ⌊|D|/e⌋`, and the
coset family attains `⌊|D|/e⌋` of the allowed `(e+1)⌊|D|/e⌋`; the `ZMod 13`, `e = 3`, `k = 1`
example has `s = 1` and sits at `e + 1` inside one class.

The two Lean-level gaps are (i) a *relative* version of `card_badSet_le_of_pencil` that bounds
the bad parameters explained by one pencil rather than requiring the hypothesis for the whole
bad set, and (ii) the packing bound `M(n, e, s)` — for `s = 0` this is just "disjoint `e`-sets",
which is elementary.

## 7. Best next theorem / experiment

**Theorem to attempt (in this order).**

1. ~~*Relative pencil bound.*~~ **Done** — `Root.CodingTheory.card_le_of_pencil`.
2. *Class separation.*  If `γ, γ'` are bad and not explained by a common pencil, then
   `|E_γ ∪ E_{γ'} ∪ E_{γ''}| ≥ |D| − k + 1` for any third bad `γ''` — this is the argument
   already present in `card_badSet_le_or_exists_triple`, restated so that it yields the
   intersection bound `|E_γ ∩ E_{γ'}| ≤ 3e − c − 1`.
3. *The case `c = 3e − 1`.*  Combining (1) and (2) with the elementary disjointness packing
   bound gives `#bad ≤ (e+1)·⌊|D|/e⌋` on exactly the row where the coset family lives — a
   proved upper bound within a factor `e + 1` of the proved lower bound `|D|/e − 1`.

**Experiment to run first.**  Determine the exact maximum of `#bad` for
`(|D|, k, e) = (12, 7, 2)` on `μ₁₂ ⊂ ZMod 13` (the coset family attains `6`; the conjecture
allows `18`).  If the exact maximum is `6`, the factor `e + 1` in the conjecture is an artefact
and the sharp bound is plausibly `⌊|D|/e⌋` *for `c = 3e − 1` only*, which would be the clean
companion to §4.

## 8. Files

| file | content |
|---|---|
| `RequestProject/Root/CodingTheory/UniqueDecodingHoleWitness.lean` | the `ZMod 13` counterexample and the two refutation theorems |
| `RequestProject/Root/CodingTheory/BadSetPencilBound.lean` | radius-free pencil bound; unconditional `e+1` / `k+3e` dichotomy |
| `RequestProject/Root/CodingTheory/CosetBadFamily.lean` | the seed line and the per-block bad parameter |
| `RequestProject/Root/CodingTheory/CosetBadFamilyMul.lean` | the multiplicative coset family, `#bad ≥ |D|/e − 1`, unboundedness at `e = 2` |
| `analysis/ud_hole_syndrome.py` | exact bad-set routine (validated against the Lean definition) |
| `analysis/ud_hole_algebraic.py` | prescribe error sets and parameters, solve the linear system |
| `analysis/ud_hole_exhaustive.py` | complete enumeration of all lines for one row |
| `analysis/ud_hole_family.py` | the coset family, built and verified exactly |
| `analysis/ud_hole_witness_check.py` | independent brute-force check of the `ZMod 13` witness |
| `analysis/ud_hole_cap_probe.py` | hill-climbing probe that refuted the `|D|/e` cap of §6 |
| `analysis/ud_hole_cap_refutation.py` | exact recomputation of the refuting witness and its error sets |
