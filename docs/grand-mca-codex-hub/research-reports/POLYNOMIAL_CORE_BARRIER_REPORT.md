# POLYNOMIAL_CORE_BARRIER_REPORT

Scope: no Lean file created or modified, no axiom, no `sorry`, no sweep, no refactor.
All statements are labelled **PROVED-IN-LEAN** (kernel-checked in this repository, name given),
**PROVED-HERE** (complete paper proof in this document), or **CONJECTURE**.
Notation: `n = |D|`, `k` = dimension, `e` = radius, `ρ = k/n`, `δ = e/n`,
`Bad = badSet k e f₀ f₁`, `Good = goodZ k e f₀ f₁ ⊇ Bad`.

---

## 1. MINIMAL CORE

There are **two** independent `#Bad ≤ e+1` theorems in the project, and the strongest one is
*not* the double count. The minimal core is the determinantal one.

**CORE (PROVED-IN-LEAN, `card_badSet_le_of_wbDet_ne_zero`, `natDegree_wbDet_le`).**

* **OBJECT counted.** Parameters `γ ∈ F` at which the line word `f₀ + γf₁` is `e`-close to
  `RS[k]` (i.e. `Good`; `Bad ⊆ Good`).
* **RESOURCE consumed.** One root of one fixed nonzero univariate polynomial
  `Δ(Z) = wbDet k e f₀ f₁ ρ ∈ F[Z]`, the maximal minor of the Welch–Berlekamp pencil
  (rows `x ∈ D`, columns = the `e+1` locator coefficients + the `k+e` numerator coefficients,
  row `x`: `Λ(x)·(f₀x + Z·f₁x) = Q(x)`).
* **WHY consumption is injective/bounded.** `γ` close ⇒ a nonzero WB pair exists at `γ`
  (`exists_wbPair_of_isCloseOn`) ⇒ the specialised pencil has nontrivial kernel ⇒ **every**
  maximal minor vanishes at `γ` (`wbDet_eval_eq_zero_of_isCloseOn`). Distinct `γ` are distinct
  roots: injectivity is the *degree principle* (a nonzero polynomial over a field has at most
  `deg` roots), nothing combinatorial.
* **TOTAL RESOURCE `≤ e+1`.** `Z` occurs only in the `e+1` locator columns and only linearly,
  so `deg Δ ≤ e+1`. The resource is literally **the dimension `e+1` of the locator space
  `{Λ : deg Λ ≤ e}`**.

So: `STRUCTURE` = *the pencil of the line is nonsingular over `F(Z)`* ⟹ `INVARIANT` =
`deg_Z(maximal minor) ≤ e+1` ⟹ `#Good ≤ e+1`, a fortiori `#Bad ≤ e+1`.
(The Lean statement is phrased for `Bad`; the same proof gives `Good` — PROVED-HERE, immediate
from `wbDet_eval_eq_zero_of_isCloseOn`.)

**The double count is a shadow of this.** In `card_badSet_le_succ_radius` /
`card_badSet_le_succ` the resource pool is `u = n − |T| ≤ 2e` (positions off the common
agreement set of the *one* pair `(q₀,q₁)` produced by two good parameters), each bad `γ`
consumes `≥ max(1, u−e)` of it, disjointly, giving `c ≤ u` and `c(u−e) ≤ u`, whence
`c ≤ max_u min(u, u/(u−e)) = e+1` at `u = e+1`. Private positions are surrogates for
non-roots of error locators; the number `e+1` arises there from an optimisation, in the core
it is a dimension. Both are the *same* resource, counted twice.

---

## 2. TRUE BARRIER

Hypotheses of the core: `1 ≤ k` (degenerate), and **`H`: some maximal minor of the WB pencil
is `≢ 0`**, i.e. the pencil has full column rank `k+2e+1` over `F(Z)`. `H` is the only
mathematically essential condition; removing it destroys the argument *and* the conclusion.

* `k + 2e < n` is **implied by `H`** (a minor with a repeated row vanishes), so it is
  **necessary, never assumed**, and it is **not sufficient**: `StrictWindowWitness`
  (`F₁₁`, `n = 8`, `k = 3`, `e = 2`, so `k+2e = 7 < 8`) has `#Bad ≥ 4 > 3 = e+1` and a totally
  degenerate pencil (`StrictWindowWitness.wbDet_eq_zero`,
  `not_forall_card_badSet_le_succ_radius_strict_window`, both PROVED-IN-LEAN).
* At `k + 2e ≥ n` the pencil is singular for **every** word
  (`exists_nonzero_wbVector_of_card_lt`), so the mechanism is unconditionally vacuous there,
  and the bound is not merely unprovable but **false**: `GapWitness` (`F₅`, `n = 4`, `k = 2`,
  `e = 1`, `k+2e = n`) has `#Bad ≥ 4 = n`, the trivial maximum.
  `δ = (1−ρ)/2` is therefore a **hard wall** for the polynomial core.

**Failure locus of `H` (PROVED-HERE, structure of the singular branch).** Suppose all maximal
minors vanish, i.e. there is `0 ≠ (Λ,Q)` over `F[Z]` with `Λ(Z,x)(f₀x + Z f₁x) = Q(Z,x)` for
all `x ∈ D`, `deg_X Λ ≤ e`, `deg_X Q < k+e`. If `Λ ≡ 0` then `Q(·,x) = 0` on `D` and
`deg_X Q < k+e < n`, so `Q ≡ 0`: contradiction. Write `Λ = Σ_{i=a}^{b} Z^i Λ_i(X)` with
`Λ_a, Λ_b ≠ 0`. Comparing coefficients of `Z^a` and of `Z^{b+1}`:

  `Λ_a(x)·f₀(x) = Q_a(x)`  and  `Λ_b(x)·f₁(x) = Q_{b+1}(x)`  for all `x ∈ D`.

**Both coordinates of the line are `(k+e, e)`-rational on `D`.** This is a rigid, codimension
`≥ n − k − 2e` condition (at most `|F|^{k+2e+1}` such words out of `|F|^n`), and it is exactly
the class `wbDet_eq_zero_of_rationalLine` already isolates. Conversely
`wbDet_eq_zero_of_correlatedAgreement`: correlated agreement at radius `e` also kills the
pencil — the two known ways of failing `H` are "the line is already jointly explained" and
"the line is rational".

---

## 3. ESSENTIAL vs PROOF-ARTIFACT

| hypothesis | verdict |
|---|---|
| `H` = WB pencil nonsingular over `F(Z)` | **ESSENTIAL** (defines the mechanism; failure is a rigid rational structure) |
| `k + 2e < n` (`δ < (1−ρ)/2`) | **NECESSARY for `H`, NOT sufficient** (StrictWindow witness). Not an assumption of the core — a consequence |
| `k + 3e ≤ n` (`δ ≤ (1−ρ)/3`; `δ ≤ 1/6` at `ρ = ½`) | **PROOF ARTIFACT of the double count.** It is used *only* as unisolvence `n − 3e ≥ k` in `eval_eq_of_card_agreement_ge`, to force every local witness to equal `q₀+γq₁`. It is neither implied by nor implies `H` (correlated-agreement lines satisfy it and violate `H`). It *is* sharp for that route: both kernel-checked counterexamples sit at exactly `k+3e = n+1` |
| field / MDS (Reed–Solomon) | ESSENTIAL but background (degree principle + unisolvence) |
| primality of `F`, non-collinear witness selection (used by the projected route) | irrelevant here; the core needs neither |

**The frequently quoted wall `δ = 1/6` at `ρ = ½` is an artifact.** The core mechanism is
alive on the whole strip `δ < 1/4`, i.e. across the entire target band `δ ∈ (1/6, 1/4]`,
for every line outside the rational locus.

---

## 4. EXTENSION or COUNTEREXAMPLE — a dichotomy, plus the exact obstruction

**DICHOTOMY (PROVED-HERE; branch (i) PROVED-IN-LEAN).** Let `k + 2e < n`. For every line
`(f₀,f₁)` exactly one holds:

* **(i) generic branch** — the WB pencil is nonsingular; then `#Good ≤ e+1`, hence
  `#Bad ≤ e+1`;
* **(ii) rigid branch** — the pencil is singular; then there are nonzero `Λ', Λ''` of degree
  `≤ e` and `A, B` of degree `< k+e` with `Λ'f₀ = A` and `Λ''f₁ = B` pointwise on `D`; in
  particular `f₀`, `f₁` agree with rational functions of type `(k+e, e)` on `≥ n − e`
  positions each.

This is the answer to "what mathematically causes `#Bad ≤ e+1`": *the degree of one
determinant*; and to "where is its edge": *the rational/Padé locus*, not a `δ`-threshold.

**Counterexamples are confined to branch (ii) and are small.** Both witnesses have `e ≤ 2`,
and both attain only `#Bad = e+2`. Padding (PROVED-HERE: `D' = D ⊔ Y`, `k' = k+m`, `e' = e`,
`f'_i = c·f_i` on `D` with `c = ∏_{y∈Y}(X−y)`, `f'_i = 0` on `Y`, over an extension field) maps
each witness to an instance with the same `#Bad` and `k' + 2e' = n'`, for arbitrarily large
`n'`; but it leaves `e` fixed, so `ρ' → 1`, `δ' → 0`. **No known counterexample has `e ≥ 3`,
and none is known at fixed `ρ = ½` with large `n`.** The strict-window normal form
`D = U ⊔ T`, `|U| = 2e`, `|T| = k+1` documented in `StrictWindowRefutation.lean` even suggests
the opposite: bad directions there are the pairs `{s,s'} ⊆ T` with `w_s − w_{s'} ∈
span(f₀|U, f₁|U)` (`w_s(x) = 1/(x−s)`), and total nonsingularity of the Cauchy matrix forbids
three disjoint such pairs once `2e ≥ 6`, plus at most `3` in one coset and at most `2`
zero-witness directions. Heuristically branch (ii) at the edge yields `#Bad = O(1)` for
`e ≥ 3` — the violations are a small-`e` phenomenon, not a blow-up.

---

## 5. STRONGEST POLYNOMIAL-SCALE THEOREM CANDIDATE

**CONJECTURE (Padé descent).** For all `k + 2e < n`: `#Bad ≤ (e+1)(1+s)` with
`s = max(0, k+3e−n) ≤ e−1`; in particular `#Bad = O(e²)` on the whole strip `δ < (1−ρ)/2`,
and `#Bad ≤ e+1` when `s = 0`.

Mechanism (why it is the natural continuation, not a new theory): in branch (ii) substitute
`f₀ = A/Λ'`, `f₁ = B/Λ''` on the `≥ n−2e` positions where `Λ'Λ'' ≠ 0`. A bad `γ` with locator
`Λ^γ` then satisfies `Λ^γ·(Λ''A + γΛ'B) ≡ Λ'Λ''·Q^γ` on that set; both sides have degree
`≤ k+3e−1`, so the difference is `V·E` with `V` the vanishing polynomial of the set and
`deg E ≤ s`. For `s = 0` this is an identity and one recovers the `k+3e ≤ n` theorem; for
`s > 0` it is again a *linear* condition in `γ`, i.e. a second determinantal count with `s+1`
extra degrees of freedom. This is exactly Kronecker's reduction of a singular pencil by its
minimal indices, specialised to Welch–Berlekamp. Consistency: `s = 1` for both witnesses, and
both have `#Bad = 4 ≤ (e+1)·2`. It is compatible with every kernel-checked datum in the
project (`badset_wb_regime_probe`, `mca_small_field_check`) — no numerical claim is used as
evidence for the conjecture.

Routes rejected on sight, per the mission's filter: Johnson/list-size (`#Bad ≤ n·Λ`),
occupancy/binomial (`2·C(n−1,2e−1)−1`, deficit ≈ `10⁶` bits per `STRENGTH_GATE_REPORT.md`),
and anything whose natural output carries `|L|`, `C(n,Θ(e))` or `2^{Θ(n)}`.

---

## 6. EXPECTED `#Bad` SCALE

| regime (`ρ = ½`) | status | `#Bad` |
|---|---|---|
| `δ ≤ 1/6` (`k+3e ≤ n`) | PROVED-IN-LEAN | `≤ e+1` (`≈ 2¹⁸` at `n = 2²⁰`) |
| `1/6 < δ < 1/4`, pencil nonsingular | PROVED-IN-LEAN (conditional on the rank test) | `≤ e+1` |
| `1/6 < δ < 1/4`, pencil singular | CONJECTURE §5 | `O(e²) ≈ 2³⁶` at `n = 2²⁰`; known lower bound `e+2` |
| `δ ≥ 1/4` (`k+2e ≥ n`) | mechanism dead, bound **false** | `= n` attained (`GapWitness`) |

Both live rows clear the operational test `#Bad ≤ 2¹²⁸` at `n = 2²⁰` by ≥ 90 bits, hence
`ε_mca ≤ 2⁻¹²⁸` for `|F| ≥ 2¹⁴⁶` resp. `2¹⁶⁴`. The transition
`#Bad = O(e) ⟶ uncontrolled` is therefore **not** at `δ = 1/6`; it is at
`δ = (1−ρ)/2`, where full column rank of a `n × (k+2e+1)` pencil becomes impossible for
dimension reasons. That single sentence is the structural reason asked for.

---

## 7. RANK AND ONE NEXT MISSION

**Verdict: C — STRUCTURAL DICHOTOMY FOUND.**

  poly-size `Bad` (`≤ e+1`, degree of one determinant)
  **OR** rigid exceptional structure (both coordinates `(k+e,e)`-rational on `D`),

valid on the whole strip `k + 2e < n`, with the hard wall at `k + 2e = n` (dimension count,
counterexample attaining `#Bad = n`).

**NEXT MISSION (one).** *Close branch (ii) by Kronecker/Padé descent.* Take a minimal-degree
kernel vector of the singular WB pencil, split off its minimal-index block, and prove the
residual bound `#Bad ≤ (e+1)(1 + max(0, k+3e−n))` — equivalently, show that the `s`-slack
identity of §5 is a nondegenerate linear system in `γ` unless the line degenerates further, and
run the descent on `s`. Success closes `ρ = ½`, `δ ∈ (1/6, 1/4)` unconditionally with a
polynomial `#Bad`; failure must produce a line with `e ≥ 3`, `k+2e < n` and `#Bad > (e+1)(1+s)`,
which would be the first genuine large-`e` obstruction and would relocate the wall from
`(1−ρ)/2` down to the rational locus.
