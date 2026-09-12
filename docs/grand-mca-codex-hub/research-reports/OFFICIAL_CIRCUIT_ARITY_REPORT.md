# Official split-locator circuits of arity four — mechanism, small model, deployed row

Continuation of the `HIGHER-ARITY-DEPENDENCY` verdict of
`RESIDUAL_DEPENDENCY_ARITY_REPORT.md`.  The arity-3 direction and the ambient `2w`-dimensional
linear-algebra direction are **not** reopened here.

---

## 0. Claim ledger

| # | Claim | Status | Where |
|---|-------|--------|-------|
| C1 | Split-locator structure forbids circuits of arity `> 3` (route (i)) | **REFUTED**, at every width `w ≥ 2` and every locator degree `e` | `official_arity_four_circuit` |
| C2 | An exact *official* circuit of arity 4 exists in a small model | **PROVED** (`|D| = 12`, `e = 4`, `w = 3`, over `𝔽₁₃`) | `Example13.official_arity_four_circuit_example` |
| C3 | The class equation transfers from `w+1` point conditions to a fixed number of label conditions | **PROVED** (12 label equations, independent of `w`, `e`, the field) | `official_arity_four_circuit_of_labels` |
| C4 | The transfer conditions are satisfiable at the **deployed** row | **PROVED** — a full official arity-4 circuit at `n = 2²¹`, `k = 2²⁰`, `e = 978944`, `w = 69632` over `𝔽_p`, `p = 2³¹−2²⁴+1` | `Deployed.official_arity_four_circuit_deployed` |
| C5 | Route (iii): the challenge count is bounded despite arity `> 3` | **PROVED for pencil-shaped families**: at most `3` dependency-free challenges, independent of `w` | `pencil_family_card_le_three` |
| C6 | Grand MCA claim | **NOT MADE.**  See §6. | — |

All Lean results are `sorry`-free; `#print axioms` for every load-bearing declaration prints
`[propext, Classical.choice, Quot.sound]` — no `native_decide`, no new axiom
(`RequestProject/OfficialCircuitArityAxiomAudit.lean`,
`RequestProject/OfficialCircuitDeployedAxiomAudit.lean`).

---

## 1. Separation of the two kinds of example

The two must not be conflated, and they live in different files.

* **Generic (old, not official).**  `RequestProject/Root/CodingTheory/ResidualDependencyArity.lean`
  contains an arity-4 family over `ZMod 5` at width `2` given by *bare vectors*: there are no
  words `f₀, f₁`, no domain `D`, no split locators, and no syndrome equations.  It refutes only
  the abstract gate hypothesis.
* **Official (this work).**  Everything in
  `RequestProject/Root/CodingTheory/OfficialCircuitArity.lean`,
  `…/OfficialCircuitArityExample.lean`, `…/OfficialCircuitCosetTransfer.lean` and
  `…/OfficialCircuitArityDeployed.lean` is stated inside the official framework: a domain
  `D ⊆ F`, two words `f₀, f₁`, the official syndrome functional `gsynd`, split locators
  `Q_E = ∏_{x∈E}(X−x)` with `E ⊆ D` monic of degree `e` dividing `Xⁿ−1`, the official locator
  system `LocatorSystem`, official nondegeneracy `LocatorNondeg`, and membership in the official
  challenge set `locatorChallengeSet`.

---

## 2. The mechanism: a three-class divided-difference word

Let `T ⊆ D` with `|T| = w+1` and let

    λ_x = ∏_{y ∈ T, y ≠ x} (x − y)⁻¹

be its divided-difference weights, so `∑_{x∈T} λ_x x^j = 0` for every `j < w`.  Split `T` into
three classes, give class `s` a scalar `r s` (the three distinct) and each point a nonzero scalar
`κ x`.  The two words are the point-mass words with masses `λ_x/κ_x` and `−r(cls x)·λ_x/κ_x`.

The **only** hypothesis on the four split locators is the *class equation*

    (γ i − r (cls x)) · Q_i(x) = θ i · κ x        for all x ∈ T.                     (CE)

Under (CE):

* the official locator system holds at `γ i` for `Q_i` — the sum telescopes to
  `θ i · ∑_{x∈T} λ_x x^j = 0`;
* the syndrome vector is `v i = θ i · ∑_s z_s/(γ i − r_s)` with
  `z_s(j) = ∑_{x ∈ T_s} λ_x x^j` and `z₀ + z₁ + z₂ = 0`, hence the **pencil shape**

      v i = β i • (γ i • u + u'),   β i ≠ 0,   u, u' independent;

* a family of that shape is a circuit of arity exactly four: the four joint vectors
  `(v i, γ i • v i)` are dependent with all coefficients nonzero and no proper subfamily is
  dependent.

Three classes are essential: with two classes all `v i` are collinear and the arity drops to
three.  This is the structural reason the arity-3 barrier is not a barrier.

---

## 3. Small model (C2)

`F = 𝔽₁₃`, `D = μ₁₂`, `n = 12`, `k = 5`, `e = 4`, `w = 3`;
`T = {1,2,3,4}` with classes `{1,2} ↦ 0`, `{3} ↦ 1`, `{4} ↦ 2`; `r = (0,6,1)`;
`κ : 1↦1, 2↦12, 3↦1, 4↦11`; locators
`E₀ = {5,6,7,10}`, `E₁ = {5,8,10,12}`, `E₂ = {6,7,8,12}`, `E₃ = {6,9,10,11}`;
challenges `γ = (3,12,5,2)`, constants `θ = (3,10,6,11)`.
(CE) is checked by kernel evaluation.  Search script:
`analysis/official_arity_four_small_instance.py`.

---

## 4. The transfer conditions (C3)

Verifying (CE) point by point costs `w+1` conditions — at the deployed row `69633` of them.  The
transfer collapses this.

Fix `d ∣ n` and read `D = μ_n` through the power map `x ↦ x^d`, whose image is the label group
`μ_{n/d}`.  Take three labels `Lab 0, Lab 1, Lab 2` carrying the three classes, and locators

    Q_i = Q_G · ∏_{τ ∈ S_i} (X^d − τ),        S_i ⊆ μ_{n/d} \ {Lab 0, Lab 1, Lab 2},

i.e. erasure sets `E_i = G ⊔ ⋃_{τ ∈ S_i} Fib τ` made of a **common** part `G` and full fibres of
the power map.  The point (`qPoly_fibre`) is that a full fibre is the root set of `X^d − τ`, so
its split locator *is* `X^d − τ` and its value at `x` depends only on the label `x^d`.  Hence for
`x` in class `s`

    Q_i(x) = κ x · Λ_i(Lab s),     κ := Q_G|_T,     Λ_i(Y) = ∏_{τ ∈ S_i}(Y − τ),

and (CE) becomes the `12` **label equations**

    (γ i − r s) · Λ_i(Lab s) = θ i,     i = 0..3,  s = 0,1,2.                        (LE)

`official_arity_four_circuit_of_labels` proves: (LE) + the bookkeeping (fibres of size `d`,
erasure sets of size `e`, `G` disjoint from `T` and from the fibres) ⟹ official arity-4 circuit.
Nothing in it depends on `w`, `e`, the domain size or the field.

**Solving (LE).**  Eliminate `θ i` and `γ i`.  With `b_{i,2} = Λ_i(Lab 0)/Λ_i(Lab 1)` and
`b_{i,3} = Λ_i(Lab 0)/Λ_i(Lab 2)`, (LE) is solvable for `(γ i, θ i)` iff

    b_{i,2}(r₃ − r₁) + b_{i,3}(r₁ − r₂) = r₃ − r₂ ,

a line `αX + βY = δ` with `α + β = δ`: a line **through `(1,1)`**, and nondegeneracy of the `r`'s
forces `α, β, δ ≠ 0`, i.e. the line is neither horizontal nor vertical.  Therefore

> **Transfer condition.**  The four points `P_i = (b_{i,2}, b_{i,3}) ∈ F²` must be collinear with
> `(1,1)` on a non-axis-parallel line.

Equivalently, with the single scalar invariant

    σ(S) = (b₃ − 1)/(b₂ − 1) = (a₁ − a₃)a₂ / ((a₁ − a₂)a₃),    a_s = Λ(Lab s),

the condition is `σ(S₀) = σ(S₁) = σ(S₂) = σ(S₃)`, with `σ ∉ {0,1}`; and then one may take
`r = (0, 1, σ)`, `γ i = 1/(1 − b_{i,2})`, `θ i = Λ_i(Lab 0)·γ i`.

So the transfer test is a **four-way collision search** for one `F`-valued invariant.  A
degree-1 `Λ_i` provably cannot work (the image of `S ↦ (b₂,b₃)` is then a conic, which a line
meets in at most two points), so `|S_i| ≥ 2` is forced.

---

## 5. The deployed row is reached (C4)

Deployed parameters (from `SPLIT_LOCATOR_GATE_AUDIT_REPORT.md`):

    p = 2³¹ − 2²⁴ + 1 = 2130706433,   p − 1 = 2²⁴ · 127
    n = |D| = 2²¹ = 2097152,  k = 2²⁰ = 1048576,  e = 978944,  w = n − k − e = 69632.

Since `2²¹ ∣ p − 1`, `μ_{2²¹} ⊂ 𝔽_p`.  Choice of the transfer data:

* `d = 2¹⁵ = 32768`, so `3d = 98304 ≥ w + 1 = 69633` and there are `N' = n/d = 64` labels;
* `ζ = 3^{(p−1)/2²¹} = 1213133211` (order `2²¹`, proved by the 21-step squaring chain),
  `η = ζ^{2¹⁵} = 1548376985` (order `64`); labels `Lab s = η^s`, `s = 0,1,2`;
* `|S_i| = m = 8`, so `deg ∏(X^d − τ) = 8·32768 = 262144` and `deg G = 978944 − 262144 = 716800`,
  which fits: `n − (w+1) − |⋃S_i|·d = 2097152 − 69633 − 26·32768 = 1175551 ≥ 716800`.

The four label sets (as `η`-exponents), found by the collision search
`analysis/official_arity_four_deployed_lean_data.py` (`6·10⁷` random 8-subsets of the `61`
non-class labels, `497` values of `σ` of multiplicity `≥ 4`):

    S₀ = η^{5, 7, 10, 23, 25, 28, 46, 63}
    S₁ = η^{7, 13, 24, 33, 43, 46, 61, 62}
    S₂ = η^{10, 16, 29, 48, 50, 51, 53, 55}
    S₃ = η^{16, 19, 22, 37, 42, 55, 60, 62}

    σ = 185237647,   r = (0, 1, 185237647),
    γ = (152355628, 1700501136, 955669506, 608650944),
    θ = (1755007086, 806241498, 433828928, 492358614).

`Deployed.official_arity_four_circuit_deployed` proves, from these numerals alone (the twelve
label equations are discharged by kernel evaluation), that there exist four erasure sets of size
exactly `e = 978944` — hence four monic degree-`e` split locators dividing `X^{2097152} − 1` — and
two words `f₀, f₁` such that

* all four *distinct* challenges lie in `locatorChallengeSet 2²⁰ 978944 f₀ f₁`,
* all four locators are `LocatorNondeg`-nondegenerate and the syndrome vectors are nonzero,
* the four joint vectors carry a dependency with **all four** coefficients nonzero,
* and **no three** of them carry a dependency.

**Caveat, stated plainly.**  The deployed protocol samples challenges from `𝔽_{p⁶}`.  The four
challenges constructed here lie in the prime subfield `𝔽_p ⊂ 𝔽_{p⁶}` and the theorem is stated
over `𝔽_p`.  All deployed *combinatorial* parameters (`n`, `k`, `e`, `w`, root-of-unity domain)
are attained exactly.

---

## 6. What is **not** claimed

* **No Grand MCA claim is made.**  What is established is that the arity-3 hypothesis fails at the
  deployed parameters — an obstruction to one particular route, not a proof of the Grand MCA
  statement and not a refutation of it.
* Nothing is claimed about official families that are not of the pencil shape.
* Route (iii) is settled only for pencil-shaped families (§7); no bound is obtained for a general
  official family beyond the pre-existing `dependency_free_subfamily_card_le ≤ w` and the
  circuit-length bound `≤ 2w+1`.
* The general-index (`ι` arbitrary) version of the master theorem, which would let §7 be applied
  to an official family of arbitrary size directly rather than through its pencil shape, has not
  been formalised.

---

## 7. Route (iii): a rank bound that survives arity four (C5)

For a pencil-shaped family `v i = β i • (γ i • u + u')` over any finite index set, a
challenge-compatible dependency `c` is exactly the vanishing of the three moments

    ∑ᵢ cᵢβᵢ ,    ∑ᵢ cᵢβᵢγᵢ ,    ∑ᵢ cᵢβᵢγᵢ² ,

so the joint family has rank at most three.  `pencil_family_card_le_three` concludes: a
pencil-shaped family with **no** nonzero challenge-compatible dependency has at most `3` members
— independently of `w`, of `e` and of the field.  For the families the split-locator mechanism
produces this improves the dependency-free bound from `w` to `3`; at the deployed row, from
`69632` to `3`.

So high arity and a small challenge count coexist: the arity is `4` because the rank is `3`, not
because the family is large.

---

## 8. Files

Lean:

* `RequestProject/Root/CodingTheory/OfficialCircuitArity.lean` — mechanism and master theorem.
* `RequestProject/Root/CodingTheory/OfficialCircuitArityExample.lean` — small model (§3).
* `RequestProject/Root/CodingTheory/OfficialCircuitCosetTransfer.lean` — transfer theorem (§4).
* `RequestProject/Root/CodingTheory/OfficialCircuitArityDeployed.lean` — deployed row (§5).
* `RequestProject/Root/CodingTheory/OfficialCircuitPencilRank.lean` — rank bound (§7).
* `RequestProject/OfficialCircuitArityAxiomAudit.lean`,
  `RequestProject/OfficialCircuitDeployedAxiomAudit.lean` — axiom audits.

Analysis (Python, exploratory; the Lean files are the verification):

* `analysis/official_arity_four_circuit_search.py`, `…_search2.py`, `…_search3.py`
* `analysis/official_arity_four_master_construction.py`
* `analysis/official_arity_four_small_instance.py`
* `analysis/official_arity_four_transfer_deployed.py` (+ `…_output.txt`)
* `analysis/official_arity_four_deployed_lean_data.py` (+ `…_output.txt`)
