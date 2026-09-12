# GATE −1 — EXISTING-THEORY DOMINATION (ℓ = 3 target)

Target under examination:

    4e + μ < N   ⟹   #Bad ≤ max(2, 6e)      (quadratic generator, ℓ = 3)

## 0. Two honest blockers, and what was done instead

**(a) The external comparison could not be performed.** This environment has no access to
external documents. I could not read Bordage–Chiesa–Guan–Manzur (ePrint 2025/2051) or the
WHIR proximity-generator statements, and I did not reconstruct their hypotheses,
generator model, or parameter regime from memory: an invented specialisation is precisely
what this gate exists to prevent. **No L-classification is asserted against those works.**
Supplying the statements (or the PDFs) into the project closes this in one pass: the
specialisation needed is mechanical once the exact hypotheses are on the table.

**(b) The ℓ = 3 problem had no formal referent here.** Nothing in the project defined
`ProximityFrame`, a three-word generator, `μ`, or `N`; every bad-set/MCA declaration was for
the two-word line generator `f₀ + γ·f₁`. Rather than compare against an undefined object, I
**fixed the natural reading and proved the target** (see §2), so that the comparison is now
about a machine-checked statement rather than a proposal. Reading used:
generator `γ ↦ f₀ + γ·f₁ + γ²·f₂`; Reed–Solomon code of degree `< k` on `D`, `N = |D|`,
`μ = k`; `Bad` defined exactly as the project's line notion, with the line replaced by the
quadratic family.

## 1. Internal domination check (project theorems only)

| Existing project bound | Generator | Applies to the ℓ = 3 target? |
|---|---|---|
| `card_badSet_le_succ_radius`, `card_badSet_le_succ` (`#Bad ≤ e+1`) | line only | no |
| `card_badSet_le_unconditional` (`#Bad ≤ (k+1)e+1`) | line only | no |
| `card_badSet_le_choose_radius` (`#Bad ≤ max(C(n,e),e)`) | line only | no |
| `card_badSet_le_circuit` / `…_choose` | line only | no |
| `GG25LineDecodable`, `GG25LiteralMCA` | explicitly the `ℓ = 1` (line) case | no |

Verdict, **internal only**: NOT DOMINATED — no result in this project implies a bad-set bound
for a three-word generator. This says nothing about the external literature.

## 2. What is now machine-checked (`RequestProject/Root/CodingTheory/QuadraticGeneratorMCA.lean`)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`:

* `Root.CodingTheory.QuadGen.card_badSetQ_le` —
  `1 ≤ k`, `k + 4e ≤ |D|` ⟹ `#Bad ≤ max 2 (6e)`. **The target, proved.**
* `…QuadGen.epsMCAQ_le` — `ε_mca ≤ max(2, 6e)/|F|` in the same window.
* `…QuadGen.exists_curveAgreement_of_three_good` — three distinct good challenges force one
  common triple `q₀,q₁,q₂` of degree `< k` agreeing with `f₀,f₁,f₂` on `S₁ ∩ S₂ ∩ S₃`
  (Vandermonde inversion at each position).
* `…QuadGen.card_badSetQ_le_two_mul_defect` — the sharper statement actually proved:
  `#Bad ≤ 2·|D \ T|`, `T` the common agreement set.
* `…QuadGen.eq_of_three_evals` — a nonzero quadratic has at most two roots, coefficient form.

### 2b. The general arity (`RequestProject/Root/CodingTheory/PolynomialGeneratorMCA.lean`)

The same argument was then carried out for the generator of **arbitrary arity `ℓ`**,
`γ ↦ ∑_{j<ℓ} γ^j f_j`. Also axiom-clean, no `sorry`:

* `Root.CodingTheory.PolyGen.card_badSetG_le` —
  `1 ≤ k`, `k + (ℓ+1)e ≤ |D|` ⟹ `#Bad ≤ max (ℓ−1) ((ℓ−1)·(ℓ·e))`, no structural hypothesis.
* `…PolyGen.card_badSetG_le_mul_defect` — the sharper form `#Bad ≤ (ℓ−1)·|D \ T|`.
* `…PolyGen.exists_genAgreement_of_good_family` — `ℓ` distinct good challenges force one
  common family `q₀,…,q_{ℓ−1}` of degree `< k` (Lagrange inversion at each position).
* `…PolyGen.epsMCAG_le` — `ε_mca ≤ max(ℓ−1, (ℓ−1)ℓe)/|F|` in the same window.
* `…PolyGen.card_badSetG_le_three` (= the `max 2 (6e)` target under `k + 4e ≤ |D|`) and
  `…PolyGen.card_badSetG_le_two` (`max 1 (2e)` under `k + 3e ≤ |D|`) are corollaries.

So the `6e` of §3 is the instance `ℓ = 3` of `(ℓ−1)·ℓ·e`, and the window `4e + μ < N` is the
instance `ℓ = 3` of `k + (ℓ+1)e ≤ |D|`: the `ℓ+1` is `1` (own radius) `+ ℓ` (witness sets).

## 3. The resource that explains `6e`

It is **not** a scalar invariant. It is an incidence pair (support × multiplicity):

* **support** — a bad challenge must exhibit a position `x ∉ T` inside its own witness set
  (otherwise that witness set is itself a common agreement set); `T` misses at most
  `ℓ·e = 3e` positions, because it is built from `ℓ = 3` witness sets each missing `≤ e`;
* **multiplicity** — at such a position the quadratic
  `R_x(γ) = (f₀x − q₀x) + γ(f₁x − q₁x) + γ²(f₂x − q₂x)` vanishes, and `R_x ≠ 0` since
  `x ∉ T`; hence at most `ℓ − 1 = 2` bad challenges can charge the same position.

`#Bad ≤ (ℓ − 1) · (ℓ·e) = 6e`, and `max 2` covers the degenerate case of at most two bad
challenges, where no triple exists. The window `4e + k ≤ |D|` is exactly what the
multiplicity step needs: the witness set of a bad challenge meets `T` in `≥ |D| − 4e ≥ k`
positions, enough to identify its interpolant with `q₀ + γq₁ + γ²q₂`. So `μ = k` in the
target's `4e + μ < N`, and the `4` is `1 (own radius) + ℓ (the three witness sets)`.

## 4. Classification

* Against the **cited external results**: **WITHHELD** — not L-A, L-B, L-C or L-D. The
  comparison requires their exact hypotheses, which are not available here (§0a). This is the
  one deliverable of the gate that is not closed.
* Against the **project's own theory**: **L-A (new regime)** — all pre-existing bad-set bounds
  here are line-only; the ℓ = 3 statement is outside their domain, and is now proved.
* On the gate's warning: no universality claim is made. The results cover the explicit
  power generators `γ ↦ ∑_{j<ℓ} γ^j f_j` over Reed–Solomon codes for every arity `ℓ`
  (§2b), in the unique-decoding-style window `k + (ℓ+1)e ≤ |D|`; they are not a general
  proximity-generator theory, and general polynomial-generator MCA statements are expected
  to exist in the literature.

## 5. To close the gate

Supply the statements of the cited results (generator, code model, definition of Bad,
parameter regime). Then the specialisation to `μ = k`, `N = |D|` is a one-pass comparison
against `card_badSetG_le` at the relevant arity `ℓ`, and against the sharper
`card_badSetG_le_mul_defect`, which is the form most likely to be either strictly sharper or
genuinely additional. Item 2 of the gate — sharper dependence on `e`, `ℓ` and `μ` — is now
answered internally: the dependence is `(ℓ−1)·ℓ·e` with `μ = k` entering only through the
window `k + (ℓ+1)e ≤ |D|`.
