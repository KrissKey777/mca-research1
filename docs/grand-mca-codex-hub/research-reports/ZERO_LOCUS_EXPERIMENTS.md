# Exact-arithmetic experiments on the zero-locus mechanism

Scripts and saved outputs (all integer arithmetic modulo a prime; **no floating point**):

| script | output | purpose |
|---|---|---|
| `analysis/zero_locus_list_size.py` | `analysis/zero_locus_list_size_output.txt` | broad scan of `#Bad` against the distance/zero-locus parameters, four code families |
| `analysis/zero_locus_list_size_targeted.py` | `analysis/zero_locus_list_size_targeted_output.txt` | sharpness of the list-size bound, necessity of its hypothesis, test of the pinning mechanism |
| `analysis/circle_factor_two_check.py` | `analysis/circle_factor_two_check_output.txt` | the circle factor-2 question: zeros vs dimension |
| `analysis/zeroBounded_beyond_unique_decoding.py` | `analysis/zeroBounded_beyond_unique_decoding_output.txt` | exhaustive in/out-of-regime comparison and the first counterexample outside `2e + t ≤ \|D\|` |

Definitions computed exactly from the Lean definitions (`AlphabetMCA.lean`): `γ` is bad iff
there is a set `S` with `|S| ≥ n − e` on which `f₀ + γf₁` agrees with a codeword while the
whole line does not.  Two reductions are used, both elementary and both proved in the Lean
development: it suffices to test `S = agreementSet (f₀+γf₁) c` for codewords `c`
(`AgreeOn` is antitone, `¬LineAgreeOn` monotone in `S`), and `LineAgreeOn C S f₀ f₁` holds iff
`f₀|S` and `f₁|S` both lie in the punctured code `C|S` (line closure; `|F| ≥ 2`).

Parameters recorded per instance: `d = d(C)`, `e`, `w = d(f₁,C)`,
`L = #{c ∈ C : d(f₁,c) ≤ 2e}`, `#Bad` and the bad set itself.

Total: **783 830** instances — ordinary Reed–Solomon (720), random linear codes (1 500),
folded Reed–Solomon with block alphabet flattened (360), and an exhaustive scan of all
`(f₀,f₁) ∈ (F₅⁴)²` for RS `[4,2]/F₅` with `e ∈ {0,1}` (781 250).

---

## 1. The far regime (`#Bad ≤ 1`, proved)

`2e < w`: 376 378 (family-wise: 392 / 841 / 145 / 375 000) instances, **0 violations** of
`#Bad ≤ 1`.  Consistent with `card_badSet_le_one_of_farFrom`.

## 2. Sharpness of the far regime

Exhaustive in/out comparison for RS `[4,2]/F₅`, all `(f₀,f₁)`, `e ∈ {0,1,2}`, where `t` is the
smallest parameter making `ZeroCountLt C t f₁` true
(`zeroBounded_beyond_unique_decoding.py`):

| `e` | `2e + t ≤ \|D\|` | instances | max `#Bad` |
|---|---|---|---|
| 0 | yes | 390 625 | 1 |
| 1 | yes | 15 625 | 0 |
| 1 | no | 375 000 | 4 |
| 2 | no | 390 625 | 4 |

First counterexample outside the regime: `e = 1`, `f₀ = (0,0,0,1)`, `f₁ = (0,0,1,0)`,
`d(f₁,C) = 1`, `t = 4`, `2e + t = 6 > 4`: bad set `{0,3,4}`, `#Bad = 3`.  Every counterexample
found has `d(f₁,C) ≤ 2e`, i.e. a codeword inside the radius-`2e` ball.

The conclusion `#Bad ≤ 1` fails as soon as `w ≤ 2e`.  Further witness (exhaustive scan):
RS `[4,2]` over `F₅`, `e = 1`, `w = 1`, `f₁` at distance 1 from the code: `#Bad = 3`,
bad set `{0,3,4}`.  Worst observed: `#Bad = 4 = |F| − 1` at `w = 2` (RS `[4,2]/F₅`), and
`#Bad = 10` for folded RS over `F₁₁` with `d = 3`, `e = 2`, `w = 3`.

## 3. The close regime (`#Bad ≤ w`, proved)

`2e + 2w < d`: 281 353 instances, **0 violations** of `#Bad ≤ w`.

*Attained with `L > 1`* (`zero_locus_list_size_targeted.py`, T1):

| code | `d` | `e` | `w` | `#Bad` | bad set |
|---|---|---|---|---|---|
| RS `[10,4]` over `F₁₁` | 7 | 1 | 2 | **2** | `{9,10}` |
| RS `[12,5]` over `F₁₃` | 8 | 1 | 2 | **2** | `{11,12}` |
| RS `[10,3]` over `F₁₁` | 8 | 1 | 2 | **2** | `{9,10}` |

with `f₁ = (1,1,0,…,0)`, `f₀ = (1,2,0,…,0)`.  This is the first instance in the project of a
proved bound `#Bad ≤ L` with `L > 1` being *attained*.

*Necessity of the hypothesis* (T2): with `2e + 2w ≥ d` the conclusion fails —
RS `[4,2]/F₅`, `e = 1`, `w = 2`, `f₀ = (3,4,3,3)`, `f₁ = (4,4,1,1)`: `#Bad = 4 > 2 = w`;
RS `[6,3]/F₇`, `e = 2`, `w = 2`, `f₀ = (6,4,3,5,4,6)`, `f₁ = (1,0,3,2,1,0)`: `#Bad = 6 > 2`.

*The pinning mechanism itself* (T3): in every in-regime instance with a nonempty bad set
(102 tested on RS `[10,4]/F₁₁`, `[10,3]/F₁₁`, `[12,5]/F₁₃`), the bad set is contained in the
ratio set `{ (h(x) − f₀(x)) / (f₁ − q)(x) : (f₁ − q)(x) ≠ 0 }` for suitable codewords `q, h` —
i.e. the proof's mechanism is what is happening, not an accident of the bound.

*Non-Reed–Solomon codes* (T4): 529 in-regime instances on random linear codes over `F₇, F₁₁`,
**0 violations**, `#Bad` reaching 2.

## 4. The combined regime (proved)

`6e < d`: 391 545 instances, **0 violations** of `#Bad ≤ max(1, 2e)`
(`card_badSet_le_two_mul_of_six_mul_lt_minDist`).

## 5. The list-size conjecture, and one refuted variant

Measured `L = #{c ∈ C : d(f₁,c) ≤ 2e}` on every instance.

* **Refuted:** `#Bad ≤ L · max(1, 2e)`.  Counterexample: RS `[4,2]/F₅`, `e = 0`, `w = 1`,
  `L = 0`, `#Bad = 1`.  (13 + 51 + 20 + 75 000 such instances; all have `L = 0`, `#Bad = 1`.)
* **Survives:** `#Bad ≤ max(1, L · 2e)` — 0 violations in all 783 830 instances, including
  every instance of the gap regime.  Stated as a conjecture in `ZERO_LOCUS_FRONTIER.md` §8;
  not proved.

## 6. The circle factor 2

`circle_factor_two_check.py`, exhaustive over the full circle `{(x,y) : x²+y² = 1}` of
`F₅, F₇, F₁₁, F₁₃` and over all codewords of the circle code of degree bound `t'`:

| `p` | `\|D\|` | `t'` | dim | max #zeros of a nonzero codeword | proved bound `2t'` |
|---|---|---|---|---|---|
| 5 | 4 | 1 | 2 | 2 | 2 |
| 5 | 4 | 2 | 3 | 2 | 4 |
| 7 | 8 | 1 | 2 | 2 | 2 |
| 7 | 8 | 2 | 4 | 4 | 4 |
| 11 | 12 | 1 | 2 | 2 | 2 |
| 11 | 12 | 2 | 4 | 4 | 4 |
| 13 | 12 | 1 | 2 | 2 | 2 |
| 13 | 12 | 2 | 4 | 4 | 4 |

(the `p = 5, t' = 2` row has dimension 3, not 4, because the domain has only 4 points).  For
ordinary Reed–Solomon the same table gives max #zeros `= t − 1` exactly, matching its proved
bound.

Reading: the proved circle bound is **attained**, so it cannot be improved for that code; and
by `finrank_le_of_zeroBounded` (Singleton) no zero bound below `dim − 1 = 2t' − 1` is provable
for *any* code of dimension `2t'`.  The factor 2 is the dimension of the circle code.

## 7. Counterexamples preserved

| # | statement refuted | witness |
|---|---|---|
| C1 | `#Bad ≤ 1` outside `w > 2e` | RS `[4,2]/F₅`, `e=1`, `f₀=(3,4,3,3)`, `f₁=(4,4,1,1)`, `#Bad = 4` |
| C2 | `#Bad ≤ w` without `2e+2w < d` | same instance (`w = 2`, `#Bad = 4`) |
| C3 | `#Bad ≤ L · max(1,2e)` | RS `[4,2]/F₅`, `e = 0`, `L = 0`, `#Bad = 1` |
| C4 | any bound independent of `\|F\|` inside the gap | folded RS over `F₁₁`, `n=6`, `d=3`, `e=2`, `w=3`, `#Bad = 10 = \|F\| − 1` |
| C5 | improvability of the circle zero bound `2t'` | attained on the circle of `F₇, F₁₁, F₁₃` at `t' = 2` |

Earlier counterexamples of the project (minimum distance alone insufficient; characteristic 2;
the `+1` slack in `2e + 2t + 1 ≤ |D|`; `#Bad ≤ s` for multicosets) are unaffected and remain in
`analysis/circle_bridge_falsification.py` and `MulticosetSharpSliceWitness.lean`.
