# The prefix/image fibre of the deployed Mersenne-31 boundary-prefix atom

**Verdict: the requested bound `max fibre ≤ 9.57219783037 × average` is FALSE as stated, with
an explicit counterexample; the sharp constant is a power of two, and the bound holds exactly
when the boundary overhang is at most 3, where the sharp constant is 8.**

Everything below is machine-checked in `RequestProject/PrefixFibre.lean` (no `sorry`,
axioms `propext`, `Classical.choice`, `Quot.sound` only), except the two clearly marked
*measurements* (`analysis/prefix_fibre_atom_measure.py`), which are exploratory and not
verified in Lean.

## 0. Reading of the question

The request's vocabulary ("boundary-prefix atom", "first-match coherent primitive
prefix/image fibre", "large owner") has no counterpart in the existing sources, so it was
given the following concrete reading, which is the only one that is simultaneously
Mersenne-31 specific, deployed, and has a finite max/average constant to determine:

| phrase | object |
|---|---|
| deployed Mersenne-31 field | `p = 2^s − 1`, `s = 31` |
| primitive twiddle | `2^k`, the powers of the primitive `s`-th root of unity `2` — the *free* (multiplication-free) twiddles used by the length-31 DFT |
| boundary-prefix atom | `A_m = {0,…,2^m−1}`: the residues whose boundary prefix (top `s−m` bits) vanishes |
| image prefix / bucket | `π_b(y) = y / 2^(s−b)`: the `b` leading bits, `2^b` buckets |
| prefix/image fibre | `fibre s m b k j = {x ∈ A_m : π_b(2^k·x mod p) = j}` |
| average | `2^m / 2^b` |
| quotient/periodic branch (already removed) | `s ≤ k + m`: the twiddle folds the atom around the Mersenne boundary and the fibre map becomes `2^(s−k)`-periodic |
| coherent branch (the one in question) | `k + m ≤ s` |

## 1. Quantification of the achieved max/average factor

The exact law (proved, `card_fibre_coherent`, `card_fibre_zero`, `card_fibre_zero_mul`):
on the coherent branch, writing `lo = s − k − b`,

```
  |fibre s m b k j| = min(2^m, (j+1)·2^lo) − j·2^lo,
  max_j |fibre| = |fibre … 0| = 2^min(lo, m),
  max fibre / average = 2 ^ min(s − k − m, b)      (exactly, not an upper bound).
```

So the factor is **exactly `2^t`** for the boundary overhang `t = s − k − m`, capped by the
number of prefix bits `b`; it is *row-sharp* — every fibre is either empty or of exactly the
same size, and bucket `0` attains the maximum.

On the periodic branch (`s ≤ k + m`, `k + b ≤ s`) the factor is exactly `1`
(`card_fibre_periodic`): every bucket receives exactly the average `2^(m−b)`. That branch is
therefore harmless, which confirms that the coherent branch is where the whole question lives.
In the remaining branch, where the prefix window is wider than the rotated atom
(`m + k ≤ s ≤ k + b`), the fibres are singletons and the factor is exactly `2^(b−m)`
(`card_fibre_wrapped_le_one`, `card_fibre_wrapped_ratio`).  Together these three branches
cover every `(m, b, k)` with `m < s`, `b ≤ s`, `k ≤ s` except the doubly-wrapped corner
`s ≤ k + m` **and** `s ≤ k + b`, which is not formalised; it lies inside the periodic branch
that the question excludes, and the exhaustive small-`s` measurement below finds the same
`2^t` law there.

Measured and proved values at `s = 31`, atom `m = 20`, prefix width `b = 8`:

| `k` | 0 | 5 | 7 | 8 | 11 | ≥ 11 |
|---|---|---|---|---|---|---|
| overhang `t = 31−k−20` | 11 | 6 | 4 | 3 | 0 | 0 |
| max/average | 256 (capped by `2^b`) | 64 | **16** | 8 | 1 | 1 |
| `≤ 9.57219783037`? | no | no | **no** | yes | yes | yes |

## 2. Verdict on the constant `9.57219783037`

`8 < 9.57219783037 < 16` (`target_between`), and the sharp factor only takes the values
`2^t`.  Hence:

* **Counterexample** (`target_fails_deployed`, `deployed_ratio_eq_sixteen`): at
  `s = 31, m = 20, b = 8, k = 7` the bucket-`0` fibre has `2^16 = 65536` elements against an
  average of `2^12 = 4096` — a factor of exactly `16 > 9.57219783037`.  This is an outright
  refutation, not a surviving obstruction: the configuration is a legitimate coherent
  (non-periodic, non-exceptional) instance.
* **Positive half** (`target_holds_of_overhang_le_three`, `card_fibre_le_eight`): whenever
  `s ≤ k + m + 3`, every fibre is at most `8 ×` the average, hence *below* the requested
  `9.57219783037` with `19.65 %` of margin.  Requested preference (1) is therefore achieved
  in exactly the regime in which any bound of that size can hold.
* **Exact criterion** (`target_holds_iff`): for `b ≥ 4`,
  `(∀ j, |fibre| · 2^b ≤ 9.57219783037 · 2^m) ↔ s ≤ k + m + 3`.
  There is no room to improve the hypothesis: the criterion is an equivalence.
* **Sharp constant over the whole deployed twiddle range** (`sharp_constant_deployed`): at
  `m = 20, b = 8` the exact factor is `2 ^ min(11−k, 8)`, so the uniform-in-`k` sharp constant
  is `2^8 = 256` (and `2^(s−m) = 2^11 = 2048` once `b ≥ 11`), not `9.57…`.

Reduction to one simpler exact statement (requested preference (2)): the whole question
collapses to the arithmetic statement `2^min(s−k−m, b) ≤ C`, i.e. to *the boundary overhang
`t = s − k − m` alone*.  Nothing about primality, Sidon sets or asymptotic primitive-`Q`
machinery enters; the constant is decided by one integer.

## 3. Downstream Mersenne / KoalaBear consequence

* The reason the law is exact for `M31` is the Mersenne rotation identity
  (`twiddle_eq_rotate`): for `x < 2^s − 1`, `2^k·x mod (2^s−1)` is the cyclic left rotation of
  the `s`-bit word, so image prefixes are *bit windows* of the argument and every fibre count
  is a power of two.  This is exactly the free-twiddle structure the project already uses for
  the multiplication-free length-31 DFT.
* For the KoalaBear prime `q = 2^31 − 2^24 + 1` there is no such structure
  (`koalabear_no_rotation`: `2^k mod q ≠ 1` for all `1 ≤ k ≤ 31`; in fact `ord_q(2)` is
  `133 169 152` — *measurement*).  The shared part of the analysis is only the non-folding
  regime `2^k·x < q`, where the same `2^t` law holds for trivial reasons; the folded regime,
  which for `M31` is still a bit permutation and still exactly uniform, is for KoalaBear not
  a permutation of bit windows at all.  *Measurement* (`analysis/prefix_fibre_atom_measure.py`,
  not verified in Lean): at `m = 20, b = 8, k = 24` the KoalaBear max/average is `2.0156`,
  neither `1` nor a power of two.
* Operational reading for a deployed bucketing/routing layer over `M31`: if small values
  (atom width `m`) are twiddled by a free `2^k` and routed on the top `b` bits, the worst-case
  bucket load is *exactly* `2^min(s−k−m, b)` times the average.  To stay inside a constant of
  size `9.57…` one must use `k ≥ s − m − 3` (or let the atom fold, `k + m ≥ s`, which is
  perfectly uniform).  Any other choice pays a power-of-two imbalance, up to `2^(s−m)`.

## 4. What was checked how

* `analysis/prefix_fibre_atom_measure.py` — exhaustive verification of the fibre law for
  Mersenne exponents `s = 5, 7, 13` over all `m, b, k` (0 mismatches), plus the deployed and
  KoalaBear evaluations.
* The Lean definitions were cross-checked against that independent model by `#eval` on four
  parameter sets (`s,m,b,k = (7,4,3,1), (7,4,3,3), (7,5,3,4), (9,6,2,2)`); the fibre profiles
  agree exactly.
