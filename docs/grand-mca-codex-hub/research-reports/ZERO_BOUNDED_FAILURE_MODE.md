# Failure mode of the `#Bad ≤ 1` mechanism outside its regime

Companion to `ZEROBOUNDED_STATUS.md`.  All numbers below come from exact-arithmetic scans
(`analysis/zero_locus_list_size.py`, `analysis/zero_locus_list_size_targeted.py`; outputs saved
next to the scripts).  Notation as in `ZEROBOUNDED_STATUS.md`; `w = d(f₁, C)`.

## 1. Where the regime ends

The proved regime is `w > 2e` (equivalently `ZeroCountLt C t f₁` with `2e + t ≤ n`).  Its
boundary is not the inequality `2e + t ≤ n` as a numerical accident: the argument produces,
from two distinct bad challenges, a codeword `q₁ ∈ C` with `d(f₁, q₁) ≤ 2e`.  So the *only*
way the argument can fail is that such a codeword exists, i.e. `w ≤ 2e`.

## 2. What actually happens when `w ≤ 2e`

Exhaustive scan, Reed–Solomon `[4,2]` over `F₅` (`d = 3`), all `5⁸ = 390 625` pairs `(f₀,f₁)`,
`e ∈ {0,1}`:

| `e` | `w` | observed `#Bad` |
|---|---|---|
| 1 | 0 | 0 (second layer is a codeword: `badSet_eq_empty_of_snd_mem`) |
| 1 | 1 | up to **3** |
| 1 | 2 | up to **4** = `|F| − 1` |
| 0 | any | ≤ 1 |

First explicit counterexample to `#Bad ≤ 1` outside the regime: `p = 5`, `D = {1,2,3,4}`,
`k = 2`, `e = 1`, `f₀ = (3,4,3,3)`, `f₁ = (4,4,1,1)`, `w = 2`; the bad set is `{0,1,3,4}`, so
`#Bad = 4`.  Larger instances reach `#Bad = 10` (folded RS over `F₁₁`, `n = 6`, `d = 3`,
`e = 2`, `w = 3`), i.e. essentially the whole field.

## 3. Classification of the failure

Of the four candidate explanations in the mission text, the scans single out the first:

* **several distinct close codewords appear — yes, this is the mechanism of failure.**  When
  `w ≤ 2e`, the codeword `q₁` extracted from a pair of bad challenges is no longer unique: the
  auxiliary codewords `h_γ` attached to different bad challenges can differ, and each pair of
  distinct `h`'s supports its own bad challenge.  The formal counterpart is the proof of
  `card_badSet_le_hammingWeight`: the *only* step that can break is the argument
  `d(h_γ, h_γ') ≤ 2e + w < d ⇒ h_γ = h_γ'`;
* agreement sets becoming too small — no; the agreement sets are still of size `≥ n − e` by
  definition of badness;
* the zero-set size jumping — no; the relevant zero locus (of `f₁ − q`) is *large* in the
  failure regime, not small.  What changes is that a large zero locus no longer pins the
  challenge, because the codeword it is measured against is not unique;
* other — the residual case is `d(C)` too small relative to `e` and `w`; see §4.

## 4. The precise dividing line

Two regimes are now proved (see `ZERO_LOCUS_FRONTIER.md`):

```
w > 2e          ⇒ #Bad ≤ 1        (far regime;   ZeroBounded/ZeroCountLt/FarFrom)
2e + 2w < d(C)  ⇒ #Bad ≤ w        (close regime; list-size theorem)
```

and the gap between them is exactly

```
(d − 2e)/2  ≤  w  ≤  2e ,
```

which is nonempty precisely when `d ≤ 6e`.  Every observed counterexample to both conclusions
lies in that gap (783 830 scanned instances over ordinary RS, random linear codes, folded RS
and an exhaustive small RS scan; 0 violations of `#Bad ≤ 1` in the far regime, 0 violations of
`#Bad ≤ w` in the close regime, 0 violations of `#Bad ≤ max(1,2e)` in the combined regime
`6e < d`).  In the gap the bad set can be
as large as `|F| − 1`, so no bound of the form `#Bad ≤ L(w, e)` with `L` independent of `|F|`
can hold there: **the gap is a genuine barrier for the zero-locus route, not a proof
deficiency.**

## 5. Consequence for the research programme

The failure mode is *not* "the zero locus behaves worse than expected"; it is "the zero locus
is measured against a codeword that stops being unique".  Any extension beyond the two proved
regimes must therefore control the *set* of nearby codewords (a list-decoding hypothesis),
not the zero locus of a single difference.  That is the honest statement of what the current
route can and cannot reach, and it is recorded as such in `ZERO_LOCUS_FRONTIER.md` §6.
