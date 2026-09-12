# [WEIGHTED-LIST-REDUCTION] — official MCA as a layer cake over the interleaved (pair) list profile, and the deployed pivot `m = 16`

**Files.**
`RequestProject/Root/CodingTheory/WeightedInterleavedList.lean` (theory),
`RequestProject/Root/CodingTheory/DeployedWeightedList.lean` (the deployed KoalaBear row),
`RequestProject/WeightedListAxiomAudit.lean` (axiom audit),
plus a small refactor of `RequestProject/Root/CodingTheory/SpreadIncidence.lean` (the
covering step is now a named theorem, `card_badSet_le_sum_card_badWithPair`, from which the
old `card_badSet_le_sum_spreadWeight` is a four-line corollary).

Everything is `sorry`-free, compiles module-by-module, and uses only `propext`,
`Classical.choice`, `Quot.sound`.  Everything is stated against the project's *official*
`IsBad / badSet / epsMCA / LineCloseOn` predicates.

---

## 0. Verdict

The requested object — the **weighted interleaved list profile** — exists, is exactly what
controls official MCA, and is now machine-checked, together with its **multiplicity
stratification** and its deployed evaluation.  What is *not* delivered is a bound on that
profile at the deployed radius: §5 records the precise, quantitative obstruction (the heavy
sector is still strictly post-Johnson), so no claim of a Grand-MCA advance is made.

Ranking asked for in the mission, as delivered:

1. weighted interleaved list profile + multiplicity stratification — **done** (§2, §3);
2. light-sector ↔ MDS/incidence abundance — **bridge proved, obstruction proved** (§4);
3. heavy sector → list decoding — **reduced, then blocked by Johnson** (§5);
4. new abstract invariants — deliberately not attempted.

---

## 1. The object

For a fixed pair of words `(f₀,f₁) : D → F` and the interleaved code `C² = RS_k(D)²`,

```
L₂(r)  =  #{ (c₀,c₁) ∈ C² : |A_{(c₀,c₁)}| ≤ r },
A_{(c₀,c₁)} = devActive f₀ f₁ c₀ c₁ = { x ∈ D : f₀x ≠ c₀x ∨ f₁x ≠ c₁x }
```

(`pairListProfile`, `Root.CodingTheory.pairListProfile`).  This is the *block* (interleaved)
list of the pair code at block radius `r`: the deviation is measured on the **common**
support of the two coordinates, exactly as in the interleaved formulation of MCA.

The second ingredient is the **multiplicity radius**

```
pairRadius e m = ⌊ m·e / (m−1) ⌋   (m ≥ 2),      pairRadius e m = 2e   (m ≤ 1),
```

which by the established fibre law (`mul_pred_card_devActive_le` from `SpreadIncidence.lean`)
bounds the joint deviation of any pair explaining at least `m` bad challenges
(`card_devActive_le_pairRadius`, `mem_pairListProfile_of_le_card_badWithPair`).

---

## 2. The layer cake (Main Question A)

`sum_eq_sum_card_filter` is the elementary layer-cake identity; combined with the covering
step and the unconditional fibre bound `m ≤ e+1` it gives

> **`card_badSet_le_sum_pairListProfile`.**  For every line and every radius,
>
> ```
> #Bad  ≤  max 1 ( Σ_{m=1}^{e+1}  L₂( pairRadius e m ) ).
> ```

This is the exact weighted form the mission asked for, and it is a strict refinement of the
coarse bound: the coarse `#Bad ≤ (e+1)·#bigPairs` is *literally* this sum with every layer
replaced by its largest term `L₂(2e)`.  The layers are evaluated at **strictly decreasing**
radii, from the joint radius `2e` (layer `m = 1`) down to `e+1` (layer `m = e+1`).  The
content is: a bad set of size `M` cannot be paid for by pairs at the a priori radius `2e`
alone — it must be paid for layer by layer, and the deeper layers only accept pairs from
progressively **smaller** interleaved lists.

**Stratified form.**  For any threshold `M ≥ 2` and any radius `r` dominating all layers
above `M` (`card_badSet_le_heavy_light`):

```
#Bad  ≤  max 1 ( (M−1)·L₂(2e)  +  (e+2−M)·L₂(r) ),
```

and if the heavy list is empty (`card_badSet_le_of_no_heavy`), `#Bad ≤ max 1 ((M−1)·L₂(2e))`.

---

## 3. The deployed pivot: `m = 16` (deployed row `n = 2^21`, `k = 2^20`, `δ = 61319/131072`)

`e = ⌊δ·n⌋ = 981104`, `n − k = n/2 = 1048576`, `B* = 274980728111395087`.

| `m` | `pairRadius e m` | `≤ n/2`? |
|---|---|---|
| 2 | 1962208 | no |
| 15 | 1051182 | no |
| **16** | **1046510** | **yes** |

`pairRadius_le_iff_sixteen_le` proves the **exact** statement: for `m ≥ 2`,
`pairRadius e m ≤ n − k ⟺ m ≥ 16`.  Hence the deployed split

* **HEAVY** `m ≥ 16`: block radius `≤ 1046510 < n/2`;
* **LIGHT** `2 ≤ m ≤ 15`: only the a priori block radius `2e = 1962208`.

Deployed bound (`deployed_heavy_light`):

```
#Bad  ≤  max 1 ( 15·L₂(1962208)  +  981090·L₂(1046510) ).
```

**Deployed gates** (all machine-checked on `domKB = μ_{2^21} ⊆ F_{p^6}`, `p = 2^31−2^24+1`):

| statement | content |
|---|---|
| `deployed_dichotomy_prize` | `#Bad > B*` ⇒ a heavy pair exists **or** `L₂(2e) ≥ 18332048540759673 ≈ 1.83·10^16` |
| `deployed_dichotomy_orbit` | `#Bad ≥ 2^59+1` ⇒ a heavy pair exists **or** `L₂(2e) ≥ 38430716820228233 ≈ 3.84·10^16` |
| `deployed_bigPairs_ge_prize` | `#Bad > B*` ⇒ `#bigPairs ≥ 280276553592 ≈ 2.80·10^11` |
| `deployed_bigPairs_ge_orbit` | `#Bad ≥ 2^59+1` ⇒ `#bigPairs ≥ 587562750474 ≈ 5.88·10^11` |

The last two are the coarse gates named in the mission and reproduce its numbers exactly.
The first two are five orders of magnitude stronger *provided* the counterexample has no
multiplicity-16 fibre — which is the real content of the stratification: a Prize-breaking
line must either concentrate 16 challenges on one codeword pair, or exhibit an abundance of
pairs about `10^16`, not `10^11`.

---

## 4. The abundance bridge (Main Question B)

**The bridge exists and is proved.**  `card_pairListProfile_mul_choose_le`:

```
L₂(r) · C(|D| − r, k)  ≤  C(|D|, k).
```

Proof: distinct codeword pairs have joint agreement sets meeting in at most `k−1` positions
(`card_jointAgree_inter_le`, the pair form of the MDS agreement bound), so the families of
`k`-subsets they contain are pairwise disjoint inside the `k`-subsets of `D`.  This is
*exactly* the double counting that drives the project's MDS / circuit-incidence abundance
line (`CircuitIncidence.card_badSet_le_circuit`), transported from challenges to codeword
pairs.  It answers the mission's Question B in the affirmative *as a bridge*.

**The obstruction is also proved, and it is sharp.**  `pos_choose_sub_iff`: the bridge is
non-vacuous iff `r + k ≤ |D|`.  On the deployed row, `abundance_visible_iff_sixteen_le`:

> for `m ≥ 2`, the abundance bound at the multiplicity radius is non-vacuous **iff `m ≥ 16`**.

So on the deployed row (rate `1/2`, where `n − k = n/2`) the mission's heavy/light pivot and
the abundance-visibility pivot are **the same integer**:

```
HEAVY  =  abundance-visible,        LIGHT  =  abundance-blind.
```

In the light sector the bridge is not merely weak, it is empty: `n − 2e = 134944 < k`, so
`C(n − 2e, k) = 0` (`deployed_light_abundance_vacuous`).  This is the precise obstruction
requested: **the MDS/incidence abundance machinery cannot see the light sector at the
deployed radius, because `2e` exceeds the pair code's threshold `n − k`.**

---

## 5. Where the heavy sector stops (Main Question A, second half)

The heavy sector *is* reduced to interleaved list decoding at block radius `1046510`, i.e.
relative radius `0.4990…` — just below capacity `1/2` for rate `1/2`, as the mission
predicted.  But it is still far above Johnson, and this is now recorded numerically:

* `heavy_agreement_sq_lt_johnson`: the guaranteed heavy agreement `a = n − 1046510 = 1050642`
  satisfies `a² < n·k` (Johnson agreement `√(n·k) ≈ 1482910`, relative `0.7071` versus the
  heavy `0.5010`);
* `heavy_agreement_sq_lt_johnson'`: `a² < n·(k−1)`, which is the exact form needed by the
  pairwise convexity count `M·(a²/n − (k−1)) ≤ a − (k−1)` — with a negative leading
  coefficient it bounds nothing.

Consequently the abundance bridge, although non-vacuous in the heavy sector, is
quantitatively inert there: `C(n,k)/C(n−r,k)` is astronomically larger than `B*`.  Closing
the heavy sector therefore requires a genuine post-Johnson interleaved list-size bound, and
for worst-case interleaved Reed–Solomon no such unconditional bound is available (this is
the standing state of the art the mission itself cites).  **No advance beyond Johnson is
claimed.**

---

## 6. Main Question C — the block-support weights of the pair code

The candidate `d_r(C²) = N − k + ⌈r/2⌉` is correct, by the locator argument sketched in the
mission (a joint zero set of size `z` forces both components divisible by a degree-`z`
locator, leaving a space of dimension `2(k−z)`, so `r ≤ 2(k−z)`).

It was **not** formalised, and the mission's own gate is the reason: it yields no useful
rank-vs-fibre or rank-vs-abundance consequence here.  The decisive reading of the formula is
negative:

```
d_1(C²) = d_2(C²) = N − k + 1 :  rank 2 in the pair code buys nothing.
```

The first improvement over the `k−1` agreement bound already in use
(`card_jointAgree_inter_le`, which is the `r = 1` case) appears only at rank `3`, and each
further unit of `|Z|` costs two further dimensions.  Over the deployed field a list of
codeword pairs can have rank `1` and size `|F|` (a pencil `p + t·(L·u, L·v)` through a
common locator), so no rank hypothesis is available for free — which is precisely why the
generalized-weight route degenerates to the `r = 1` bound the file already uses.  Recording
this as an assessed dead end rather than formalising a lemma with no consumer.

---

## 7. Novelty gate

* The interleaved/pair formulation of MCA and its Johnson-type analysis are standard
  (Haböck; Gopalan–Guruswami–Raghavendra for interleaved list decoding) and are **not**
  re-proved here.
* What is new relative to the project's own previous state: the reduction of official
  `#Bad` to a *layer cake over the interleaved list profile at decreasing radii*, the exact
  multiplicity↔radius pivot `m = 16` on the deployed row, the identification of that pivot
  with the abundance-visibility threshold, and the deployed dichotomy gates
  (`10^16` pairs versus a heavy fibre).
* The coarse gates `2.80·10^11` / `5.88·10^11` reproduce the numbers stated in the mission
  and are now theorems about the deployed row rather than arithmetic remarks.
* No external counterexample construction is present in this tree, so nothing about any
  reported construction is replayed or asserted; the gates above are conditional audit
  criteria only.
