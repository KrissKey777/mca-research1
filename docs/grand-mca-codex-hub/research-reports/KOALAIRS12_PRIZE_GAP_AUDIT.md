# PRIZE GAP AUDIT — "koalaIRS12" cash-out

**Mission.** No new structural theory.  Determine whether *any* theorem already proved in this
repository raises the certified soundness of the "koalaIRS12" parameter point, and if not, name
the exact inequality whose smallest improvement would.

Everything numeric below is produced by `analysis/koala_irs_prize_gap_audit.py` (exact integers /
80-digit decimal arithmetic, no floats in the inputs).  Nothing in this document is a Lean
theorem; the Lean status of every cited result is stated explicitly.

---

## 0. What "koalaIRS12" was traced to, and what could not be traced

Traced (public, read directly from the source, not reconstructed from intuition):

| object | location |
|---|---|
| the reduction that turns `ε_mca` into protocol soundness | `ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean`, `certifiedExtractorError` / `winningSetUpperBound` |
| the parameter façade a leaderboard entry instantiates | `ArkLib/ProofSystem/ToyProblem/Leaderboard.lean`, `FixedRadiusParameters` (`koalaFRS` is the in-tree inhabitant: `k = 2^20`, `|ι| = 2^16`, `s = 32`, `t = 128`, `F = KoalaBear.Ext6`) |
| the interleaved encoder the executable extractor uses | `ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean` |
| the challenge field | `KoalaBear.Ext6`, `p = 2^31 − 2^24 + 1`, `|F| = p^6`, `log₂|F| = 185.9321` |

**Not traced, because it is not public.**  `Impl/IRS.lean` states in as many words that the concrete
interleaved profile — smooth base-field domain, production parameter shape, and *any numeric
certificate* — lives in a **downstream prize-challenge repository**, deliberately not in ArkLib
("no numeric error value is proven in-tree at any production shape").  So the exact
`(ρ, t, δ)` triple behind the number 67.33 could not be read off; §4 reconstructs it from the
number itself, and every conclusion below is stated so that it does not depend on which
reconstruction is right.

**The reduction (exact, verbatim in content).**

```
eps(δ, t) = (1-δ)^t + ( ε_mca(C, δ) + |Λ(C^{⋈2}, δ)| / |F| ) · ( 1 - (1-δ)^t )
bits      = -log2 eps(δ, t)
```

`ε_mca` is `mcaError (AffineLineGenerator F) C δ` — the affine-line, **arity-2** mutual-correlated-
agreement error.  That is exactly the event this repository calls `badSet k e f₀ f₁` (`MCA.lean`):
`IsBad` = "some `S` with `|S| ≥ n − e` witnesses closeness of `f₀ + γ f₁` but not of the whole
line", ArkLib's `IsMCA` = "some `T` with `|T| ≥ n(1−δ)` on which the combination is in the projected
code but some word is not".  With `δ = e/n` the two predicates agree (the `∀γ`-form and the
`∃ word`-form are interchangeable by two-point Lagrange, `exists_codewords_of_lineCloseOn`).

---

## 1. The decisive arithmetic fact: the MCA **constant** is worth zero bits

At `|F| = 2^185.93` and `n = 2^16` every bad-set bound proved in this project is between `2^13`
and `2^32`.  The query term of the reduction at the audited score is `2^-67`.  Therefore

```
ε_mca ≤ B/|F| ≤ 2^32 / 2^185.93 = 2^-153.9   vs   (1-δ)^t = 2^-67.33
```

and the sum is unchanged to more than 30 decimal places.  Concretely (ρ = 1/2, unique-decoding
radius, t = 202):

| `B` | certified bits |
|---|---|
| `0` | 83.8375748543 |
| `1` | 83.8375748543 |
| `2^20` | 83.8375748543 |
| `2^40` | 83.8375748543 |
| `2^60` | 83.8375748543 |

A constant improvement starts to matter only once the score approaches the ceiling
`−log₂((B+1)/|F|)`:

* `B = (k+1)e+1` (subresultant, ρ = 1/2 at UD): ceiling **156.93 bits**
* `B = e+1` (sharp counting bound, ρ = 1/2 at `(1−ρ)/3`): ceiling **172.52 bits**

Both are ~90 bits above the number being audited.

**Consequence for the requested per-theorem table.**  For every theorem in the audit list the
`ε_MCA` value is `< 2^-150` and its *contribution to the final protocol soundness is exactly
0.000000 bits*.  What distinguishes them is not the value, but the **radius window** in which they
are valid — that is the only thing that reaches the score.

| certified theorem (this repo, `sorry`-free) | window on `δ = e/n` | `B` | `ε_mca` at ρ=1/2, n=2^16 | Δ bits |
|---|---|---|---|---|
| `PolyGen.card_badSetG_le_sharp` (ℓ=2) | `δ ≤ (1−ρ)/3` | `e+1` | `2^-172.5` | 0 |
| support-overlap phase law (`card_badSetG_le_two_mul_of_defect_ge`) | `δ ≤ (1−ρ)/3`, conditional on defect | `2` | `2^-184.4` | 0 |
| circuit / incidence bound (`card_badSetG_le_circuit`, `…_le_choose_sparse`) | window-free | `C(n,e)` | `2^42600` (vacuous) | 0 (unusable at `e ≫ 7`) |
| Hankel phase bound (`mem_badSetG_iff_det_syndromeMatrix_eq_zero`, `card_badSetG_le_sum_natDegree`) | minimal-support phase | `≤ e+1` | `2^-172.5` | 0 |
| cumulative-rank / staircase (`#Bad ≤ (e+1)(ℓ−1) − Δ`) | same window | `≤ e+1` | `2^-172.5` | 0 |
| minimal-support top-word exclusion (`… − 1`) | same window, conditional | `e` | `2^-172.5` | 0 |
| two-word `#Bad ≤ |T|` (`card_badSetG_le_card_support_two`) | `shiftDet ≠ 0` | `≤ e` | `2^-172.5` | 0 |
| **`Subresultant.card_badSet_le_unconditional`** | **`δ ≤ (1−ρ)/2`** | `(k+1)e+1` | `2^-156.9` | see §2 |
| `MCAJohnson.card_badSet_le_listSizeMax` | `δ ≤ (1−ρ)/2` | `n·Λ` | `2^-154` | see §2 |
| `MCAJohnson.epsMCAmax_le_johnson` | `δ < (1−√ρ)/2` | `O(n)` | `2^-170` | 0 (radius below UD at ρ=1/2) |

Combinations of these bounds change nothing: the minimum of several numbers all below `2^-150`
is still below `2^-150`.

---

## 2. The only lever is the **radius**, and our best radius is already matched in ArkLib

Since the constant is free, the score is `t · log₂(1/(1−δ))` to within `10^-30` bits.  The
question therefore collapses to: *what is the largest `δ` at which an admit-free MCA bound
exists?*

Certified radius ladder (relative radii; `ρ` = rate of the underlying RS row code):

| rate | ours `(1−ρ)/3` | half-Johnson | GKL `1 − ρ^{1/3}` | unique decoding `(1−ρ)/2` | Johnson `1 − √ρ` |
|---|---|---|---|---|---|
| 1/2 | 0.16667 | 0.14645 | 0.20630 | **0.25000** | 0.29289 |
| 1/4 | 0.25000 | 0.25000 | 0.37004 | **0.37500** | 0.50000 |
| 1/8 | 0.29167 | 0.32322 | **0.50000** | 0.43750 | 0.64645 |
| 1/16 | 0.31250 | 0.37500 | **0.60315** | 0.46875 | 0.75000 |

Bits per spot check `log₂(1/(1−δ))`:

| rate | `(1−ρ)/3` | half-Johnson | GKL | UD | Johnson |
|---|---|---|---|---|---|
| 1/2 | 0.26303 | 0.22845 | 0.33333 | 0.41504 | 0.50000 |
| 1/4 | 0.41504 | 0.41504 | 0.66667 | 0.67807 | 1.00000 |
| 1/8 | 0.49750 | 0.56325 | 1.00000 | 0.83007 | 1.50000 |
| 1/16 | 0.54057 | 0.67807 | 1.33333 | 0.91254 | 2.00000 |

The strongest radius this repository certifies for the arity-2 MCA event is
`δ ≤ (1−ρ)/2` (`Subresultant.card_badSet_le_unconditional`, window `k + 2e ≤ |D|`).

**But ArkLib already has that radius, admit-free, with a better constant.**
`ProximityGap/BCIKS20/EpsCa.lean`:

```
theorem rs_mcaError_le_of_le_relUDR
    (hδ_pos : 0 < δ) (hδ : δ ≤ relativeUniqueDecodingRadius (ReedSolomon.code domain deg)) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code domain deg) δ ≤ n / |F|
```

with `relativeUniqueDecodingRadius = ((d−1)/2)/n = (1−ρ)/2` for RS, in a file with **no** `sorry`,
and the interleaving transport `ProximityGap.mcaError_interleaved_eq` (also `sorry`-free) carries
it from the scalar RS code to the interleaved code the koalaIRS profile uses.  ArkLib additionally
has the GKL/1.5-Johnson MCA bound `linear_mcaError_le_one_point_five_johnson`
(`δ ≤ 1 − ρ^{1/3}`, proved from `linear_mcaError_powers_le`, no `sorry` in that file), which is
*larger* than our radius at ρ ≤ 1/8.

So on the axis that matters we are **at**, never above, the public admit-free frontier:

| rate | best ArkLib admit-free δ | best δ from this repo | frontier |
|---|---|---|---|
| 1/2 | 0.25000 (UD) | 0.25000 (UD) | tie |
| 1/4 | 0.37500 (UD) | 0.37500 (UD) | tie |
| 1/8 | 0.50000 (GKL) | 0.43750 (UD) | ArkLib |
| 1/16 | 0.60315 (GKL) | 0.46875 (UD) | ArkLib |

---

## 3. Conditional results: does the protocol supply the hypotheses?

Tested against the actual protocol objects, not intuition.

* **"the leading/top word is within decoding radius of the RS code" — REFUTED as a protocol
  guarantee.**  The supremum defining the score is over `ToyProblem.ViolatingInstance`
  (`SoundnessBounds.lean`): the data is `v, μ₁, μ₂, f₁, f₂` with the *single* hypothesis
  `¬ RelaxedRelationFor (ℓ := 2) enc δ v ![μ₁,μ₂] ![f₁,f₂]`, i.e. the **pair** has no common
  agreement set carrying constraint-satisfying codewords.  `mcaError` likewise takes
  `⨆ U : Fin 2 → (ι → A)` with no side condition on `U`.  Nothing forces `f₂` (or `f₁`) to be
  individually close to the code; the negated relation is a statement about the pair, and it is
  satisfied by instances whose second word is literally a codeword with the wrong claimed value
  `μ₂`.  This is precisely the configuration our own §100 extremal family realises
  (`MinimalSupportSlotSharpness`: the `±`-pattern family attains the sharp bad-set size while its
  slot-1 word is identically zero).  So the conditional theorem does **not** import.
* Even if it did import, its yield is `#Bad ≤ (ℓ−1)(e+1) − 1`, i.e. `Δ bits = 0` by §1.
* Same verdict, same reason, for every other conditional in the list (defect ≥ e+2,
  `shiftDet ≠ 0`, rigidity, minimal-support phase): all are constant-side, hence worth 0 bits, and
  none is guaranteed by the reduction.

---

## 4. Reconstruction of the 67.33-bit anchor

Solving `t · log₂(1/(1−δ)) = 67.33` at each certified radius (`analysis/…_audit.py` §4) gives an
integer `t` in exactly two places:

| reading | rate | radius | `t` | bits |
|---|---|---|---|---|
| **R1** | 1/2 | GKL `1 − ρ^{1/3}` (1/3 bit per query) | 202 | 67.3333 |
| **R2** | 1/4 | GKL `1 − ρ^{1/3}` (2/3 bit per query) | 101 | 67.3333 |
| R3 | 1/2 | `(1−ρ)/3` (our counting window) | 256 | 67.3368 |

All other combinations need a non-integer `t` (e.g. UD at ρ=1/2 needs `t = 162.23`).  R1/R2 are
the only readings that reproduce the printed digits exactly, so the incumbent most plausibly sits
at the **GKL 1.5-Johnson radius**.

**Scores under each reading:**

| reading | incumbent | ours (best repo route, UD radius) | Δ |
|---|---|---|---|
| R1 (ρ=1/2, t=202) | 67.333 | 83.838 | **+16.504** |
| R2 (ρ=1/4, t=101) | 67.333 | 68.485 | **+1.152** |
| R3 (ρ=1/2, t=256) | 67.332 | 106.250 | **+38.917** |

**These deltas are real but they are not ours.**  The radius that produces them is
`δ ≤ (1−ρ)/2`, and it is available admit-free from ArkLib's own
`rs_mcaError_le_of_le_relUDR` + `mcaError_interleaved_eq` with the *better* constant `n/|F|`.
Our `Subresultant.card_badSet_le_unconditional` proves the same window with a worse constant, and
the constant is worth 0 bits.  So under readings R1–R3 the honest statement is:

> the incumbent's number can be raised by ~1–39 bits by *selecting a different already-proved
> ArkLib theorem*, with no new mathematics and no theorem from this repository.

---

## 5. REQUIRED OUTPUT

```
CURRENT RECORD : 67.33 bits  (koalaIRS12; most consistent reading: GKL 1.5-Johnson radius,
                              ρ = 1/2 with t = 202, or ρ = 1/4 with t = 101)
OURS           : 67.33 bits  (no theorem of this repository changes the value;
                              the strongest repo route, δ = (1-ρ)/2, is already
                              available admit-free inside ArkLib with a better constant)
DELTA BITS     : +0.000000   (from this repository)
                 +16.50 / +1.15 / +38.92 available by ArkLib route selection alone (R1/R2/R3)
RECORD BEATEN  : NO  (by our mathematics)
```

### BOTTLENECK EXTRACTION

* **`B_target` does not exist.**  Work backwards from the record: the inequality
  `#Bad ≤ B_target` is *sufficient* for any `B_target ≤ 2^98` at a 67-bit score (§1), and it is
  *insufficient* for every `B_target`, including `B_target = 0`, if the radius is unchanged.  The
  multiplicative gap between our current `B` and `B_target` is therefore not a meaningful
  quantity: our `B` is already `2^90`-fold inside the sufficient region.
* **The binding inequality is the radius window**, e.g. `k + 2e ≤ |D|` in
  `Subresultant.card_badSet_le_unconditional` and `δ ≤ relUDR` in ArkLib's counterpart.
* **Sensitivity.**  `d bits / d δ = t / ((1−δ) ln 2)`.  At the frontier `δ = (1−ρ)/2`:

  | rate, t | bits per unit δ | Δδ for +1 bit | extra error positions at n = 2^16 |
  |---|---|---|---|
  | 1/2, 162 | 311.7 | 0.003208 | 210 |
  | 1/2, 202 | 388.6 | 0.002574 | 169 |
  | 1/4, 101 | 233.1 | 0.004289 | 281 |
  | 1/2, 256 | 492.4 | 0.002031 | 133 |

  So **+1 bit costs ≈ 170 additional correctable positions** — an *additive* radius improvement
  of 0.26% of the block length, at any bad-set size up to `2^98`.
* **Milestones above the frontier** (bits per query, multiplicative):

  | rate | frontier | Johnson `1−√ρ` | capacity `1−ρ` |
  |---|---|---|---|
  | 1/2 | 0.41504 | 0.50000 (×1.205) | 1.00000 (×2.409) |
  | 1/4 | 0.67807 | 1.00000 (×1.475) | 2.00000 (×2.950) |
  | 1/8 | 1.00000 | 1.50000 (×1.500) | 3.00000 (×3.000) |
  | 1/16 | 1.33333 | 2.00000 (×1.500) | 4.00000 (×3.000) |

  At ρ = 1/2, reaching the Johnson radius is worth **+13.8 / +17.2 / +21.8 bits** at
  `t = 162 / 202 / 256`; reaching `δ = 0.35` is worth **+33 / +42 / +53 bits**.

---

## 6. DECISION

**C — MATHEMATICAL GAP REMAINS.**

*Smallest quantitative improvement that would beat the record from our side:* an admit-free MCA
bound `#Bad ≤ B` with **any** `B ≤ 2^98` (so the constant is irrelevant, and `(k+1)e+1`,
`(ℓ−1)(e+1)`, `n·Λ` all qualify) valid at a radius **strictly above the current frontier**

```
δ > max( (1−ρ)/2 , 1 − ρ^{1/3} )      (= 1/4 at ρ = 1/2, = 3/8 at ρ = 1/4,
                                        = 1/2 at ρ = 1/8, = 0.60315 at ρ = 1/16)
```

for the arity-2 affine-line event.  The minimum useful step is `Δδ ≈ 0.0026` at ρ = 1/2
(≈ 170 positions at n = 2^16), which buys +1 bit at t ≈ 200.

*Which existing mechanism is closest to supplying it:* the Johnson-range route.  ArkLib's single
external admit on the whole numeric path is
`CapacityBounds.rs_mcaError_le_in_johnson_range` (`sorry`, ABF26 T4.12 / [BCHKS25 Thm 4.6]) —
affine-line MCA for RS on the *whole* Johnson range `δ < 1 − √ρ`, with a bound of size
`O(n·m^5/ρ^{3/2})`, i.e. `2^40`-ish, hence far inside the free region.  **Proving that one
statement admit-free is worth +17.2 bits at ρ = 1/2, t = 202, and +33.7 bits over the R1
incumbent.**  On our side the nearest machinery is the Guruswami–Sudan/Johnson list route
(`MCAJohnson`, `MCAJohnsonGS`, `ListDecodingGS`), which currently stops at *half* the Johnson
radius because the mutual agreement set is extracted from two points of the line at radius `2e`
(`SOTA_PLAN.md` §2); the missing ingredient is the trivariate/Hensel extraction of BCIKS20 §5,
already identified in `MCAJohnsonGS.lean`'s scope note.  The subresultant/Welch–Berlekamp pencil
machinery (`SubresultantCore`, `SubresultantCorrelatedBridge`) is the other candidate carrier, but
it is currently tied to the unique-decoding window `k + 2e ≤ |D|`.

*What is now known to be worthless for the prize, and should not be reopened:* every
constant-side result — the sharp value `(ℓ−1)(e+1)`, its inverse/stability theory, the phase law,
the Hankel/locator factorisation `det H(γ) = det(V_T)² ∏ P_x(γ)`, staircase/cumulative-rank
refinements, the top-word `−1`, and `#Bad ≤ |T|`.  Each is worth **0.000000 bits** at
`|F| = 2^186`, and would remain worth 0 bits until the certified score exceeded ≈ 157 bits.

---

## 7. Provenance check performed during this audit

The full project was rebuilt (`8257` jobs, `Build completed successfully`, no `sorryAx` anywhere in
the log) and the axiom report emitted by `RequestProject/Main.lean` was re-read.  Both theorems the
audit leans on are `sorry`-free and axiom-clean:

```
'Root.CodingTheory.Subresultant.card_badSet_le_unconditional' depends on axioms:
    [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.PolyGen.card_badSetG_le_sharp'            depends on axioms:
    [propext, Classical.choice, Quot.sound]
```

On the ArkLib side, the files carrying the comparison theorems
(`ProximityGap/BCIKS20/EpsCa.lean`, `ProximityGap/Errors.lean`,
`ProximityGap/CapacityBounds/JohnsonMca.lean`, `.../Powers.lean`, `.../Frs.lean`) contain no
`sorry`; the Johnson-range MCA theorem `rs_mcaError_le_in_johnson_range`
(`ProximityGap/CapacityBounds.lean:216`) is an explicit external admit.

---

## 8. Reproduce

```
python3 analysis/koala_irs_prize_gap_audit.py
```

Assumptions that a corrected koalaIRS12 profile would change: `n = 2^16`, `k_scalar = 2^20`,
`|F| = (2^31−2^24+1)^6`, `Λ = 1` at radii below half the minimum distance, and the rate/repetition
pairs of §4.  None of the qualitative conclusions (§1 constant-worthlessness, §2 frontier tie,
§3 top-word refutation, §6 decision) depends on those choices: they hold for every
`|F| ≥ 2^150`, `n ≤ 2^20` and every score below 150 bits.
