# MCA RESEARCH KERNEL — the minimal reusable spine

Compression of the CodingTheory layer (173 modules, ~2550 declarations) to the results that
can carry a **non-Johnson** bound on the bad set of an affine line.  Every entry is a
`sorry`-free theorem of this repository; the name is the Lean name, verified against the
sources.  Notation: `n = |D|`, `k` dimension, `e` radius, `δ = e/n`, `ρ = k/n`, `c = n−e−k`,
`Λ` a list size, `#Bad = (badSet k e f₀ f₁).card`.

Status legend — **ACTIVE**: on the non-Johnson composition path; **SUPPORT**: needed as an
input by an ACTIVE result; **FROZEN**: hypotheses force `δ ≤ 1/4` at rate 1/2 and it feeds no
stronger active theorem (Phase-2 gate); **KILLED**: refuted, kept as a negative certificate.

---

## 1. Kernel table (34 entries)

| # | Lean name (`Root.CodingTheory.`) | statement | window | output | strength | depends on | obstruction removed | status |
|---|---|---|---|---|---|---|---|---|
| 1 | `IsBad`, `badSet`, `epsMCA` (`MCA.lean`) | the event and its counting measure | — | definition | — | — | fixes the object | SUPPORT |
| 2 | `isBad_iff_exists_agreement_no_correlated_pair` | `γ` bad ⟺ some decoding of the γ-point has an agreement set carrying no correlated pair | none | characterisation | — | 1 | removes the two quantifier layers of `IsBad` | ACTIVE |
| 3 | `badSet_eq_empty_of_direction_codeword` | direction `f₁` a codeword ⇒ `#Bad = 0` | none | `#Bad = 0` | — | 2 | isolates the degenerate line | SUPPORT |
| 4 | `card_badPairSet_le` (`AffineFactorSplit`) | one codeword pair `(A,B)` explains ≤ `n` bad parameters | none | fibre `F ≤ n` | linear | 1 | the per-pair fibre — no list size needed | **ACTIVE** |
| 5 | `card_le_of_common_pair` (`MCAPairCover`) | distinct bad parameters sharing a pair consume distinct positions | none | fibre `≤ n` | linear | 1 | same, in agreement-set form | ACTIVE |
| 6 | `card_family_le_of_pairwise_inter` (`SetFamilyJohnson`) | `|A|(t²−n·c) ≤ n·t` for a family of `t`-sets with pairwise meets `≤ c` | `t² > n·c` | isolated count | `O(n)` | — | bounds the *unpaired* layer; its side condition is exactly `δ < 1−√ρ` | **ACTIVE** |
| 7 | `card_badSet_le_pairCover` (`MCAPairCover`) | `#Bad ≤ n·Λ(k,τ)² + n(n−e)/((n−e)²−n(τ−1))` | `n(τ−1) < (n−e)²` | `Structured ∪ Residual` | radius `1−(ρ(1+1/m))^{1/4}` as stated | 4,5,6 | **the composition itself**, with τ free | **ACTIVE** |
| 8 | `epsMCAmax_le_pairCover_gs` | same with the Guruswami–Sudan list size substituted | GS window | `ε_mca` | explicit constants | 7 | numeric packaging | SUPPORT |
| 9 | `card_badSet_le_affineSplit` (`AffineFactorSplit`) | `#Bad ≤ #Pairs·n + (2b_Y(R)−1)d_Z(R)` for an interpolant split into affine factors × residual | GS interpolant + `disc R ≠ 0` | `Structured ∪ Residual` | length-linear | 4 | discriminant vanishing under correlated agreement | **ACTIVE** |
| 10 | `sq_dvd_residual`, `eval_discLine_eq_zero_of_sq_dvd` | a bad parameter off the affine factors is a root of `disc R` | as 9 | residual root count | poly | 9 | identifies the residual locus | ACTIVE |
| 11 | `card_badSet_le_affineSplit_transfer` (`MultiplicityElimination`) | 9 with squarefreeness only on a *carrier* `S` of the double roots | `DoubleRootTransfer` | same | same | 9 | global squarefreeness | ACTIVE |
| 12 | `doubleRootTransfer_reducedPart_fails`, `sqfreeKernel_bound_fails` | the reduced part does **not** carry the double roots; the squarefree-kernel bound misses a locus of size `|F|` | — | refutation | — | 11 | closes two proposed repairs | KILLED |
| 13 | `card_badSet_le_unconditional` (`SubresultantCorrelatedBridge`) | `#Bad ≤ (k+1)e+1`, unconditional | `k+2e ≤ n` (δ ≤ (1−ρ)/2) | `O(k·e)` | UD frontier | subresultant core | the strongest unconditional radius of the repo | SUPPORT (radius already matched externally) |
| 14 | `card_badSet_le_succ_radius` (`UniqueDecodingMCA`) | `#Bad ≤ e+1` | `3e < n−k+1` | sharp | δ ≤ (1−ρ)/3 | 1 | the sharp counting row | FROZEN |
| 15 | `not_forall_card_badSet_le_succ_radius_of_two_radius` | 14 fails at `2e = n−k`: `#Bad = n` | — | refutation | — | 14 | shows 14 is optimal in its hypothesis | KILLED (as an extension) |
| 16 | `card_badSetG_le_linear_window` (`SyndromeWindowReduction`) | `#Bad ≤ (e+1)(ℓ−1)` in the *linear* window | `(2ℓ−2)e+k ≤ n`, `3e+k ≤ n` | sharp | δ ≤ (1−ρ)/3 | support-concentration | removes the quadratic window | FROZEN |
| 17 | `card_badSetG_le_unconditional`, `card_le_or_rigid` (`SyndromeRigidityDichotomy`) | `#Bad ≤ (e+1)(ℓ−1)` or the family is *rigid* | quadratic window | dichotomy | — | 16 | the rigidity alternative | FROZEN |
| 18 | `card_badSetG_le_hankel`, `…_hankel'`, `…_hankel_or` (`SyndromeHankelCollapse`) | bad ⊆ roots of `e+1` Hankel determinants; `2#Bad ≤ (ℓ−1)(e+1)(e+2)`, or some `det ≡ 0` | `k+2e+1 ≤ n` | domain-free constant | δ < (1−ρ)/2 | syndrome relation | replaces incidence counting by a determinant degree | SUPPORT |
| 19 | `syndrome_relation`, `eval_det_hankel_eq_zero` | closeness off a set of size `m` ⇒ the locator annihilates the shifted moments; bad ⇒ Hankel determinant root | `2m+k+1 ≤ n` | algebraic certificate | — | 1 | the syndrome→Hankel bridge | SUPPORT |
| 20 | `hankelRel_iff_locator_mul` (`HankelLocatorKernel`) | `ker H = Λ_E·F[X]_{≤d}` exactly when `|E| ≤ rows` | `rows ≥ |E|` | exact kernel law | — | — | pins when kernel membership certifies a locator | SUPPORT |
| 21 | `exists_hankelRel_nonvanishing` | as soon as `rows < |E| ≤ cols` a kernel vector vanishes nowhere on `E`; the minimal-degree vector is a non-locator | — | refutation | — | 20 | kills locator repair on the boundary layers | KILLED |
| 22 | `card_badSetG_add_corank_le` (`HankelRankProfile`) | `#Bad + corank ≤` graded budget | minimal-support phase | staircase refinement | constant-side | 18 | rank profile ⇒ budget law | FROZEN |
| 23 | `mem_badSetG_iff_det_syndromeMatrix_eq_zero` (`MinimalSupportHankelBridge`) | bad ⟺ syndrome-matrix determinant vanishes, in the `M = e+1` phase | minimal support | exact locus | constant-side | 19 | exact (not just containment) locus | FROZEN |
| 24 | `card_badSetG_le_two_mul_of_defect_ge` (`SupportOverlapPhase`) | `#Bad ≤ 2` above a defect threshold | defect ≥ e+2 | constant | conditional | 19 | support-overlap phase law | FROZEN |
| 25 | `card_badSet_le_circuit` (`CircuitIncidence`), `card_badSetG_le_choose_sparse` | `#Bad ≤ C(n,e)` type incidence bounds | window-free | combinatorial | vacuous for large `e` | 1 | the only *window-free* bound | SUPPORT (matches the exact worst case `#Bad ≤ C(n,e)`) |
| 26 | `card_badSet_le_listSizeMax`, `epsMCAmax_le_johnson` (`MCAJohnson`) | `#Bad ≤ n·Λ`; `ε_mca` at half-Johnson | `δ < (1−√ρ)/2` | `O(n·Λ)` | half-Johnson | list decoding | the pair is extracted from two points at radius `2e` | SUPPORT |
| 27 | `card_badSet_mul_choose_le` (`ShorteningMCA`) | agreement-set shortening transfer `#Bad·C(S,t) ≤ B·C(n,t)` | shortening | transfer | exponential in `t` | — | moves an instance below its Johnson budget | SUPPORT |
| 28 | `two_pow_le_choose_div_choose`, `not_constant_shortening_for_positive_slack` (`ChojeckiRadius`) | linear shortening depth costs `2^{Θ(n)}`; no constant depth gives positive slack | — | refutation | — | 27 | kills shortening as a constant-relative-radius route | KILLED |
| 29 | `subJohnsonBoundPoly_false` (`SubJohnsonRefutation`) | the dimension-based sub-Johnson hypothesis is false for every `t, C` | — | refutation | — | — | forces the length-based form | KILLED |
| 30 | `forcing_unique_at_frontier`, `forcing_not_unique_beyond_frontier` (`ForcingBarrier`) | forcing is unique iff `k+2e ≤ n`; beyond the frontier two interpolants exist | — | barrier | — | — | explains why every WB/pencil route stops at UD | SUPPORT (the barrier to be routed around) |
| 31 | `exists_correlatedAgreement_of_two_goodZ` (`UniqueDecodingMCA`) | two good parameters with overlapping witnesses ⇒ a correlated pair | `k+2e ≤ n` | pair extraction | UD only | 1 | *the* step that dies in the interior (overlap `n−2e < k`) | SUPPORT |
| 32 | `card_le_card_badSet_blockWord`, `card_div_card_le_epsMCAmax` (`MCALowerBound`) | explicit lines with `r` bad parameters; `ε_mca ≥ r/|F|` | any radius | lower bound | `Θ(1/|F|)` | — | pins the scale of every upper bound | SUPPORT |
| 33 | `card_badSetG_le_sharp` (`PolynomialGeneratorMCA`) + `PolynomialGeneratorSharpness` | `#Bad ≤ (ℓ−1)(e+1)`, sharp | `k+(ℓ+1)e ≤ n` | sharp constant | δ ≤ (1−ρ)/3 | 14 | the arity-generic sharp row | FROZEN |
| 34 | `card_badSet_le_affineSplit_linear` | if the residual is `Y`-linear, no non-degeneracy hypothesis at all | as 9 | unconditional corner | poly | 9 | a genuinely hypothesis-free corner of the split | ACTIVE |

## 2. Minimal dependency spine (DAG)

```
                MCA.IsBad / badSet                        (1)
                        |
      isBad_iff_exists_agreement_no_correlated_pair        (2)
                        |
        +---------------+----------------------+
        |                                      |
  syndrome_relation (19)              card_badPairSet_le (4)
        |                                      |   card_le_of_common_pair (5)
  Hankel collapse (18,20)                      |
        |   (window k+2e+1 ≤ n : FROZEN)       |
        |                                      v
        |                       card_badSet_le_pairCover (7)  <-- SetFamilyJohnson (6)
        |                                      |
        |                                      +--> affine split (9,10,11,34)
        v                                                      |
  subresultant / WB pencil (13,30,31)  <--------- residual disc / carrier
        (all die at k+2e = n : ForcingBarrier)
```

Two live edges only:

* **(6) + (7)** — the set-family Johnson bound is available *exactly* on `δ < 1−√ρ`
  (its hypothesis `(n−e)² > n(k−1)` is that inequality), and `card_badSet_le_pairCover`
  already delivers `Bad ⊆ Structured ∪ Residual` with a **free threshold `τ`**;
* **(4)/(5)** — the fibre of a structured bucket is `≤ n` unconditionally.

Everything else in the table is either an input to these, a frozen constant-side refinement,
or a certified negative result.

## 3. Phase-2 freeze list (routes not to pursue)

Frozen because their hypotheses force `δ ≤ (1−ρ)/3` or `δ ≤ (1−ρ)/2` (i.e. `δ ≤ 1/4` at
rate 1/2) and they feed no stronger active theorem: 14, 16, 17, 22, 23, 24, 33 — the sharp
constant `(ℓ−1)(e+1)`, the staircase / cumulative-rank refinements, the support-overlap phase
law, the minimal-support exact locus, the top-word `−1`, single- and two-syndrome locator
repair, near/far counting, and list-size renamings of `#Bad`.  This matches
`KOALAIRS12_PRIZE_GAP_AUDIT.md` §1: at `|F| = 2^186` each of them is worth 0.000000 bits.

Killed (do not reopen): 12, 15, 21, 28, 29.

## 4. Where the spine stops

The only structurally new step needed is a bound on the number of *relevant* codeword pairs
at overlap threshold `τ = k+1` — the `|T| = k` layer.  `card_badSet_le_pairCover` currently
pays a list size `Λ(k,τ)²` there, which is not polynomial below the Johnson agreement
threshold `√(nk)`.  The exact measurement of that layer, on genuine UD–Johnson interior
instances, is in `NONJOHNSON_INTERIOR_MEASUREMENT.md`; it puts the layer at `O(1)` and
identifies the mechanism (a rank cap in the `2(n−k)`-dimensional syndrome space).
