# Field reduction, the multiplication algebra and the Desarguesian spread

**Verdict: `[EXACT-NORMAL-FORM]` + `[SPREAD-INCIDENCE-DICTIONARY]` + `[RANK-GATE]` +
`[BARRIER]`.**  No advance past Johnson is claimed, and Grand MCA is *not* resolved here; see
§6 for the honest status of the main goal.

All statements below are machine-checked, `sorry`-free, and depend only on
`propext / Classical.choice / Quot.sound` (audited in
`RequestProject/FieldReductionAxiomAudit.lean`).  Everything is stated against the project's
official `IsBad / badSet / badWithPair / LineCloseOn / devActive / pairAgree` predicates.

Files:

| file | content |
|---|---|
| `RequestProject/Root/CodingTheory/DesarguesianSpread.lean` | the multiplication algebra of `K/F` as a matrix spread set; the field-reduction spread of `K × K` |
| `RequestProject/Root/CodingTheory/SpreadMCA.lean` | official MCA as incidence with that spread; the exact fibre description; the linear-set rank theorem |
| `RequestProject/Root/CodingTheory/FieldReductionNormalForm.lean` | the `U + M(r)V` normal form; the common-support coordinate decomposition of `IsCloseOn`, `LineCloseOn`, `IsBad` |
| `RequestProject/Root/CodingTheory/SpreadIncidenceBarrier.lean` | sharpness of the spread constraint |
| `RequestProject/Root/CodingTheory/KoalaBearFieldReduction.lean` | the deployed KoalaBear row in normal form, and the deployed rank gate |

---

## 1. The multiplication algebra is a spread set

For a field extension `K/F` the regular representation `ρ(r) = mulLeft F r` satisfies
`ρ(r) − ρ(s) = ρ(r − s)`, which is bijective for `r ≠ s`
(`mulLeft_sub_bijective`).  So `{ρ(r)}` is a **matrix spread set**.  Its graphs

  `spreadElem r = {(v, r·v)} ⊆ K × K`,

together with `spreadInf = {0} × K`, form the family `spreadMember : Option K → Submodule F (K × K)`
— the Desarguesian spread of field reduction `P¹(K) → PG(2[K:F] − 1, F)`.  Proved:

* `spreadMember_inter_eq_bot` — distinct members meet only in `0`;
* `existsUnique_spreadMember` — **every nonzero vector lies on exactly one member**, with the
  slope map `spreadIndex` computing the index;
* `finrank_spreadElem`, `finrank_spreadInf` — every member has `F`-dimension `[K:F]`;
* `spreadElem_map_scale`, `spreadElem_map_swap` — invariance under the `K`-scaling and under
  the projective inversion `(v,u) ↦ (u,v)`, i.e. the spread is a `P¹(K)`-object, not a
  basis-dependent one.

## 2. Official MCA *is* spread incidence

For a codeword pair `(c₀,c₁)` put `devVec x = (f₁x − c₁x, f₀x − c₀x)`.  Then

* `devVec_ne_zero_iff` : `devVec x ≠ 0 ⟺ x ∈ devActive`;
* `mem_pairAgree_iff_devVec_mem_spreadElem` : the `γ`-points agree at `x` **iff**
  `devVec x ∈ spreadElem F (−γ)`.

Because the spread partitions the nonzero vectors, *each deviating position votes for exactly
one challenge*.  This is the geometric source of the project's existing fibre law
`disjoint_devActive_inter_pairAgree`, and it upgrades it to an identification of the challenge
coordinate itself:

* `spreadIndex_devVec` : at an active agreeing position the spread index of the deviation is
  `some (−γ)`;
* `badWithPair_subset_image_challengeAt` : **every challenge explained by the pair is the
  slope of one of its deviation vectors** — the challenge coordinate is replaced by the set of
  spread members met by the deviation locus;
* `card_badWithPair_le_card_devActive'` : hence `m ≤ |A|`, re-derived geometrically;
* `mem_badWithPair_iff_votes` (with `mem_votes_iff`): an **exact, iff** description —
  `γ` is explained by the pair exactly when the spread member indexed by `−γ` carries all but
  at most `e` of the deviation vectors and the resulting support is not line-close.  Nothing
  about the challenge remains except this incidence datum.

## 3. The rank (linear set) theorem

If the deviation locus lies in an `F`-subspace `W ⊆ K × K` — after field reduction, an
`F`-linear set of `PG(1,K)` of rank `dim_F W` — then each explained challenge owns a whole
punctured `F`-line of `W`, and lines of different challenges lie on different spread members,
so they are disjoint:

  `card_badWithPair_scaling_bound` / `card_badWithPair_le_of_finrank`:
  `(|F| − 1)·m + 1 ≤ |F|^{dim_F W}`,

i.e. `m` is at most the number of points of a linear set of that rank.  Consequences:

* `card_badWithPair_le_one_of_finrank_le_one` — a **rank-one** deviation locus explains at
  most **one** challenge;
* `card_badSet_le_card_bigPairs_of_rank_one` — if every big pair of a line has rank-one
  deviation, then `#Bad ≤ max 1 (#bigPairs)`.

## 4. The exact field-reduction normal form

With `D ⊆ F` (recorded by a section `a : ↥D → F`, `algebraMap (a x) = x`) and an `F`-basis `B`
of `K`:

* `repr_lineComb` : in coordinates the line is literally `U + M(γ)·V`, `M(γ)` the
  regular-representation matrix of the challenge;
* `isCloseOn_iff_forall_coord` : `K`-valued `(S,k)`-closeness **iff** all `[K:F]` base-field
  coordinate words are `(S,k)`-close *on the same `S`*;
* `lineCloseOn_iff_coord`, `isBad_iff_coord` : official `K`-valued MCA is, witness by witness,
  the interleaved base-field problem on **one common support**, with the correlated
  (`¬LineCloseOn`) clause preserved verbatim.  No six independent list-decoding problems
  appear anywhere.

Deployed instantiation (`KoalaBearFieldReduction.lean`): `p = 2^31 − 2^24 + 1`,
`K = F_{p^6}`, `H = μ_{2^21} ⊆ F_p^*`, `k = 2^20`.  Since `2^21 ∣ p − 1`, every evaluation
point is base-field rational (`secKB_spec`), so `isBad_iff_coord_deployed` and
`mem_badSet_iff_coord_deployed` give the row's badness in the six-coordinate common-support
form, and `card_badWithPair_rank_bound_deployed`,
`heavy_pair_rank_ge_two_deployed` give the deployed rank gate: every pair explaining two or
more official challenges has deviation rank `≥ 2` over `F_p`.

## 5. Barrier: the spread alone gives exactly the fibre law

`exists_spread_configuration` shows that whenever `m·(a − e) ≤ a` there **is** a configuration
of `a` nonzero vectors of `K × K` realising `m` distinct challenges, each spread member
carrying `≥ a − e` of them.  So the inequality `m·(|A| − e) ≤ |A|` is the *complete* content
of the field-reduction picture of the challenge fibre; improvements must use information the
spread does not see (Reed–Solomon degrees, locator/syndrome geometry, or the evaluation
domain).  Quantitatively the rank theorem only bites at rank `1` on the deployed row: rank `2`
already permits `p + 1 ≈ 2.1·10^9` challenges per pair, far above the per-pair ceiling
`e + 1 ≈ 9.8·10^5`.  This is an honest negative calibration of the "Desarguesian-spread
incidence" programme: it produces the right *language* (basis-independent, projective) and an
exact fibre description, but no new quantitative gain by itself.

## 6. Status of the main goal (Grand MCA)

Not resolved, and no resolution is claimed.

* The deployed row at agreement `1,116,048` is taken as externally certified **OFFICIAL
  UNSAFE** (`#Bad ≥ 2^59 + 1 > B*`), per the mission instruction; nothing here re-proves or
  contradicts that, and no attempt is made to prove that row SAFE.
* What is added is a faithful reformulation (`§4`) and a challenge-free, basis-independent
  description of the fibre (`§2`), plus one genuine structural gate (`§3`) and its own
  limitation (`§5`).
* The remaining question, in the new language, is exactly: *how many members of the
  Desarguesian spread can carry `≥ |A| − e` deviation vectors of a **Reed–Solomon** codeword
  pair on the smooth domain `μ_{2^21}`?*  The geometry alone answers `⌊|A|/(|A|−e)⌋`
  (§5, sharp); everything beyond that must come from the code.
