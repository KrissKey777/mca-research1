# ARISTOTLE MISSION — IRREGULAR CORE/FIBRE DECOMPOSITION — REPORT

Mission: *do not* prove the regular `Σ(c_i−1) ≤ 2κ−3` bound; instead decide whether every
large family of bad MCA challenges admits a canonical common-core / common-fibre subfamily
that descends to an already controlled correlated-agreement / quotient / grading /
low-dimensional-codeword component.

Notation: `D ⊆ F` the evaluation domain, `n = |D|`, `k` the RS dimension, `κ = n − k`,
`e` the radius, `#Bad = |badSet k e f₀ f₁|`.  "Band" means `2e ≤ κ ≤ 3e − 1`, i.e. strictly
inside unique decoding but strictly below the hypothesis `3e < κ + 1` of the existing
theorem `card_badSet_le_succ_radius`.

---

## 1. Strongest surviving statement

**The core/fibre programme fails, and it fails for a structural reason: in the band the bad
challenges are indexed by the fibres of a fold of the domain, not by a common core.**

Precisely, machine-checked in `RequestProject/Root/CodingTheory/FoldPencil.lean`:

> **Fold-pencil theorem** (`isBad_foldPencil`, `card_le_card_badSet_foldPencil`).
> Let `E : ι → Finset D` be pairwise disjoint blocks of size `e` which are the fibres of a
> degree-`e` fold, i.e. there are scalars `u : ι → F` (injective) with
> `∏_{y ∈ E p} (x − y) = u q − u p` for every `x ∈ E q`.  Fix two blocks `E a ≠ E b`, set
> `R = D ∖ (E a ∪ E b)`, `W = ∏_{x∈R}(X − x)` and
> `f₀ = W·1_{E a}`, `f₁ = W·1_{E b}`.
> If `n < k + 3e` and `k + 2e ≤ n` then for every third block `i` the challenge
> `γ_i = (u a − u i)/(u b − u i)` is bad, with window `D ∖ E i` of size `n − e` and witness
> codeword `p_i = (u a − u i)·∏_{x ∈ R ∖ E i}(X − x)`.  Hence
> `#Bad ≥ |ι| − 2`.

Concrete instances, also machine-checked:

* `exists_foldPencil_multiplicative` — `D` = union of `t` cosets of the group `μ_e` of
  `e`-th roots of unity, fold `x ↦ x^e`; for every `k` in the band
  `#Bad ≥ t − 2 = n/e − 2`.
* `foldPencil_e_eq_one` / `sub_two_div_card_le_epsMCAmax_of_e_eq_one` — for `e = 1` the fold
  hypothesis is vacuous, so **every** Reed–Solomon code with `k = n − 2` (`κ = 2 = 2e`, the
  exact unique-decoding boundary) has a line with at least `n − 2` bad challenges, whence
  `ε_mca ≥ (n − 2)/|F|` — compared with the `e + 1 = 2` cap valid for `κ ≥ 3e = 3`.

Consequences.

* The `3e` hypothesis of `card_badSet_le_succ_radius` is **sharp**: it cannot be relaxed to
  the unique-decoding condition `2e ≤ κ`.  The failure is not marginal — it is by a factor
  `Θ(n/e²)`.
* `ε_mca^max(k, e) ≥ (n/e − 2)/|F|` throughout the band; for `e = 1`, `≥ (n−2)/|F|`.
* The extremal families in the band carry **pairwise disjoint** error sets.  There is
  therefore *no* common core to charge to and *no* nontrivial fibre of `γ ↦ p_γ`: every
  component of every proposed decomposition is a singleton.

## 2. Status

| item | status |
|---|---|
| fold-pencil theorem (general blocks) | **MACHINE-CHECKED** (`FoldPencil.lean`, no `sorry`, axioms `propext, Classical.choice, Quot.sound`) |
| multiplicative `h = X^e` instance | **MACHINE-CHECKED** (`exists_foldPencil_multiplicative`) |
| unconditional `e = 1` instance, `ε_mca ≥ (n−2)/|F|` | **MACHINE-CHECKED** |
| component cap `|component|·(m+b−e) ≤ m`, `≤ e+1` | **MACHINE-CHECKED** (`CoreFibreCharging.lean`) |
| fibre cap for generalised common-window pencils | **MACHINE-CHECKED** (`card_fibreBad_le_succ`, `card_fibreBad_le_of_uniform_fibres`) |
| smallest counterexamples, core/codeword statistics | **EXACT-COMPUTED** (exhaustive over the stated prime fields) |
| upper bound conjecture of §10 | **DERIVED / conjectural** (consistent with all exhaustive data, tight on four rows) |

## 3. Smallest exact counterexample to every killed hypothesis

All are exhaustive computations over prime fields (`analysis/corefibre_band.py`,
`analysis/foldpencil_check.py`, `analysis/foldpencil_stats.py`), cross-checked against the
project's independent brute-force scanner on 210 instances.

**H0 — "`#Bad ≤ e+1` in the strict unique-decoding regime".  KILLED.**
Smallest: `q = 11`, `D = {1,…,8}`, `n = 8`, `k = 3`, `e = 2` (`κ = 5`, band):
`f₀ = (1,2,0,0,0,0,0,0)`, `f₁ = (10,9,1,0,0,0,0,10)`, `badSet = {0,1,2,3}`, so `#Bad = 4 > 3 = e+1`.
All four windows are maximal of size `6 = n − e` and the four error sets
`{1,2}, {3,8}, {5,7}, {4,6}` are pairwise disjoint and tile `D`.
Further exhaustive band rows: `n=10,k=5,e=2,q=13 → #Bad=5`; `n=12,k=7,e=2,q=17 → #Bad=6`.

**H1 — "large `#Bad` forces a large literal common core `T ⊆ S_γ`".  KILLED, scalably.**
In the row above `⋂_γ S_γ = ∅`.  For the multiplicative fold pencils the common core has
size exactly `e` while `#Bad = t − 1 = n/e − 1` (table in §4): the core stays bounded while
`#Bad` grows linearly in `n`.
(The earlier `n=4,k=2,e=1,q=5` instance with `#Bad = 4` and empty core is smaller but is a
list-decoding-regime accident; the band examples above kill H1 in the relevant regime.)

**H2 — "most `S_γ` contain a common `T` up to a bounded petal" (robust core).  KILLED.**
The error sets of the extremal families are pairwise **disjoint** of size exactly `e`
(`max_err_multiplicity = 1` in every row of §4), so the family `{E_γ}` is a partition, i.e.
a "sunflower" with *empty* core and `Θ(n/e)` petals each of full size `e`.  No robust-core
extraction can gain anything: the petals carry all the mass.

**H3 — "the agreeing codewords `{p_γ}` lie in a low-dimensional affine container".  KILLED.**
`dim span{p_γ} = #Bad − 1 = t − 2 = Θ(n/e)` in every fold-pencil row (§4), and the
affine hull has the same dimension.  The container grows with `n`; it is not `O(1)`- or
even `O(polylog)`-dimensional.

**H4 — "each large fibre of `γ ↦ p_γ` is explained by an existing correlated /
quotient / grading branch".  VACUOUS, hence useless.**
`#distinct codewords = #Bad` in every row: all fibres of `γ ↦ p_γ` are singletons, so the
decomposition `Bad = ⊔_ξ Bad_ξ` has `#components = #Bad` and `|Bad_ξ| = 1`.  The bound
`#Bad ≤ Σ_ξ fibreCap(ξ)` degenerates to `#Bad ≤ #Bad`.

**Component charging (Phase 4).  Structurally valid but empty here.**
The per-component cap *is* true and is now formalised
(`CoreCharge.card_mul_le_card_support`: `|B|·(m + b − e) ≤ m`, hence `|B| ≤ e + 1` for a
non-degenerate component, `CoreCharge.card_le_succ_of_lt_core`), and it charges the shared
core `b` **once**.  It is attained by the common-window pencil (`m = e+1`, `b = 0`).  But
the fold pencil shows that the *number* of components is not bounded, so component charging
alone cannot bound `#Bad`.

## 4. Common-core statistics (exact)

Multiplicative fold pencils `D = ⋃_{p<t} c_p·μ_e`, fold `x ↦ x^e`, all `k` in the band.
`core = |⋂_γ S_γ|`; `minpair = min_{γ≠δ} |S_γ ∩ S_δ|`; `mult = max_x #{γ : x ∈ E_γ}`.

| q | e | t | n | k | κ | #Bad | e+1 | core | minpair | mult | disjoint errors |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 11 | 1 | 10 | 10 | 8 | 2 | 9 | 2 | 1 | 8 | 1 | yes |
| 13 | 1 | 12 | 12 | 10 | 2 | 11 | 2 | 1 | 10 | 1 | yes |
| 17 | 1 | 16 | 16 | 14 | 2 | 15 | 2 | 1 | 14 | 1 | yes |
| 13 | 2 | 6 | 12 | 7 | 5 | 5 | 3 | 2 | 8 | 1 | yes |
| 13 | 2 | 6 | 12 | 8 | 4 | 5 | 3 | 2 | 8 | 1 | yes |
| 17 | 2 | 6 | 12 | 7 | 5 | 5 | 3 | 2 | 8 | 1 | yes |
| 31 | 2 | 8 | 16 | 11 | 5 | 7 | 3 | 2 | 12 | 1 | yes |
| 31 | 3 | 6 | 18 | 10 | 8 | 5 | 4 | 3 | 12 | 1 | yes |
| 31 | 3 | 6 | 18 | 12 | 6 | 5 | 4 | 3 | 12 | 1 | yes |

Reading: the common core is `Θ(e)`, *not* `Θ(n)`, while `#Bad = t − 1 = n/e − 1`.  The
windows do overlap a lot pairwise (`minpair = n − 2e ≫ k` in the low-rate rows — the
families are "irregular" in the sense of `card_le_two_mul_of_regular_windows`), but the
overlap is *not* a single shared core.

Broader Phase-1 scan (`analysis/corefibre_scan.py`, 331 instances, `phase1.json`):
0 violations of the core-charging cap, 0 cover violations, 16178 components of which 14
degenerate (`m + b ≤ e`) and 613 with a nonempty core (`b > 0`); H1 already fails on 141 of
the 331 instances.

## 5. Codeword-family dimension / fibre statistics

Same rows as §4:

| q | e | t | n | k | #Bad | #distinct `p_γ` | `dim span{p_γ}` | affine dim | max fibre of `γ↦p_γ` |
|---|---|---|---|---|---|---|---|---|---|
| 11 | 1 | 10 | 10 | 8 | 9 | 9 | 8 | 8 | 1 |
| 13 | 1 | 12 | 12 | 10 | 11 | 11 | 10 | 10 | 1 |
| 17 | 1 | 16 | 16 | 14 | 15 | 15 | 14 | 14 | 1 |
| 13 | 2 | 6 | 12 | 7 | 5 | 5 | 4 | 4 | 1 |
| 31 | 2 | 8 | 16 | 11 | 7 | 7 | 6 | 6 | 1 |
| 31 | 3 | 6 | 18 | 10 | 5 | 5 | 4 | 4 | 1 |

So `dim span{p_γ} = #Bad − 1` exactly, and every fibre is a singleton.  The witnesses
`p_i = (u a − u i)·∏_{x ∈ R ∖ E i}(X − x)` are pairwise non-proportional by construction:
they have *different root sets*.  This is the algebraic reason H3/H4 die — the fold moves
the witness, it does not keep it.

## 6. Degree-`d` pencil classification

Two different families were separated; this settles the mission's question
*"Is CommonWindowPencil merely the degree-1 member of a general fibre theorem?"*.

**(a) Twisted common-window pencils (`f₁ = 1_Y`, `f₀ = −h(x)·1_Y`).**
Formalised in `CoreFibreCharging.lean` for an arbitrary twist `hf : D → F`
(`fibreTunedWord`, `isBad_fibrePencil`).  A challenge `γ` is bad exactly when the fibre
`Y ∩ hf⁻¹(γ)` is nonempty and misses at most `e` positions of `Y`.  Distinct challenges have
disjoint fibres, so
`#fibreBad · (|Y| − e) ≤ |Y|`, hence `#fibreBad ≤ e + 1` (`card_fibreBad_le_succ`), and if
all fibres meeting `Y` have `d` points (`hf = X^d` on a union of `μ_d`-cosets) then
`#fibreBad ≤ ⌊e/d⌋ + 1` (`card_fibreBad_le_of_uniform_fibres`).
**Verdict: within this family the degree-one twist is extremal and higher degree is strictly
worse.  Answer to the literal question: NO — raising the degree of the twist of the
common-window pencil does not help.**

**(b) Fold pencils (`f₀ = W·1_{E a}`, `f₁ = W·1_{E b}` with `E i` the fibres of `h`).**
This is the family that *does* generalise, and it is a genuinely different construction: the
degree-`e` fold acts on the **domain**, and the challenges are indexed by the fibres of the
fold, not by points of one block.  Here `#Bad ≥ t − 2 = n/e − 2`, unbounded.
For `h = X^e` on a smooth multiplicative domain the fibres are exactly the `gcd(e, |D|)`
… more precisely the `μ_e`-cosets, i.e. the sectors of the quotient `D ↠ D/μ_e`, and the
`t = |D|/e` sectors give `t − 2` bad challenges (`exists_foldPencil_multiplicative`).
`e = 1` is the degenerate member and needs no structure at all.
**Verdict: YES — there is a general fibre theorem, but the common-window pencil is not its
degree-one member; it belongs to family (a).  Family (b) is the new mechanism, and it is the
one that kills the `e+1` cap in the band.**

The sharp threshold is explained by a degree count: the witness `Z_i` has degree `n − 3e`,
so the construction needs `n − 3e < k`, i.e. `κ ≤ 3e − 1`, and the non-closeness argument
needs `k ≤ n − 2e`, i.e. `2e ≤ κ`.  The family exists **exactly** on the band and dies at
`κ = 3e`, which is precisely where `card_badSet_le_succ_radius` takes over.

## 7. Quotient / grading relation

The fold pencil *is* a quotient/grading phenomenon, and it connects directly to the
project's existing fold machinery:

* the domain carries the equivalence `x ∼ y ⟺ h(x) = h(y)`, i.e. the quotient
  `D ↠ D/μ_e` (multiplicative model) or `D ↠ D/H` (additive model, `H` a subgroup of the
  additive group);
* `f₀` and `f₁` are supported on two single sectors and are **constant along no sector**
  (they equal `W`, which is a fixed nonzero scalar on each block only in the sense of the
  fold identity), and the bad challenges are in bijection with the remaining sectors;
* the descent is *not* to a correlated-agreement branch: the witnesses `p_i` live on
  different subsets of the domain and their span is `Θ(n/e)`-dimensional.  So the quotient
  organises the bad set, but no known branch absorbs it.

In other words: the correct invariant is the **fold (quotient) of the domain**, not a core of
the window family.  `#Bad` is governed by the number of sectors `n/e`, i.e. by the *index of
the quotient*, and the correct charging unit is a sector, not a challenge and not a core.

## 8. Are VC / shatter / sunflower tools quantitatively useful?

**No.**  Three independent reasons, all exact:

1. The extremal window family is `{D ∖ E_i}` with `E_i` pairwise disjoint.  As a set system
   it is already a `Δ`-system with empty core; a sunflower lemma applied to it returns the
   family itself and no information.
2. The shatter function is irrelevant: the family has only `t = n/e` members, so *any*
   VC-type argument would have to beat `n/e`, which is exactly the quantity we want to
   bound — the tool would have to be at least as strong as the conclusion.
3. Robust-sunflower bounds are at best `polylog`-type in the *number of sets*; here the
   number of sets is already linear in `n` and each has size `e`, so any bound exponential
   in `e` (classical Erdős–Rado) is astronomically useless at the target row, as anticipated
   in the mission brief.

The useful tool is the **algebraic restriction** coming from Reed–Solomon: the windows are
complements of fibres of a low-degree map, and that is a much stronger statement than any
combinatorial complexity bound.

## 9. Target-row consequence

* In the band `2e ≤ κ ≤ 3e − 1` the correct lower bound on the MCA error is
  `ε_mca^max(k,e) ≥ (n/e − 2)/|F|`, not `(e+1)/|F|`.  For `e = 1`, `κ = 2`:
  `ε_mca^max ≥ (n − 2)/|F|`, unconditionally, for every Reed–Solomon code.
* Therefore any target row that quotes `ε_mca ≤ (e+1)/|F|` or `#Bad ≤ e+1` **must** carry
  the hypothesis `3e < κ + 1`; the unique-decoding condition `2e < κ + 1` is not enough.
  This is now a machine-checked constraint on the specification, not a heuristic caveat.
* Conversely nothing here damages the `κ ≥ 3e` row: the fold pencil provably cannot exist
  there (its witness degree exceeds `k`).
* No improvement to the prize row is claimed.  The mission's Phase-5 gate is *not* passed by
  any core/fibre decomposition: all of them are refuted.  What is gained is a sharp
  delimitation of where the cheap `e+1` bound can be used at all.

## 10. ONE next lemma

> **Prove (or refute) the fold upper bound**
> `#Bad ≤ max(e + 1, |D| / (κ − 2e + 1))`
> for every MCA line in the unique-decoding regime `2e ≤ κ`.

Why this one, and only this one:

* it is the *matching upper bound* for the construction just proved, so it would close the
  band completely: the fold pencil attains it (`n = 8, 10, 12` with `e = 2, κ = 5` give
  `#Bad = 4, 5, 6 = n/2` exactly, and the bound is `n/2`), and the common-window pencil
  attains the other branch (`e + 1`);
* it is consistent with **every** exhaustive row computed so far, including the four rows
  where it is tight, and with the `κ ≥ 3e` regime, where `κ − 2e + 1 ≥ e + 1` makes the
  `e + 1` branch dominant for `n ≥ (e+1)²`;
* it is stated in terms already formalised (`badSet`, `IsBad`), so no new definitions are
  needed;
* the natural attack is the disjointness dichotomy visible in every extremal example: two
  bad challenges whose maximal windows meet in more than `k + e` positions share a witness
  line and fall under the (already proved) component cap `e + 1`, while challenges with
  "far" windows have error sets that are nearly disjoint, so at most `n/(κ − 2e + 1)` of
  them fit into `D`.

**Explicitly not recommended:** the regular bound `Σ(c_i − 1) ≤ 2κ − 3`.  As the project
already proves (`card_le_two_mul_of_regular_windows`), a regular pair forces `κ ≤ 2e`, so in
the strict unique-decoding regime the regular branch is empty and the bound is vacuous there.

---

### Files

* `RequestProject/Root/CodingTheory/FoldPencil.lean` — the fold pencil, the multiplicative
  `h = X^e` instance, the unconditional `e = 1` instance and the `ε_mca` lower bound.
* `RequestProject/Root/CodingTheory/CoreFibreCharging.lean` — the component cap with the
  core paid once, and the classification of twisted common-window pencils by their fibres.
* `analysis/corefibre_lib.py`, `corefibre_scan.py`, `corefibre_band.py`,
  `corefibre_band_crosscheck.py`, `corefibre_matching.py`, `corefibre_fold.py`,
  `foldpencil_check.py`, `foldpencil_stats.py` — the exact experiments; raw data in
  `analysis/corefibre_data/`.
