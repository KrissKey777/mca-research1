# Which route for MCA proximity? — decision note

This note answers one question: **after the `2e/3e` thread, which of the three candidate
routes should carry the MCA proximity-gap effort?**

* **R1** finite syndrome / MDS-circuit certificates,
* **R2** parametric candidate list + double counting,
* **R3** smooth (2-adic subgroup) evaluation domains.

Everything below is either a machine-checked theorem of this project or an exact-arithmetic
computation whose script and saved output are in `analysis/`.  Nothing here is asymptotic
hand-waving, and no claim of a post-Johnson result is made.

---

## 0. The `2e/3e` thread is now closed

The anchor theorem of the previous run is

```
card_badSet_le_succ_radius :  1 ≤ k → k ≤ |D| → 3e < |D| − k + 1 → #bad ≤ e + 1 .
```

**Result of this session (formal).**  The hypothesis cannot be relaxed to the
unique-decoding condition `2e < |D| − k + 1`:

```
not_forall_card_badSet_le_succ_radius_of_two_radius   (Lean, kernel-checked)
```

with the explicit witness `F = ZMod 5`, `D = {0,1,2,3}`, `k = 2`, `e = 1`,
`g₀ = 1_{1}`, `g₁ = 1_{0} + 1_{1}`, whose strong bad set is `{0, 2, 3, 4}`.  So

* `#bad = 4 = |D|` — the bad set attains the *trivial* bound `card_badSet_le`;
* hence in the band `2e < |D| − k + 1 ≤ 3e` **no** bound of the form `#bad ≤ c(e)` can hold,
  not just the bound `e + 1`;
* and `GapWitness.wbDet_eq_zero`: every maximal minor of the Welch–Berlekamp pencil of the
  witness vanishes identically, so the witness is invisible to the pencil route as well.

**One important refinement.**  Every counterexample found (exhaustively, see below) satisfies
`2e = |D| − k` *exactly*.  The strictly stronger hypothesis

```
k + 2e < |D|        (equivalently 2e < |D| − k,  one unit below d_min − 1)
```

is **not** refuted, and it is exactly the regime of `WelchBerlekampPencil.lean`.  The two
unique-decoding criteria are now combined in one statement,

```
card_badSet_le_succ_radius_of_count_or_pencil :
    3e < |D| − k + 1  ∨  (some maximal WB minor ≠ 0)   →   #bad ≤ e + 1 ,
```

so the only hole left in the whole unique-decoding range is

> **(UD-hole)** `k + 2e < |D|` together with a *totally degenerate* pencil
> (every maximal minor identically zero).

Exhaustive exact scan of the feasible part of that window (`q = 7`, `|D| = 6`, `k = 1`,
`e = 2`; 14 412 000 instances) found `max #bad = 3 = e + 1`: no counterexample.

---

## 1. Verified evidence collected for the decision

| experiment | script | result |
|---|---|---|
| anchor theorem audit, regime `3e < N−k+1` | `analysis/badset_2e_condition_check.py` | 1 200 036 instances, **0** violations of `#bad ≤ e+1` |
| gap regime `2e < N−k+1 ≤ 3e` | same | refuted for every scanned tuple; `max #bad = N = |D|` throughout |
| minimal counterexamples + cross-check | `analysis/badset_2e_condition_counterexample_search.py` | two independent algorithms agree on every bad set |
| strict WB window `k+2e < N` | `analysis/badset_wb_regime_probe.py` | no counterexample (exhaustive where feasible, plus random / planted / rational lines) |
| smooth vs generic domain | `analysis/badset_smooth_domain_probe.py` | `max #bad = N` for multiplicative-subgroup, coset **and** generic domains alike |

The last row is the empirical answer to R3: at the level of the *line* bad set, smoothness of
`D` buys nothing.

---

## 2. The three routes, judged against the actual goal

The goal is a proximity-gap statement usable for FRI/STIR-style protocols, i.e. a bound on
`ε_mca` at radii **above** the unique-decoding radius (ideally past Johnson).  Judged against
that goal:

### R2 — parametric candidate list + double counting: **do not make this the main line**

* Double counting is now *provably* exhausted at its natural boundary: the anchor theorem is
  optimal in its hypothesis (§0), and the failure is not an artefact of the proof — the bad
  set genuinely jumps from `e+1` to `|D|` at `3e = |D| − k + 1`.
* The parametric-list ingredient that would push it further was refuted in the previous run
  (`|codewordLocus(G)| ≤ listSize · deg_Y G` is false), and the whole interpolant-factorisation
  family is closed.
* Residual value: closing **(UD-hole)** would make the unique-decoding row complete and sharp.
  That is a cheap, well-scoped library task, and it has *no* post-Johnson consequences.

### R3 — smooth 2-adic domains: **a setting, not a route**

* The probe shows the line-MCA combinatorics is insensitive to whether `D` is a multiplicative
  subgroup of order `2^m`, a coset of one, or an arbitrary subset: the same worst case
  `#bad = |D|` occurs in all three.  Smoothness does not by itself improve MCA bounds.
* Where smoothness genuinely pays is *folding*: the project's folded-RS capacity results
  (`FoldedRSCapacityListDecoding.lean`, `FoldedRSMCA*.lean`) already exploit it.
* Conclusion: adopt smooth domains as the *parameter setting* of whatever certificate is
  produced (that is what implementations use anyway), but do not expect the smooth structure
  to supply the missing proof step.

### R1 — finite syndrome / MDS-circuit certificates: **the main line**

* It is the only one of the three whose object is not tied to unique decoding: a bad parameter
  is expressed through syndromes / circuit incidences of the MDS code, and the question becomes
  *how many parameters can lie on the relevant secants/circuits*, a finite incidence count.
* Repeated factors of an interpolant — the mechanism behind every closed dead end — play no
  privileged role there.
* Infrastructure already exists in the project: `SyndromeSpace.lean`,
  `SyndromeQuantitative.lean`, `SyndromeRigidity.lean`, `CircuitIncidence.lean`,
  `ShorteningMCA.lean`, `PrizeCertificates.lean`, `MCA_ROOT_WITNESSES.md`.
* Deliverables are unconditional and machine-checkable for the parameters they name, which is
  exactly what a two-sided bracket on `δ*_C(2^-128)` needs.
* Honest limitation: results are row-specific, not asymptotic.  The asymptotic shortening
  exponent `Ψ_ρ` remains a second-stage target.

---

## 3. Recommendation

**Order of work.**

1. **(cheap, optional, 1 step)** close **(UD-hole)**: `k + 2e < |D|` and a totally degenerate
   pencil ⟹ `#bad ≤ e + 1`.  This completes the unique-decoding row; the numerics support it,
   and the statement to attack is now completely explicit.
2. **(main line)** build the first finite syndrome / MDS-circuit certificate for **one**
   official rate, `ρ = 1/2`, on a smooth domain.
3. **(second stage)** only then formalise the general shortening exponent.

**Concrete first target for step 2.**

* Fix `ρ = 1/2`, `D` a 2-adic coset of size `2^m` (the FRI setting), `k = |D|/2`.
* Define `BMCA(a)` — the bad-parameter count at relative radius `a/|D|` — as a *finite*
  quantity of the syndrome model (`SyndromeSpace.lean`), not through an interpolant.
* Prove the containment lemma: every bad parameter lies on a circuit-secant of the shortened
  MDS instance (this is the only genuinely new mathematical step, and it is radius-agnostic).
* Bound the number of such parameters by a decidable finite count for the fixed instance.
* Combine with the existing unsafe witness to obtain `U(a₀+1) ≤ B* < L(a₀)`, i.e. the first
  two-sided bracket for `δ*_C(2^-128)`.

**What not to reopen:** repeated-factor elimination, `codewordLocus` list-size bounds,
squarefree reduced-part carriers, gcd/derivative/resultant-only arguments, the `#bad ≤ 1`
claim, and now also the `2e < |D| − k + 1` weakening of the anchor theorem.
