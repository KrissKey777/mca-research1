# MCA research constitution — checkpoint

Scope of this session: the overriding objective *increase the certified RS MCA/proximity
radius `δ`*, under the anti-drift gate (all FFT/NTT/Verus/implementation work frozen).

Everything marked **Lean** below is machine-checked and `sorry`-free in this repository, with
axioms `propext`, `Classical.choice`, `Quot.sound` only (`RequestProject/Main.lean` audit).
Everything marked **exact computation** is deterministic integer/rational arithmetic in
`analysis/paircover_radius_optimiser.py` — exact, but not Lean-verified.

---

## 0. Status of the previous bottleneck (ND∃)

`ND_EXISTS_MISSION_REPORT.md` records **ND∃ REFUTED** by the scalable spike-line family, with
the refutation formalised at both prize schedules (`ndExists_fails_rho_half`,
`ndExists_fails_rho_quarter`).  That is exit condition 2 of the constitution ("refuted by a
scalable family"), so this session did **not** re-open ND∃ or any of its weakenings
(SF∃/CO∃/GCD-SEP∃ are refuted by the same family).

The surviving successor stated there, **(DICH)**, is *not* attacked here: its (far) half needs
a classification of linear subspaces inside the `Y`-discriminant hypersurface — Test C of the
constitution — which is a long formalisation with no cheap falsifier, and RULE 0 ranks it below
what was actually done (below, and §5).

---

## 1. Two radius scales must be kept apart

The word "frontier" is used in two different senses in this project, and they give different
answers.  Both are recorded here to avoid over-claiming.

**(a) Radius with *any* nontrivial `#bad` bound.**  Best known admit-free values (see
`KOALAIRS12_PRIZE_GAP_AUDIT.md`):

| rate | `(1−ρ)/2` (UD) | `1 − ρ^{1/3}` (GKL, ArkLib) | frontier | Johnson `1 − √ρ` |
|---|---|---|---|---|
| 1/2 | **0.25000** | 0.20630 | 0.25000 | 0.29289 |
| 1/4 | **0.37500** | 0.37004 | 0.37500 | 0.50000 |
| 1/8 | 0.43750 | **0.50000** | 0.50000 | 0.64645 |
| 1/16 | 0.46875 | **0.60315** | 0.60315 | 0.75000 |

**(b) Radius under the *prize error gate*** `ε_mca ≤ 2⁻¹²⁸` at `|F| ≥ 2¹⁶⁰`.  That gate forces
`#bad ≤ 2³²`, which kills the unique-decoding bounds (their constant is `≈ k·e ≈ 2³⁷`) and the
`#bad ≈ n` GKL/Johnson-style bounds are the only ones that survive.  Before this session the
best `2⁻¹²⁸` certificates in this repository were the half-Johnson ones
(`threshold_rho_*`, `MCAJohnsonGS.lean`).

---

## 2. What this session added (all Lean, all unconditional)

`RequestProject/Root/CodingTheory/PairCoverFrontierCrossing.lean` instantiates the *already
proved* unconditional pair-covering bound `epsMCAmax_le_pairCover_gs` (`MCAPairCover.lean`) at
`n = 2²⁰` and the four prize rates, with parameters optimised exactly:

| rate | previous `2⁻¹²⁸` certificate | new certificate | `Δδ` | `#bad` bound |
|---|---|---|---|---|
| 1/2 | `e = 109801` (`δ = 0.10471`) | `e = 161864` (`δ = 0.15437`) | **+0.04966** | `4.15·10⁹ ≤ 2³²` |
| 1/4 | `e = 231202` (`δ = 0.22049`) | `e = 301212` (`δ = 0.28726`) | **+0.06677** | `4.16·10⁹` |
| 1/8 | `e = 317044` (`δ = 0.30236`) | `e = 418122` (`δ = 0.39875`) | **+0.09639** | `4.25·10⁹` |
| 1/16 | `e = 377745` (`δ = 0.36025`) | `e = 515000` (`δ = 0.49114`) | **+0.13089** | `3.52·10⁹` |

At `ρ = 1/16` the new radius is also strictly past the **unique-decoding frontier**
`k + 2e ≤ n` (`e = 491520`): `pairCover_rho_sixteenth_best` sits `46 960` positions beyond it,
and `pairCover_rho_sixteenth_minimal_crossing` records the one-position crossing `e = 491521`.
It is **not** past the external cube-root radius `1 − ρ^{1/3} = 0.60315` at that rate, so on
scale (a) this is *not* a frontier crossing; on scale (b) it is the best certified radius here
at every rate.

Also added, `BadSetCorrelatedCharacterisation.lean`: a structural theorem removing both
quantifier layers from the definition of a bad challenge,

> `γ` is bad **iff** some degree-`< k` polynomial agrees with `f₀ + γ f₁` on `≥ |D| − e`
> positions while the direction `f₁` agrees with **no** degree-`< k` polynomial on that
> agreement set — equivalently, iff some decoding of the γ-point has an agreement set carrying
> no correlated agreement of the pair `(f₀, f₁)`.

Consequence (`badSet_eq_empty_of_direction_codeword`): if `f₁` alone is a codeword, the bad set
is empty at every radius — strengthening `BCHKSJohnson.badSet_eq_empty_of_isCloseOn_univ`,
which assumed both `f₀` and `f₁` to be codewords.  This also explains the spike-line KILL: the
only agreement set there that fails to carry a correlated agreement is the one at `γ = 1`.

---

## 3. Scalable barrier: the ceiling of the pair-covering mechanism (Lean)

`pairCover_ceiling`: the two hypotheses of the mechanism — the GS list condition
`k·n·(m+1) < m·τ²` and the set-family Johnson condition `n·(τ−1) < t²` — force

    k·n³ < (t² + n)²,     i.e. essentially   δ < 1 − ρ^{1/4},

independently of `m` and `τ`.  Corollaries, all Lean:

* `pairCover_cannot_reach_frontier_rho_half` (`e ≥ 262144`), `…_rho_quarter` (`e ≥ 393216`),
  `…_rho_eighth` (`e ≥ 458752`): the hypotheses are **jointly unsatisfiable** at or beyond the
  unique-decoding frontier at those three rates;
* `pairCover_cannot_reach_cube_root_rho_sixteenth` (`e ≥ 632427`): unsatisfiable at the
  cube-root radius at `ρ = 1/16`.

`1 − ρ^{1/4}` beats `(1−ρ)/2` exactly for `ρ` below the root of `t³ + t² + t = 1`
(`t = ρ^{1/4}`), i.e. `ρ ⪅ 0.0874`; of the prize rates only `1/16` qualifies.  This is a
termination-condition-C result *for this mechanism*: constants can still be improved inside the
window, but no choice of `τ, m` reaches the frontier at `ρ ≥ 1/8`.

---

## 4. Checkpoint block

**CURRENT BOTTLENECK:** a `#bad` bound at `δ` strictly above `max((1−ρ)/2, 1−ρ^{1/3})`.  The
pairwise/second-moment machinery cannot supply it (see §5).

**CANDIDATE:** instantiate + bound the unconditional pair-covering mechanism.

**CHEAPEST FALSIFIER:** exact integer feasibility of its two hypotheses at the frontier radii
(`analysis/paircover_radius_optimiser.py`, and the Lean ceiling theorem).

**RESULT:** feasible only at `ρ = 1/16` on radius scale (a); feasible and strictly better than
everything previously certified here at all four rates on radius scale (b).

**RADIUS BEFORE:** (b) `0.10471 / 0.22049 / 0.30236 / 0.36025`; (a) `0.25 / 0.375 / 0.5 / 0.60315`.

**RADIUS AFTER (proved):** (b) `0.15437 / 0.28726 / 0.39875 / 0.49114`; (a) unchanged except
that this repository's own plain-RS radius at `ρ = 1/16` now exceeds its unique-decoding value.

**EXPECTED BIT GAIN:** `log₂(1/(1−δ))` per spot check rises by `0.0823 / 0.1292 / 0.2145 /
0.3303` bits at rates `1/2, 1/4, 1/8, 1/16` relative to the previous `2⁻¹²⁸` certificates; at
`t = 128` repetitions that is `+10.5 / +16.5 / +27.5 / +42.3` bits.  Against radius scale (a)
the gain is `0` at rates `1/2, 1/4, 1/8` and `0` at `1/16` as well, since GKL is higher.

**SCALABLE COUNTEREXAMPLE:** none needed — the ceiling theorem is the barrier.

**NOVELTY STATUS:** none claimed.  The mechanism is standard Johnson/list-decoding counting
(constitution NOVELTY GATE items 1–3); the contribution is the admit-free instantiation and the
exact ceiling.

**RESEARCH SCORE:** `P_success` HIGH, `V_radius` MEDIUM (scale (b)) / LOW (scale (a)),
`V_novelty` LOW, `C_research` LOW.

**DECISION:** FREEZE the pair-covering mechanism.  Its remaining head-room is a constant-factor
fibre improvement (`|D| → e+1`, worth `Δδ ≈ +0.0025` at `ρ = 1/16`, exact computation), which
RULE 0 classifies Tier C.

---

## 5. Where the elementary route provably stops — and the exact next branch

Write `α = 1 − δ`, `t = αn`, and let `S_γ` be a maximal agreement set of a bad `γ`.

1. **Second moment.**  If `m` challenges are bad then some pair has
   `|S_γ ∩ S_{γ'}| ≥ (α² − α/m)·n`.  This crosses `k` exactly when `α² > ρ`, i.e. at the
   **Johnson** radius — so the pair step itself is not the obstruction.
2. **Codeword line.**  A pair with `|S_γ ∩ S_{γ'}| ≥ k` determines a unique codeword line
   `ℓ = (q₀,q₁)` with `f₀ = q₀`, `f₁ = q₁` on that intersection, and both challenges lie in its
   fibre `W_ℓ`.
3. **Fibre bound.**  `|W_ℓ| ≤ (n − |T_ℓ|)/max(1, t − |T_ℓ|) ≤ e + 1`, where
   `T_ℓ = {x : f₀ = q₀, f₁ = q₁}` — because the sets `S_γ \ T_ℓ`, `γ ∈ W_ℓ`, are nonempty and
   pairwise disjoint.
4. **Missing count (CL).**  `#bad ≤ (#arising codeword lines) · (e+1) + (isolated Johnson
   term)`, and the isolated term is finite exactly at the Johnson radius (`t² > n(k−1)`).  The
   one missing ingredient is therefore

   > **(CL)** the number of codeword lines `ℓ` with `|T_ℓ| ≥ k` and `|W_ℓ| ≥ 2` is bounded by a
   > constant `C(ρ, δ)` independent of `#bad`.

   Bounding that count by the set-family Johnson bound needs `|T_ℓ| ≥ τ > √(k·n)`, and the
   second moment only guarantees `|T_ℓ| ≳ α²n`; `α²n > √(kn)` is precisely `α² > √ρ`, i.e.
   `δ < 1 − ρ^{1/4}`.  **This is the same exponent the Lean ceiling theorem produces**, so the
   `ρ^{1/4}` wall is intrinsic to the whole pairwise family of arguments, not an artefact of
   the particular constants — which is why the Johnson radius needs the polynomial method
   (GS interpolation) and why the ND∃ line of attack existed at all.

**Proposed next branch (for external pre-screen before any formalisation), exact statement:**

    (CL)  For a Reed-Solomon line with no correlated agreement at radius e, the number of pairs
          (q0,q1) of degree-<k polynomials whose common agreement set with (f0,f1) has size >= k
          and whose fibre contains at least two e-close challenges is at most C(rho, delta),
          with C independent of the number of bad challenges.

    If (CL) holds with C = O(1) or O(n / e), then
          #bad  <=  C * (e + 1)  +  n*t / (t^2 - n*(k-1))
    is an elementary, admit-free Johnson-radius MCA theorem (t = n - e, valid whenever
    t^2 > n(k-1), i.e. delta < 1 - sqrt(rho)), worth +0.0429 radius at rho = 1/2 and +0.147 at
    rho = 1/16 on radius scale (a).

Falsification order if the branch is greenlit (RULE 1): exact enumeration of the arising
codeword lines for small exact instances above the unique-decoding frontier (`q ≤ 13`,
`n ≤ 13`, `k ≤ 4`), measuring `C` against `#bad`; a family in which `C` grows with `#bad`
KILLs the branch immediately, and would also explain, structurally, why every elementary
pairwise argument stops at `1 − ρ^{1/4}`.

---

## 6. CHECKPOINT — branch (CL): KILLED

**CURRENT BOTTLENECK:** the missing count `(CL)` of §5 — bounding the number of *arising
codeword lines* independently of `#Bad`.

**CANDIDATE:** `(CL)` with `C = C(ρ, δ) = O(1)`, which would give the elementary
Johnson-radius theorem `#bad ≤ C·(e+1) + n·t/(t² − n(k−1))`.

**CHEAPEST FALSIFIER:** exact enumeration of the whole codeword-line set for small RS
instances above the unique-decoding frontier and inside the Johnson radius —
`analysis/cl_codeword_line_count_probe.py` (exact arithmetic over `GF(q)`, whole bad set and
whole set of arising lines computed per instance, no sampling *inside* an instance).

**RESULT:** at `q = n = 11`, `k = 3`, `e = 5` (unique decoding stops at `e ≤ 4`;
`t² = 36 > 22 = n(k−1)`, so this is strictly inside Johnson) the worst instance found has

```
#Bad = 6,   C = 14,   max fibre = 2,   max |T| = 4
```

so `C` already exceeds `#Bad` and tracks `binom(#Bad,2) = 15` with fibres of size 2: each bad
*pair* contributes its own codeword line and the fibres do not merge.  Substituting
`C ≈ #Bad²/2` into `#bad ≤ C·(e+1)` is vacuous.

The probe also exposes the structural reason, which is exact and not an artefact of the small
field.  Fix a bad `γ` with witness set `S_γ` and witness polynomial `p_γ`.  A codeword line
`(q₀,q₁)` through `γ` satisfies `q₀ + γ·q₁ = p_γ` (their agreement contains `≥ k` points of
`S_γ`), so it is parametrised by `q₁` alone, and

```
T(q₁) = { x ∈ S_γ : f₁(x) = q₁(x) }.
```

Hence *the number of codeword lines through `γ` equals the number of degree-`<k` polynomials
agreeing with `f₁` on `≥ k` points of `S_γ`* — a list-decoding count for `f₁|_{S_γ}` at
agreement `k` out of `|S_γ| = t`.  That is far below the Johnson radius of the restricted
problem (`k² > |S_γ|·k` is false), so the count is unbounded in general.

**RADIUS BEFORE / AFTER IF TRUE:** `0.166666 → 0.292893` at `ρ = 1/2` (Johnson) — not obtained.

**EXPECTED BIT GAIN:** 0 on this branch.

**SCALABLE COUNTEREXAMPLE:** the mechanism above is scalable (it is a statement about
list-decoding `f₁` restricted to `S_γ` at agreement `k`), the `q = 11` instance is its smallest
exact realisation.

**NOVELTY STATUS:** none claimed; this is the standard reason the polynomial method is needed
at the Johnson radius.

**RESEARCH SCORE:** `P_success` LOW, `V_radius` HIGH, `V_novelty` LOW, `C_research` LOW.

**DECISION:** **KILL** `(CL)` at threshold `k`.  The count only becomes finite at threshold
`τ > √(kn)` — which is exactly the pair-covering mechanism, whose `ρ^{1/4}` ceiling is already
an admit-free theorem (`pairCover_ceiling`).

**NEXT SINGLE TEST:** the *other* endpoint of the threshold interval, `τ = k + e`, at which the
list-size factor disappears entirely.  See §7.

---

## 7. CHECKPOINT — the near/far codeword-line dichotomy: FORMALIZED

**CANDIDATE:** run the codeword-line threshold at the opposite endpoint `τ = k + e`.  At that
threshold a *single* codeword line controls the *whole* bad set, so no list size is needed.

**CHEAPEST FALSIFIER:** the two halves must meet.  Exact optimisation
`analysis/near_far_dichotomy_optimiser.py` first; then Lean.

**RESULT (both halves proved, admit-free,
`RequestProject/Root/CodingTheory/NearCodewordLineMCA.lean`):**

* **Near.** `card_badSet_le_succ_radius_of_near_codeword_line` — if *any* pair `(q₀,q₁)` of
  degree-`<k` polynomials agrees with `(f₀,f₁)` on `≥ k + e` common positions then
  `#bad ≤ e + 1`, **at any radius `e`, with no regime hypothesis**.  Reason: a witness set `S`
  meets `T` in `≥ |S| + |T| − n ≥ k` positions, so the local witness is forced to be
  `q₀ + γ·q₁`; the private parts `A γ \ T` are then pairwise disjoint and of size
  `≥ n − e − |T|`.
* **Far.** `card_badSet_le_setFamilyJohnson_of_far` — if *no* codeword pair reaches `k + e`,
  then no two badness witnesses meet in `≥ k + e` positions (two such witnesses *build* such a
  pair, `exists_codewordLine_of_two_witnesses`), so the witnesses form a Johnson family of
  `t`-sets with pairwise intersections `≤ k + e − 1`.
* **Combination.** `card_badSet_le_of_nearFar`, `epsMCAmax_le_of_nearFar`:

```
  #bad ≤ max ( e + 1 ,  n·t / (t² − n·(k + e − 1)) )      whenever  n·(k+e−1) < t².
```

**RADIUS BEFORE:** `δ = 0.166666…` at `ρ = 1/2` (the reach of `card_badSet_le` /
`card_badSet_le_succ_radius`, both gated by `3e < |D| − k + 1`); the pair-covering certificate
gives only `0.154366…` there.

**RADIUS AFTER:** `δ = 0.177124…` at `ρ = 1/2` — `nearFar_rho_half`: `|D| = 2²⁰`, `k = 2¹⁹`,
`e = 185728`, certified `#bad ≤ 456383`, hence `ε_mca ≤ 2⁻¹²⁸` for `|F| ≥ 2¹⁶⁰`.
**Δδ = +0.010458 at the constitution's primary laboratory rate.**

**EXPECTED BIT GAIN:** `−log₂(1 − δ)` per spot check rises from `0.263034` to `0.281245`,
i.e. `+0.018211` bits per query, `≈ +2.33` bits over 128 queries.

**SCALABLE COUNTEREXAMPLE:** none; the ceiling is a theorem (`nearFar_ceiling`).

**NOVELTY STATUS:** none claimed.  Both halves are elementary counting (constitution NOVELTY
GATE items 1–2); the contribution is the admit-free hypothesis-form near lemma at arbitrary
radius and the closure of the case distinction.

**RESEARCH SCORE:** `P_success` HIGH, `V_radius` LOW-to-MEDIUM, `V_novelty` LOW,
`C_research` LOW.

**DECISION:** **FORMALIZE — done.**  Then **FREEZE**: the mechanism is at its own ceiling.

### Where it stops, exactly

`nearFar_ceiling`: the Johnson regime `n·(k + e − 1) < (n − e)²` is `(1 − δ)² > ρ + δ`, i.e.

```
   δ  <  (3 − √(5 + 4ρ))/2 ,
```

numerically `0.177124 / 0.275255 / 0.327396 / 0.354356` at `ρ = 1/2, 1/4, 1/8, 1/16`.  The
`τ = k+e` endpoint therefore *dominates* the `τ ≈ √(kn)` endpoint (the pair-covering mechanism,
ceiling `1 − ρ^{1/4}` = `0.159104 / 0.292893 / 0.405396 / 0.5`) exactly when `ρ + δ < √ρ` —
which happens at `ρ = 1/2` and nowhere else among the four prize rates.  Hence the current
best certified radii of this repository are

```
   ρ = 1/2   δ = 0.177124   nearFar_rho_half                     (this section)
   ρ = 1/4   δ = 0.287258   pairCover_rho_quarter
   ρ = 1/8   δ = 0.398752   pairCover_rho_eighth
   ρ = 1/16  δ = 0.491867   pairCover_rho_sixteenth_best
```

against the certified frontier `max((1−ρ)/2, 1 − ρ^{1/3})` = `0.25 / 0.375 / 0.5 / 0.60315`
and Johnson `1 − √ρ` = `0.292893 / 0.5 / 0.646447 / 0.75`.  **No frontier crossing at `ρ = 1/2`;
the intrinsic obstruction is that every threshold `τ` in the interval `[√(kn), k+e]` gives a
mechanism whose ceiling is one of the two endpoints above.**

**NEXT SINGLE TEST (for external pre-screen before any further formalisation).**  The exact
open statement that would break the endpoint barrier, in the notation above:

```
(NEAR-u)  Let the line agree with a codeword line on n − u positions, i.e. after subtracting
          that codeword line f0 and f1 are supported on a set E with |E| = u.  Bound
                    #Bad  =  #{ γ : dist(a0 + γ a1, RS_k) ≤ e },      supp(a0),supp(a1) ⊆ E,
          for u in the window  n − k − e < u ≤ n − √(kn).
```

For `u ≤ n − k − e` the answer is `#Bad ≤ e + 1` (the near half above, since then `|T| ≥ k+e`).
For `u > n − k − e` the witness codewords need no longer be `0` on `D \ E`, and nothing is
known.  This window is nonempty exactly when `δ > √ρ − ρ` (`0.207107` at `ρ = 1/2`), i.e. in
the whole region of interest; it is also exactly the window in which the earlier separability
route provably fails (the multi-spike generalisation of the `ND∃` counterexample family forces
`(Y − p)² ∣ Q` for every admissible interpolant as long as `u ≤ n − √(kn)`).  So `(NEAR-u)` is a
**strictly smaller lemma** than both `ND∃` and the `(DICH)` dichotomy of
`ND_EXISTS_MISSION_REPORT.md`, and it is the single remaining gate on the Johnson radius for
every elementary route examined here.

---

## 8. CHECKPOINT — (NEAR-u) in the open window: SURVIVES falsification

**CURRENT BOTTLENECK:** `(NEAR-u)` of §7 — the only remaining gate on pushing the near
threshold below `k + e`.

**CANDIDATE:** `#Bad ≤ e + 1` continues to hold for `u > n − k − e`, i.e. the near half of the
dichotomy survives past the threshold at which its proof breaks.

**CHEAPEST FALSIFIER:** exhaustive computation of the *actual* bad set (the `MCA.lean`
definition, in the equivalent form of `BadSetCorrelatedCharacterisation.lean`) for lines whose
coefficient words are supported on a set `E` of prescribed size `u`, at parameters where the
open window is nonempty — `analysis/near_u_window_probe.py`.  Witness polynomials are
enumerated exhaustively by interpolating through every `k`-subset of the domain.

**RESULT** (`q = 17`, `n = 16`, `k = 4`; `√(kn) = 8`, so the window is
`max(n−k−e, e) < u ≤ 8`):

```
   e = 6, u = 7   (window (6,8])    max #Bad = 7  =  e + 1
   e = 6, u = 8   (window (6,8])    max #Bad = 7  =  e + 1
   e = 7, u = 8   (window (7,8])    max #Bad = 8  =  e + 1
   e = 5, u = 8   (window (7,8])    max #Bad = 2  <  e + 1
   e = 5, u = 6   (proved region)   max #Bad = 6  =  e + 1   (bound sharp)
```

All these radii are inside the Johnson radius (`(n−e)² > n(k−1)`).  **No violation of
`#Bad ≤ e + 1` was found anywhere in the open window**, and the bound is attained, so it cannot
be lowered.

**RADIUS BEFORE:** `0.177124` at `ρ = 1/2` (`nearFar_rho_half`).

**RADIUS AFTER IF TRUE:** if `(NEAR-u)` holds down to a near threshold `τ₀`, the far half only
needs the Johnson condition `t² > n(τ₀ − 1)`.  With `τ₀ = √(kn)` (the extent actually probed)
the combined ceiling becomes `1 − ρ^{1/4}` = `0.159104 / 0.292893 / 0.405396 / 0.5`, i.e. it
would *not* improve `ρ = 1/2` but would lift `ρ = 1/4, 1/8, 1/16` to the exact pair-covering
ceiling with the far better constant `e + 1` in place of the squared list size
(`Δδ ≈ +0.006 / +0.007 / +0.008`).  With `τ₀ = k` it would be the full Johnson radius
`1 − √ρ` — but `τ₀ = k` is *not* supported by any evidence here and is exactly the regime the
`(CL)` probe of §6 shows to be unstructured.

**EXPECTED BIT GAIN:** `0` at `ρ = 1/2`; `≈ +0.9 / +1.3 / +1.7` bits over 128 queries at the
three lower rates, for `τ₀ = √(kn)`.

**SCALABLE COUNTEREXAMPLE:** none found.

**NOVELTY STATUS:** unknown; the statement is a shortened-code question about lines supported
on a small set, and should be pre-screened against the interleaved-RS and shortening literature
before any formalisation (NOVELTY GATE items 1–3).

**RESEARCH SCORE:** `P_success` MEDIUM, `V_radius` LOW (at `ρ = 1/2`) / MEDIUM (lower rates),
`V_novelty` UNKNOWN, `C_research` MEDIUM.

**DECISION:** **CONTINUE — but hand to the external pre-screen first**, per the constitution's
formalisation budget (a candidate must have a quantitative radius implication *and* survive the
novelty gate before Lean).  The exact statement to pre-screen is `(NEAR-u)` as printed in §7,
with the added empirical claim `#Bad ≤ e + 1` throughout the window.

**NEXT SINGLE TEST (queued):** determine the largest `τ₀` for which `#Bad ≤ e + 1` *fails*, by
adversarial (not random) construction: prescribe `m` challenges `γ_j`, codewords `c_j` and
agreement sets `S_j`, and solve the linear system `a₀ + γ_j a₁ = c_j` on `S_j`.  Dimension
counting gives `m ≤ 2n/(n − e − k)` = `2/(1 − δ − ρ)` — a *constant*, e.g. `8` at
`ρ = 1/2, δ = 1/4` and `9.66` at the Johnson radius — which is the first quantitative hint that
`#Bad` stays `O(1)` all the way to Johnson and that the obstruction is entirely in the proof,
not in the truth.  Confirming or refuting that counting bound by exact construction is the
cheapest next probe.

---

## 9. CHECKPOINT — (NEAR-u) in the open window: **REFUTED** (supersedes §8)

**Correction to §8.**  The verdict recorded in §8 ("SURVIVES falsification", `max #Bad = e+1`)
was obtained from *randomly sampled* coefficient pairs (`analysis/near_u_window_probe.py`,
80 samples per point).  It is **wrong**.  Under an *adversarial* construction the bound
`#Bad ≤ e + 1` fails throughout the open window.  §8 is retained above as the record of what
the random probe showed; the statement it endorses is false.  Full account and certificates:
**`NEAR_U_KILL_REPORT.md`**, code `analysis/near_u_adversarial_kill.py`,
`analysis/near_u_counterexample.py`, `analysis/near_u_maxbad_search.py`.

**CURRENT BOTTLENECK:** `(NEAR-u)`.

**CHEAPEST FALSIFIER:** superimpose the two badness mechanisms at `u = e + 1`.

* *zero-codeword witnesses*: each `x ∈ E` contributes the bad challenge
  `γ_x = −a₀(x)/a₁(x)`; the witness sets are disjoint, so this mechanism alone gives at most
  `⌊u/(u−e)⌋` bad challenges — which is exactly `e + 1` at `u = e + 1`.  **The conjectured
  ceiling `e+1` is just this value; it is not a barrier.**
* *maximal root collision*: with all `e` errors outside `E` and `R ⊆ D \ E`, `|R| = n−u−e`,
  the polynomial `g = Π_{x∈R}(X − x)` has `deg g < k` exactly when `e ≥ (n−k)/2`, and agrees
  with `a₀ + γ* a₁` on `E ∪ R`, a set of size `n − e`; `a₁` is far there whenever `a₁|E` is
  not a scalar multiple of `g|E`.  Cost `n − k − e < u` linear conditions.

Setting `a₀|E = g|E − γ*·a₁|E` with the ratios `g(x)/a₁(x)`, `x ∈ E`, pairwise distinct makes
all `e + 2` challenges bad simultaneously.

**RESULT:** certified `#Bad ≥ e + 2` (and `≥ e + 3` with two root sets) at

```
   (n,k,e) = (7,1,3) (9,1,4) (8,2,3) (12,3,5) (24,12,6) (32,16,8) (64,32,16)
             (128,64,33) (128,64,36),      q = 11, 13, 17, 23, 37, 67, 101, 137,
             1009, 10007, 2³¹−1
```

and the *exhaustive* bad set on the minimal instances is `#Bad = 2(e+1)`, independent of `q`
over four orders of magnitude.  At `ρ = 1/2` the family exists for every `n ≥ 24` and every
`δ ∈ [(1−ρ)/2, 1−√ρ)`.

**SCALABLE COUNTEREXAMPLE:** **yes** — `(n−k)/2 ≤ e` and `e+1 ≤ n − ⌈√(kn)⌉` is the whole
window, so the family scales in `n` at every rate and over every field.

**RADIUS BEFORE / AFTER:** `0.177124` at `ρ = 1/2`, unchanged.  Even *if* `(NEAR-u)` had been
true its symbolic optimum is

```
   δ_max^{NEAR-u}(ρ) = max{ (3 − √(5+4ρ))/2 , 1 − ρ^{1/4} }   (self-consistent branch)
   δ_max^{NEAR-u}(1/2) = (3 − √7)/2 = 0.177124344…  =  the radius already certified.
```

**Δδ = 0, bit gain 0 at `ρ = 1/2`; the frontier `1/4` is not crossed under any version of the
conjecture inside its own window.**

**NOVELTY STATUS:** none.  The killing mechanism is the near-codeword-line (spike) geometry
already Lean-verified in `SpikeLineCounterexample.lean`.

**RESEARCH SCORE:** `P_success` 0, `V_radius` 0, `V_novelty` 0.

**DECISION:** **KILL `(NEAR-u)`.  Do not formalise** (the negative result adds no mathematics
beyond the existing spike family).  **Return to `ND∃` / `(DICH)`**, the only route with a
nonzero radius payoff (`Δδ = +0.115769`, `+27.99` bits over 128 queries at `ρ = 1/2`).

**NEXT SINGLE TEST:** run the same adversarial construction against the near half of `(DICH)`:
for lines at distance exactly `u` from the codeword-line variety, measure `max #Bad`
adversarially as a function of `(u, e, n−k)` and fit the true law — the present data says
`#Bad ≈ u/(u−e) + O(u/(n−k−e))`, capped by the list size.  `(DICH)` is worth pursuing only if
that law, combined with the far half's Johnson condition, still admits `δ > 1/4` at `ρ = 1/2`.
