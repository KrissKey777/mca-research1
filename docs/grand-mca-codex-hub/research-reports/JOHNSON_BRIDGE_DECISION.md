# MASTER MISSION — PROVE OR KILL THE PROXIMITY MASTER THESIS

**Verdict: D — UNIQUE BOTTLENECK IDENTIFIED.**

One precise missing lemma, `(ND∃)` below, whose proof moves the certified plain-Reed–Solomon
MCA radius from `(1−ρ)/2` to `1 − √ρ − 2⁻¹⁰` at both prize parameter sets, with
`ε_mca ≤ 2⁻¹²⁸` and no other change.  Everything else on that route is now admit-free in this
repository.

Along the way the mission's PHASE 1 produced two hard results that were *not* previously
known here, both formalized and sorry-free:

* the `∀`-form of the non-degeneracy hypothesis that the repository's Johnson-radius
  certificates were carrying is **false** at both prize schedules, so those certificates were
  vacuous as stated (`nd_forall_false_rho_half`, `nd_forall_false_rho_quarter`);
* the unconditional unique-decoding mechanism has an **exact structural barrier** at
  `k + 2e = |D|`: strictly past that point its central object does not exist at all
  (`forcing_not_unique_beyond_frontier`).

The chain has been repaired under the satisfiable `∃`-form with the *same* constants
(`threshold_rho_half_bchks_exists`, `threshold_rho_quarter_bchks_exists`).

---

## PHASE 0 — the exact claim

For a Reed–Solomon evaluation domain `D ⊆ F` with `n = |D| = 2²⁰`, dimension `k = ρn`, and
the line challenge family `γ ↦ f₀ + γ·f₁`:

> `IsBad k e f₀ f₁ γ` — there is `S ⊆ D` with `|S| ≥ n − e` such that `f₀ + γ f₁` agrees on
> `S` with a polynomial of degree `< k`, but *not every* point of the line does.
> `epsMCAmax k e D = max_{f₀,f₁} |badSet k e f₀ f₁| / |F|`.

Target theorem, in one line:

> `epsMCAmax k e D ≤ 2⁻¹²⁸` for `e = ⌊n(1 − √(ρ + 1/n) − 2⁻¹⁰)⌋` and `|F| ≥ 2¹⁶⁰`,
> at `ρ = 1/2` (`k = 524288`, `e = 306096`) and `ρ = 1/4` (`k = 262144`, `e = 523263`).

Maximum `#Bad` compatible with `2⁻¹²⁸` at `|F| ≥ 2¹⁶⁰` is `2³²`, which is exactly the constant
the BCHKS schedule of this repository achieves.

---

## CURRENT RADIUS FRONTIER

| family | radius | status | statement |
|---|---|---|---|
| plain RS | `δ ≤ (1−ρ)/2` (`k + 2e ≤ n`), `#Bad ≤ (k+1)e + 1` | **unconditional, admit-free** | `Subresultant.card_badSet_le_unconditional` |
| plain RS | `δ < (1−ρ)/3` (`3e < n−k+1`), `#Bad ≤ n` | unconditional | `card_badSet_le` |
| plain RS | `δ = 1 − √ρ − 2⁻¹⁰`, `#Bad ≤ 2³²` | **conditional on (ND∃)** | `threshold_rho_*_bchks_exists` |
| folded RS | `δ ≤ 1 − ρ − η` (capacity) | unconditional, admit-free | `Folded.foldedRS_epsMCA_unconditional` |

The plain-RS unconditional frontier is `(1−ρ)/2`.  The folded-RS capacity result is for a
genuinely different code family and does **not** transfer (see the KILL log below).

## JOHNSON TARGET

`δ < 1 − √ρ`; concretely `δ = 1 − √(ρ + 2⁻²⁰) − 2⁻¹⁰`, i.e. `e = 306096` at `ρ = 1/2` and
`e = 523263` at `ρ = 1/4`, versus the frontier radii `e = 262144` and `e = 393216`.

---

## PHASE 1 — KILL THE CURRENT MACHINERY

### 1.1 The forcing mechanism: structural KILL at exactly `k + 2e = n`

Every unique-decoding-regime bound here — Welch–Berlekamp/subresultant pencil, canonical
`W_can`, syndrome recurrence of order `e`, top Hankel determinant, cumulative Hankel rank,
support/incidence machinery — runs through one common step.  Two bad challenges `γ ≠ γ'`
carry agreement sets `S_γ, S_{γ'}` of size `≥ n − e`; on the intersection, of guaranteed size
only `n − 2e`, the two agreeing codewords `p_γ, p_{γ'}` determine a *pair*

```
q₁ = (p_γ − p_{γ'})/(γ − γ'),   q₀ = p_γ − γ q₁,
```

and the argument needs this pair to be the *same* for all choices of `γ, γ'` — which is
exactly uniqueness of interpolation on `n − 2e` points.

**Result (formalized).**

* `forcing_unique_at_frontier` — for `k + 2e ≤ n` the guaranteed intersection has `≥ k`
  points and the recovered pair is unique.
* `exists_two_interpolants_of_card_lt`, `forcing_not_unique_beyond_frontier` — for
  `n < k + 2e` the guaranteed intersection has `≤ k − 1` points, and on **every** such set
  and for **every** data the recovered codeword is never unique: `p` and `p + ∏_{x∈S}(X−x)`
  are two distinct degree-`< k` polynomials realising it.
* `forcing_guaranteed_size_ge_iff` — the switch is at exactly one point, `n − 2e ≥ k`.

This is a rank/degree obstruction on the mechanism, not a lossy estimate.  It is *not* a
refutation of MCA past `(1−ρ)/2` — MCA does hold up to Johnson.  It says the determinant /
locator / subresultant formalism cannot express the Johnson mechanism, because its only route
to a canonical codeword pair is uniqueness of interpolation, and past the frontier there is no
canonical pair to extract.  Any Johnson-range route must replace "one codeword" by "an
interpolation object for the whole line", which is precisely what the Guruswami–Sudan
interpolant does.

**Verdict per mechanism: structural KILL for all six**, since all six factor through the same
forcing step.

### 1.2 The Johnson-range route already present: a hidden vacuity

The repository already contains a Johnson-radius chain — `epsMCAmax_le_bchks_nat`,
`epsMCAmax_le_bchks_disc`, `epsMCAmax_le_bchks_linear`, `exists_const_epsMCAmax_le_bchks`,
`epsMCAmax_le_of_schedule`, `threshold_rho_half_bchks`, `threshold_rho_quarter_bchks`,
`epsMCAmax_le_bchksRHS_rho_half`, `epsMCAmax_le_bchksRHS_rho_quarter` — sorry-free, but each
carrying the hypothesis

```
(ND∀)  ∀ f₀ f₁, (badSet k e f₀ f₁).Nonempty →
         ∀ Q, LineInterpolant k L m bY dZ D f₀ f₁ Q → ∃ x₀, discLine bY x₀ Q ≠ 0.
```

**(ND∀) is false**, and the proof is three lines of algebra:

1. *The interpolation conditions are multiplicative.*  If `Q₀` interpolates the formal line
   `f₀ + Z f₁` with multiplicity `m₀`, weighted degree `< L₀`, `Y`-degree `≤ bY₀`,
   `Z`-degree `≤ dZ₀`, then `Q₀²` interpolates it with multiplicity `2m₀`, weighted degree
   `< 2L₀ − 1`, `Y`-degree `≤ 2bY₀`, `Z`-degree `≤ 2dZ₀`
   (`GS.hasMultAt_mul`, `GS.wdegLt_mul`, `GS.zdegLe_mul`, `LineInterpolant.sq`).
2. *A square is discriminant-degenerate.*  `discLine bY x₀ (S²) = 0` for every `x₀`
   (`discLine_eq_zero_of_isSq`), because a repeated factor kills the resultant of the
   polynomial and its derivative — and if the specialisation is constant, the derivative
   column of the Sylvester matrix is zero (`discRes_eq_zero_of_natDegree_eq_zero`).
3. *Lines with a bad point exist.*  The spike `f₀ = δ_{x₀}`, `f₁ = −f₀` has `γ = 1` bad
   whenever `1 ≤ k` and `k + e + 1 ≤ n` (`exists_badSet_nonempty`), so the hypothesis
   "`badSet` nonempty" does not save (ND∀).

So (ND∀) fails as soon as the Guruswami–Sudan counting condition still holds after *halving*
the schedule.  It does, at both prize parameter sets, using the sharpened monomial count
`2k·#monIdx(k,L) ≥ L² + kL` (`GS.card_monIdx_ge'`, `count_of_clean'`):

| | `k` | `e` | `L` | `m` | `bY` | `dZ` | `L₀` | `m₀` | `bY₀` | `dZ₀` | count margin |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `ρ=1/2` | 524288 | 306096 | 642769488 | 866 | 1225 | 1318349 | 321384744 | 433 | 612 | 659174 | ×1.00048 |
| `ρ=1/4` | 262144 | 523263 | 403177215 | 768 | 1537 | 1182344 | 201588608 | 384 | 768 | 591172 | ×1.0000017 |

(`2m₀ ≥ m`, `2L₀ ≤ L+1`, `2bY₀ ≤ bY`, `2dZ₀ ≤ dZ` in every column.)

Formalized as `nd_forall_false` (general) and `nd_forall_false_rho_half`,
`nd_forall_false_rho_quarter` (the two prize instances).  **Consequence: those nine
statements were vacuous.**  The bit gain they appeared to certify was 0.

### 1.3 The repair

`epsMCAmax_le_disc_of_bad` already takes the existential form

```
(ND∃)  ∀ f₀ f₁, (badSet k e f₀ f₁).Nonempty →
         ∃ Q x₀, LineInterpolant k L m bY dZ D f₀ f₁ Q ∧ discLine bY x₀ Q ≠ 0,
```

which the square construction does **not** refute: a square is one interpolant among many,
and the existential asks for one good one.  The schedule packaging and the two prize
certificates are re-derived under (ND∃) with the same constants:
`epsMCAmax_le_of_schedule_exists`, `threshold_rho_half_bchks_exists`,
`threshold_rho_quarter_bchks_exists`.  The Guruswami–Sudan counting condition is no longer
needed there — under (ND∃) the interpolant is supplied by the hypothesis itself.

---

## PHASE 2 — MISSING ALGEBRAIC INGREDIENT

The implication chain of the Johnson-range argument, with the repository status of each step:

```
many good challenges γ on a line
  ⇒ [PRESENT]  a Guruswami–Sudan interpolant Q(X,Y,Z) of the *formal* line f₀ + Z f₁
               exists inside the budget (L, m, bY, dZ)
               — GS.exists_line_interpolating, exists_lineInterpolant
  ⇒ [MISSING]  (ND∃) some such Q, at some x₀, has Q(x₀,Y,Z) of full Y-degree bY and
               squarefree in Y, i.e. discLine bY x₀ Q ≠ 0
  ⇒ [PRESENT]  every bad γ is a root of discLine bY x₀ Q as a polynomial in Z
               — eval_discLine_eq_zero_of_agreement (via (X − p)² ∣ Q|_{Z=γ})
  ⇒ [PRESENT]  #Bad ≤ deg_Z discLine ≤ (bY + (bY−1))·dZ ≤ 2³²
               — epsMCA_le_disc, epsMCAmax_le_disc_of_bad
  ⇒ [PRESENT]  ε_mca ≤ 2³²/|F| ≤ 2⁻¹²⁸  for |F| ≥ 2¹⁶⁰
```

So the essential object is **multiplicity interpolation with a non-degenerate discriminant**,
and the single missing step is the *non-degeneracy of one interpolant*.  All of
bivariate/multiplicity interpolation, the weighted-degree polynomial, the determinant/minor
vanishing, and the `#Bad ≤ degree` conversion are already in place.

### The unique bottleneck

> **(ND∃)** For the schedule `(k, L, m, bY, dZ)` and any `f₀, f₁ : D → F` whose bad set is
> nonempty, there exist a Guruswami–Sudan interpolant `Q` of the formal line `f₀ + Z f₁`
> inside the budget and a point `x₀ ∈ F` such that `Q(x₀, Y, Z)` has `Y`-degree exactly `bY`
> and is squarefree in `Y` over `F[Z]`.

Equivalently (`discLine_ne_zero_of_isCoprime`): `Q(x₀,·,·)` and `∂_Y Q(x₀,·,·)` are coprime
over `F[Z]` with degrees `bY` and `bY − 1`.

Why it is genuinely the crux, and why it is not free: the interpolation conditions cut out a
**linear** subspace `V` of interpolants, and `V` is closed under nothing that forces
squarefreeness — indeed §1.2 shows `V` always contains squares.  (ND∃) is the statement that
`V` is not *entirely* degenerate.  It is a Zariski-open condition on `V`, so it is either
generic or identically false, and deciding which is exactly the content of the
Johnson-radius argument.

---

## CHEAP COUNTEREXAMPLE

For (ND∀): `Q₀²` at the halved schedule, on the spike line `f₀ = δ_{x₀}`, `f₁ = −δ_{x₀}`.
Scalable: it works at every rate and radius for which the halved schedule meets the counting
condition, and both prize instances do, with margin.  Formalized.

For the forcing mechanism: `p` versus `p + ∏_{x∈S}(X−x)` on any `S` of `k−1` points.
Scalable: it works over every field, at every `k`, for every prescribed data.  Formalized.

For (ND∃): **none found.**  No small-parameter obstruction was identified; (ND∃) survives.

---

## DEGREE / BAD-SET BUDGET

`#Bad ≤ deg_Z discLine bY x₀ Q ≤ (bY + (bY−1))·dZ`.

| | `bY` | `dZ` | `(2bY−1)·dZ` | `≤ 2³²`? | `ε_mca` at `|F| = 2¹⁶⁰` |
|---|---|---|---|---|---|
| `ρ = 1/2` | 1225 | 1318349 | 3 228 636 701 | yes (`2³² = 4 294 967 296`) | `≤ 2⁻¹²⁸` |
| `ρ = 1/4` | 1537 | 1182344 | 3 633 343 112 | yes | `≤ 2⁻¹²⁸` |

The budget gate is met: `B = 2³² ≤ |F|·2⁻¹²⁸` for `|F| ≥ 2¹⁶⁰`.

## EXPECTED BIT GAIN

The bottleneck of the deployed soundness expression is the `(1−δ)ᵗ` term, so the gain is in
the radius, not in `#Bad`.  Moving `δ` from `(1−ρ)/2 = 0.25` to `1 − √ρ − 2⁻¹⁰ ≈ 0.2920`
at `ρ = 1/2`, and from `0.375` to `≈ 0.4990` at `ρ = 1/4`:

| | `δ` frontier | `δ` Johnson | `log₂(1−δ)` gain per repetition |
|---|---|---|---|
| `ρ = 1/2` | 0.25000 | 0.29192 | 0.0830 bits |
| `ρ = 1/4` | 0.37500 | 0.49902 | 0.3191 bits |

At `t = 128` repetitions that is `+10.6` bits at `ρ = 1/2` and `+40.8` bits at `ρ = 1/4`;
at the `t = 202` schedule, `+16.8` and `+64.5` bits.  In all cases strictly positive, so the
route passes the PHASE 5 / PHASE 6 gates.  Conversely the bit gain of any further `#Bad`
improvement inside the current radius is **0**, confirming the mission's premise.

## FORMALIZATION COST

Zero for everything except (ND∃): the entire chain from (ND∃) to `ε_mca ≤ 2⁻¹²⁸` at both
prize parameter sets is already admit-free in this repository, in the two theorems
`threshold_rho_half_bchks_exists` and `threshold_rho_quarter_bchks_exists`.  Proving (ND∃)
alone converts them to unconditional theorems with no other change.

---

## KILL LOG — routes examined and closed

| route | why killed |
|---|---|
| sharpen `#Bad` inside `(1−ρ)/2` | `Δbits = 0`; the soundness bottleneck is `(1−δ)ᵗ`, not `ε_mca ≈ 2⁻¹⁵⁴` |
| Welch–Berlekamp / subresultant pencil, `W_can`, order-`e` syndrome recurrence, top Hankel determinant, cumulative Hankel rank, support/incidence extremal locus | all factor through the forcing step; structural KILL at `k + 2e = n` (`forcing_not_unique_beyond_frontier`) |
| keep the existing Johnson certificates as they stand | hypothesis (ND∀) is **false** (`nd_forall_false_rho_half`, `nd_forall_false_rho_quarter`) |
| transfer the repository's unconditional folded-RS capacity bound (`Folded.foldedRS_epsMCA_unconditional`, `δ ≤ 1−ρ−η`) to plain RS by regrouping the smooth prize domain into blocks of size `s` | folding preserves the rate but multiplies the *relative* radius by `s`: a plain-RS radius `δ` becomes a folded radius `sδ`, so the capacity condition `sδ ≤ 1−ρ−η` certifies only `δ ≤ (1−ρ−η)/s`, strictly worse than `(1−ρ)/2` for every `s ≥ 2`. Regrouping alone gains nothing; the folded result needs the genuinely folded alphabet |
| build a general Guruswami–Sudan library | forbidden by the STOP RULE, and unnecessary: the GS side of the chain is already present, and the missing step is a single non-degeneracy statement about it |
| beyond Johnson | not attempted; the Johnson target is not yet settled |

---

## DECISION

**DECISION: HOLD on the Johnson target — outcome D.**

The mechanism study is complete and decisive: the six unique-decoding mechanisms are
structurally dead at `(1−ρ)/2`, the previously recorded Johnson certificates were vacuous,
and after repair the Johnson-radius route rests on exactly one open statement, (ND∃), whose
proof would raise the certified plain-RS proximity radius from `(1−ρ)/2` to `1 − √ρ − 2⁻¹⁰`
at both prize rates with `ε_mca ≤ 2⁻¹²⁸`, for `+10.6` and `+40.8` bits at `t = 128`.

---

## Lean artifacts added by this mission

`RequestProject/Root/CodingTheory/NonDegeneracyExists.lean`

| declaration | content |
|---|---|
| `GS.hasMultAt_mono`, `GS.hasMultAt_mul` | multiplicity conditions are monotone and multiplicative |
| `GS.wdegLt_mul`, `GS.zdegLe_mul` | weighted and `Z`-degree bounds are additive under products |
| `discRes_eq_zero_of_natDegree_eq_zero` | zero derivative column ⇒ zero formal-degree discriminant |
| `discLine_eq_zero_of_isSq` | the line discriminant of a square vanishes at every point |
| `LineInterpolant.sq` | `Q₀²` is an interpolant at the doubled schedule |
| `GS.card_monIdx_ge'` | sharpened monomial count `2k·#monIdx(k,L) ≥ L² + kL` |
| `count_of_clean'` | the sharpened counting condition implies the interpolation-existence condition |
| `exists_badSet_nonempty` | a line with a bad point exists at every rate and radius in range |
| `nd_forall_false` | **(ND∀) is false whenever the schedule can be halved** |
| `nd_forall_false_rho_half`, `nd_forall_false_rho_quarter` | the two prize instances |
| `epsMCAmax_le_of_schedule_exists` | the schedule packaging under (ND∃) |
| `threshold_rho_half_bchks_exists`, `threshold_rho_quarter_bchks_exists` | `ε_mca ≤ 2⁻¹²⁸` at `δ = 1 − √ρ − 2⁻¹⁰` under (ND∃) |

`RequestProject/Root/CodingTheory/ForcingBarrier.lean`

| declaration | content |
|---|---|
| `exists_two_interpolants_of_card_lt` | fewer than `k` points never determine a degree-`< k` codeword |
| `forcing_unique_at_frontier` | at `k + 2e ≤ n` the forcing step has a unique output |
| `forcing_not_unique_beyond_frontier` | strictly beyond, it has no output on the guaranteed intersection |
| `forcing_guaranteed_size_ge_iff` | the switch is exactly `k + 2e = n` |

All sorry-free; axiom audits in `RequestProject/Main.lean` show only
`propext, Classical.choice, Quot.sound`.
