# MCA mission report — the specialisation-free pair resultant and the far-centre dividing line

Everything marked **Lean** is machine-checked in this repository, `sorry`-free, with axioms
exactly `propext, Classical.choice, Quot.sound` (verified through `RequestProject/Main.lean`;
full build at the end of this run: `lake build`, **8295 jobs, completed successfully, no
`sorryAx`**).  Everything marked **exact computation** is deterministic finite-field
arithmetic in `analysis/`, *not* Lean-verified.

New files: `RequestProject/Root/CodingTheory/PairResultantBiv.lean`,
`RequestProject/Root/CodingTheory/CarrierDichotomy.lean`,
`analysis/co_exists_far_centre_probe.py`.
Repaired (pre-existing build failure, untouched since the initial commit, three
Mathlib-drift errors): `RequestProject/Root/CodingTheory/QuadraticFactorBranch.lean`.

---

## 0. The shortest route was tested first, and it is **blocked, but not where it was thought
to be**

The requested first test was whether the BCHKS Johnson-range proximity-gap theorem plus the
project's `FarCenterProximity` equivalences already deliver the far-centred MCA bound.

* The bridge is **already machine-checked and is not the obstruction**:
  `Root.CodingTheory.badSet_eq_goodZ_of_far` (for `e < d(f₀,C)` the MCA bad set *equals* the
  set of close challenges) and `grandMCA_iff_proximityGap` (a uniform MCA bound for
  far-centred lines *is* a uniform proximity gap).  Anything proved on the proximity side
  transfers with no loss.
* What is missing is the Johnson-range proximity statement **itself** as an admit-free
  theorem.  Per `KOALAIRS12_PRIZE_GAP_AUDIT.md` §6 this is exactly the one external admit on
  the numeric path (`CapacityBounds.rs_mcaError_le_in_johnson_range`), and the audit's own
  sensitivity analysis shows that (i) the *constant* is worth **0 bits** — any `B ≤ 2^98`
  suffices at `|F| = 2^185.93` — and (ii) the only lever is the **radius**.  So the target is
  precisely: *any* `poly(n)` bad-set bound at radius `δ < 1 − √ρ`, admit-free.
* Therefore no shortcut exists: the Johnson-range theorem has to be proved, and the project's
  route to it is the Guruswami–Sudan chain over `F[Z]`.

## 1. Strongest theorem obtained

**`Root.CodingTheory.PairResBiv.card_goodZ_le_pairResBiv` (Lean).**
Let `Q, Q'` be two formal-line Guruswami–Sudan interpolants of the line `γ ↦ f₀ + γ f₁`
(`LineInterpolant k L m bY dZ D f₀ f₁ Q`, resp. `bY'`), with `1 ≤ bY` and the root margin
`L ≤ m·(|D| − e)`.  Put

```
pairResBiv bY bY' Q Q'  :=  Res_Y(Q, Q')  ∈  F[Z][X]      -- no specialisation of X
```

If `pairResBiv bY bY' Q Q' ≠ 0` then

```
#{ γ : d(f₀ + γ f₁, C) ≤ e }  ≤  (bY + bY')·dZ ,
```

and consequently (`card_badSet_le_pairResBiv`, `epsMCA_le_pairResBiv`,
`epsMCAmax_le_pairResBiv`) `#Bad ≤ (bY + bY')·dZ` and `ε_mca ≤ (bY+bY')·dZ / |F|`, for every
line — nothing is assumed about the centre for the *upper* bound, since `Bad ⊆ Close`.

Why this is the strongest form available: the hypothesis is the **weakest non-degeneracy
condition anywhere in the chain**.

* It is implied by the previous one at *every* point:
  `pairRes bY bY' x₀ Q Q' = (pairResBiv bY bY' Q Q').eval (C x₀)`
  (`pairRes_eq_eval_pairResBiv`), hence
  `pairResBiv_ne_zero_of_pairRes_ne_zero`.  The old statement needed a specialisation point
  `x₀ ∉ D` (forced by `pairRes_eq_zero_of_mem_domain`) **and** a field-size condition; both
  disappear.
* It is strictly weaker than separability `discBiv Q ≠ 0` (`SubJohnsonBCHKS`), which is
  refuted for *every* admissible interpolant of a spike line.
* Mechanism: Mathlib's Bézout identity `Polynomial.exists_mul_add_mul_eq_C_resultant` makes
  `Res_Y(Q,Q')` a `Y`-free element of the ideal `(Q,Q')`, so
  `WitnessElimination.card_le_natDegree_of_yfree_combination` applies verbatim; the
  `Z`-degree bound is transported through the inner swap of `FactorDegreeBounds`
  (`natDegree_coeff_pairResBiv_le`).

**Companion theorem, uniform in the `Y`-degree** (`CarrierDichotomy.lean`, Lean).  For *any*
factorisation `Q = S.prod` (multiset `S`) of a trivariate polynomial killed by every close
witness: either

```
#Close  ≤  |S| · |D| · (dZ + L)          (and #Bad ≤ the same, for a far centre)
```

or **some factor of `Q` vanishes identically along the formal line at all but `e`
positions** (`card_le_or_exists_degenerate_factor`,
`card_badSet_le_or_exists_degenerate_factor`, and with `|S| ≤ deg_Y Q` in
`card_badSet_le_or_exists_degenerate_factor_natDegree`).  This replaces the per-`Y`-degree
case analysis of the degenerate branch (linear factors, quadratic factors, …) by one
inequality: the recursion over factors is done by the multiset product, and a witness kills a
product iff it kills a factor, because `subst γ p` is a ring homomorphism into the domain
`F[X]`.

## 2. Machine-checked?

Yes.  All statements listed above are `sorry`-free and axiom-clean, wired into
`RequestProject/Main.lean` with `#print axioms`.  The empirical statement in §4 is **not**
Lean-verified and is labelled as exact computation.

## 3. Exact MCA / Prize consequence

Write `(CO∃-far)` for the hypothesis now isolated in Lean as
`Root.CodingTheory.PairResBiv.COExistsFar`:

> every line with a **far** centre (`e < d(f₀,C)`) admits two admissible formal-line
> interpolants with `Res_Y(Q,Q') ≠ 0`.

Then `card_badSet_le_of_coExistsFar` / `card_goodZ_le_of_coExistsFar` (Lean) give
`#Bad ≤ (bY + bY')·dZ` for every far-centred line, at *whatever radius the interpolation
schedule supports* — i.e. on the whole Johnson range, since the schedule condition is only
`L ≤ m(|D| − e)` plus the existence of the interpolant
(`GS.exists_line_interpolating`).

Quantitatively, at the prize profile (`|F| = 2^185.93`, `n = 2^16`, the audit's free region
`B ≤ 2^98`): admissible schedules give `(bY + bY')·dZ = poly(n)` far inside the free region —
`O(n²)`-type numbers, i.e. `≈ 2^32`, with `2^66` of margin.  So under `(CO∃-far)` the
exponent question is not binding at all; what is bought is the **radius**, worth
`+17.2 bits` at `ρ = 1/2, t = 202` (audit §5), i.e. the whole gap between the current
admit-free frontier `δ ≤ max((1−ρ)/2, 1 − ρ^{1/3})` and the Johnson radius `1 − √ρ`.

No new *unconditional* radius is claimed by this run.  The certified unconditional frontier
is unchanged: `δ ≤ (1−ρ)/2` (unique decoding) and `δ < 1 − ρ^{1/3}` (TripleCluster).

## 4. The single remaining obstruction — and a correction to its status

The obstruction is exactly `(CO∃-far)`.

`ND_EXISTS_MISSION_REPORT.md` records `(CO∃)` — "two coprime admissible interpolants exist" —
as **refuted**, by the spike-line family, and that verdict is what closed this route in an
earlier run.  The new observation of this run is:

> **Every member of the refuting family has a centre at distance 1 from the code.**
> `spikeF0 = p₀ + a·δ_i` gives `d(f₀,C) = 1`, so as soon as `e ≥ 1` the refutation lives
> entirely in the *near*-centre regime — which is precisely the regime that
> `badSet_eq_goodZ_of_far` removes from the problem, and which is covered by the separate
> near-word machinery (`NearDirectionBadSet`, `NearCodewordLineMCA`).

Exact computation (`analysis/co_exists_far_centre_probe.py`, GF(31) and GF(37), `n = 12`,
`k = 3`, `e = 5` — strictly beyond the unique-decoding radius `δ = 0.375` and strictly inside
the Johnson radius `δ = 0.5`, multiplicity 1, `B = 6`, `dZ = 9`, interpolation module computed
by exact linear algebra, resultant by exact Sylvester determinant over `GF(p)[Z,X]`):

| line | `d(f₀,C)` | module dim | `Res_Y(Q₁,Q₂) ≠ 0` |
|---|---|---|---|
| random, **far** centre (14 trials, two fields) | 7–8 | 26 | **True, 14/14** |
| centre at distance 1, random direction (3 trials) | 1 | 30 | False, 0/3 |
| spike line (pair agrees with a codeword line on `n−1`) | 1 | 70 | False, 0/2 |

So the far-centre hypothesis is empirically the exact dividing line for the non-degeneracy,
and `(CO∃-far)` is **not** refuted by anything currently in the project or, as far as this run
could determine, in the literature.  It is open.

For completeness, the same obstruction in the factor language of `CarrierDichotomy`: the open
branch is "some irreducible factor of the interpolant vanishes identically along the formal
line at all but `e` positions".  For factors of `Y`-degree `1` this is the scaled/rational
witness family, already bounded over a far centre
(`WitnessElimination.card_goodZ_le_of_scaled_witness_family`,
`QuadraticFactorBranch.card_le_of_scaled_linear_factor`); the open case is `Y`-degree `≥ 2`,
which the dichotomy now handles uniformly *provided* the branch is excluded.

## 5. Shortest next attack

Prove `(CO∃-far)`, in the following order — each step is a strictly smaller statement than the
previous route required, and the first two are the ones the measurements point at.

1. **Common factor ⇒ line degeneracy.**  Combine `ResultantDichotomy`
   (`exists_irreducible_common_factor_of_forall_not_isCoprime`: if no two module elements are
   coprime, the whole module is divisible by one irreducible `G`) with
   `CarrierDichotomy.card_le_or_exists_degenerate_factor` applied to `G`.  This reduces
   `(CO∃-far)` to: *a far-centred line has no irreducible `G` in the interpolation module's
   common divisor with `|lineSupport G| ≥ |D| − e`.*  Nothing else remains.
2. **Kill the degenerate factor with the far centre.**  For `deg_Y G = 1` this is done.  For
   `deg_Y G ≥ 2` the statement to prove is: if `(Y − v_x)` divides `G(Z,x,Y)` in `F[Z][Y]` for
   `≥ |D| − e` positions `x`, then `f₀` is `e`-close to the code.  The `Z⁰`-coefficient of the
   divisibility gives `G(0,x,f₀x) = 0` on those positions, so what has to be added is a
   *degree* input forcing the relevant root of `G(0,x,·)` to be the evaluation of a
   polynomial of degree `< k`; the natural source is the witness itself (`p_γ` has degree
   `< k` and is a root of `G^γ`), i.e. a rational-parametrisation argument for the branch of
   `G` through the line, over the function field of `G` rather than over `F(Z)`.
3. **If (2) resists, weaken the target rather than the radius**: `(CO∃-far)` only has to hold
   for *one* schedule per line, and multiple interpolation sources are admissible (different
   `m`, `bY`, `dZ`).  A common factor of two *different* schedules is a strictly stronger
   degeneracy than a common factor of one module, and the dimension obstruction for `G²`
   applies to the union of the modules.
4. Measurement to run before (2): the same probe at `ρ = 1/2` in the window
   `0.25 < δ < 0.2929` (needs `n ≥ 24`, hence a real list-decoder instead of the brute-force
   `dist_to_code`), and with multiplicity `m ≥ 2`, to confirm the far/near dividing line at
   the parameters that carry the prize row.

---

## 6. Addendum: items 5(i) and 5(1) are now machine-checked

Two further pieces were formalised after the body of this report was written; both build
without `sorry` and depend only on `[propext, Classical.choice, Quot.sound]`.

**(a) The degenerate branch can be located at an irreducible factor of positive `Y`-degree**
(`CarrierDichotomy.card_le_or_exists_degenerate_irreducible`,
`…card_badSet_le_or_exists_degenerate_irreducible`).  Taking the factorisation of the
interpolant into irreducibles and separating the `Y`-free factors — whose challenges are all
roots of one fixed nonzero polynomial of `F[Z][X]`, hence at most `dZ` of them — gives

  `#badSet ≤ dZ + L·(|D|·(dZ + L))`  ∨  `∃ W, Irreducible W ∧ W ∣ Q ∧ 1 ≤ deg_Y W ∧
   |D| ≤ |lineSupport W| + e + 1`.

So the open branch is not "some factor", but "some *irreducible* factor of positive
`Y`-degree", at the cost of a single additive `dZ`.

**(b) A vanishing pair resultant *is* a common irreducible factor over `F[Z][X]`**
(`GaussDescent.lean`).  The dichotomy of `ResultantDichotomy` is stated over a field; the pair
resultant `pairResBiv` lives over the domain `R = F[Z][X]`.  Gauss's lemma descends the
fraction-field statement:

* `GaussDescent.dvd_of_map_dvd_map_of_irreducible` — an irreducible `W ∈ R[Y]` of positive
  `Y`-degree dividing `f` over `Frac(R)` divides `f` over `R`;
* `GaussDescent.exists_irreducible_common_factor_descend` — an irreducible common divisor of
  the image of a family in `Frac(R)[Y]` descends to `R[Y]`, still of positive `Y`-degree;
* `GaussDescent.resultant_dichotomy_pair` — hence, for nonzero `Q, Q' ∈ R[Y]`, either
  `Res_Y(Q,Q') ≠ 0` or `Q` and `Q'` have a **common irreducible factor of positive `Y`-degree
  in `F[Z][X][Y]` itself**;
* `GaussDescent.card_goodZ_le_or_exists_common_irreducible`,
  `…card_badSet_le_or_exists_common_irreducible` — the MCA form: for two interpolants of the
  formal line, with the first genuinely involving `Y`,

    `#badSet ≤ (bY + bY')·dZ`  ∨  `∃ W, Irreducible W ∧ 1 ≤ deg_Y W ∧ W ∣ Q ∧ W ∣ Q'`.

  (`deg_Y Q = 0` is not a gap: a `Y`-free interpolant is a `Y`-free element of the
  interpolation ideal and `WitnessElimination.card_le_natDegree_of_yfree_combination` bounds
  the close set by `dZ` outright.)

`GaussDescent.resultant_dichotomy_descend` / `…_trivariate` give the same conclusion for a
whole line-closed family, with the caveat recorded in their docstrings that the closure
hypothesis forces unbounded degrees, so they apply to a full interpolation module rather than
to a degree-budgeted family.

**Updated obstruction.**  The Gauss-lemma step of §5.1 is done, and the branch is now an
explicit trivariate polynomial rather than a fraction-field phenomenon.  What remains is
exactly §5.2: *for a far-centred line, no irreducible `W ∈ F[Z][X][Y]` of `Y`-degree `≥ 2`
dividing an interpolant can be degenerate along the formal line* (`|lineSupport W| ≥ |D| − e`).
The `Y`-degree-`1` case is already closed
(`WitnessElimination.card_goodZ_le_of_scaled_witness_family`,
`QuadraticFactorBranch.card_le_of_scaled_linear_factor`).
