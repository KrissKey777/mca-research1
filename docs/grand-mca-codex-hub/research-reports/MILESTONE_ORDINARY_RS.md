# Milestone — ordinary Reed–Solomon: the state of the line/MCA frontier

This note consolidates the **ordinary** Reed–Solomon strand (the folded strand is closed
separately in `MILESTONE_FOLDED_RS_CAPACITY.md` and is not touched here).  It is a freeze
record: it states what is proved unconditionally, what is proved conditionally and on exactly
which hypothesis, which routes have been formally refuted, and which remain open.

All Lean statements cited below are machine-checked in Lean 4 / Mathlib, contain no `sorry`
and no `admit`, introduce no `axiom`, and are audited in `RequestProject/Main.lean` with
`#print axioms`: each depends only on `propext`, `Classical.choice` and `Quot.sound`.
`lake build` is clean (8182 jobs).

Setting throughout: an evaluation domain `D ⊆ F`, dimension `k`, error budget `e`, and the
line `z ↦ f₀ + z·f₁`.  `badSet k e f₀ f₁` is the set of parameters `z` at which the specialised
word is `e`-close to the code although the line has no correlated agreement; `epsMCA` is its
density.

## 1. Unconditional: the Welch–Berlekamp pencil, unique-decoding regime

**File:** `RequestProject/Root/CodingTheory/WelchBerlekampPencil.lean`
**Narrative:** `RESULTS.md` §63.5 and §64.

The pencil is the `|D| × (k+2e+1)` matrix over `F[Z]` whose row at `x ∈ D` expresses
`Λ(x)·(f₀ x + Z·f₁ x) = Q(x)`, `deg Λ ≤ e`, `deg Q < k + e`.

| # | Statement | Lean name |
| --- | --- | --- |
| W1 | every maximal minor has `Z`-degree `≤ e + 1` | `Root.CodingTheory.natDegree_wbDet_le` |
| W2 | one non-vanishing maximal minor ⇒ `#bad ≤ e + 1` | `Root.CodingTheory.card_badSet_le_of_wbDet_ne_zero` |
| W3 | the same in density form: `ε_mca ≤ (e+1)/\|F\|` | `Root.CodingTheory.epsMCA_le_of_wbDet_ne_zero` |
| W4 | correlated agreement ⇒ every maximal minor vanishes | `Root.CodingTheory.wbDet_eq_zero_of_correlatedAgreement` |
| W5 | a rational line `f_i = P_i/Λ`, `deg Λ ≤ e`, also degenerates every minor | `Root.CodingTheory.wbDet_eq_zero_of_rationalLine` |
| W6 | and if `Λ ∤ P₀` (with `k + 2e ≤ \|D\|`) then `f₀` is not even `e`-close: W4 has no converse | `Root.CodingTheory.not_isCloseOn_of_not_dvd` |
| W7 | if `\|D\| < k + 2e + 1` the system has a nonzero solution for *every* word: the test is vacuous above unique decoding | `Root.CodingTheory.exists_nonzero_wbVector_of_card_lt` |

**What this buys.**  The best previous unconditional bound with constant `e + 1` was
`Root.CodingTheory.card_badSet_le_succ` (`SyndromeRigidity.lean`), which needs
`k + 3e ≤ |D|`.  W2/W3 give the same constant on the whole unique-decoding regime
`k + 2e < |D|`.  The price is one explicit hypothesis, `wbDet … ≠ 0`: a rank condition on a
concrete square matrix, decidable on any given instance, not a conjecture.

**What it does not buy.**  W7 is a proof that the route stops at `k + 2e < |D|`.  W5/W6 are a
proof that pencil degeneracy is *strictly weaker* than correlated agreement, so the degenerate
branch cannot be closed by declaring correlated agreement.

## 2. Unconditional fallback beyond Johnson: the binomial bound

`Root.CodingTheory.card_badSet_le_shorten_circuit` (`ShorteningMCA.lean`, `RESULTS.md` §55–56):

```
#bad · C(|D| − e, t)  ≤  C(|D|, t) · B ,
```

with no hypothesis beyond the numeric ones — in particular no restriction of `e` to the
Johnson radius.  It is obtained by combining agreement-set shortening with circuit incidence
for the shortened generalised instances (`subJohnsonBound_of_circuit`).  Its weakness is its
shape: the transfer factor `C(|D|,t)/C(|D|−e,t)` is **binomial**, not polynomial, so it does
not by itself produce the polynomial post-Johnson thresholds the prize table asks for.

Also unconditional, at a radius between the half-Johnson and the Johnson radius:
`Root.CodingTheory.epsMCAmax_le_pairCover_gs` (`MCAPairCover.lean`), radius
`δ < 1 − (ρ(1+1/m))^{1/4}`.

## 3. Conditional: the length-based post-Johnson bound

`Root.CodingTheory.card_badSet_le_affineSplit` and `epsMCA_le_affineSplit`
(`AffineFactorSplit.lean`, `RESULTS.md` §61):

```
#bad ≤ (#Pairs)·|D| + (2·b_Y(R) − 1)·d_Z(R) ,
```

which is **linear in the code length** with schedule-only constants — the shape BCHKS25
predicts.  It applies to a canonical interpolant `Q` split as (product of affine linear factors
`Y − (A + Z·B)`) × (affine-factor-free residual `R`).  Repeated *affine* factors are handled
unconditionally: they enter `Pairs` with multiplicity.

The polynomial post-Johnson chain in the abstract `SubJohnsonBound` form is
`card_badSet_le_subJohnson` / `epsMCA_le_subJohnson`.

## 4. The exact remaining hypothesis

One statement, and only one:

> the affine-factor-free residual `R` of the canonical split is squarefree in `Y`,

in Lean the hypothesis `discLine bYR x₀ R ≠ 0` of `card_badSet_le_affineSplit`.  By
`Root.CodingTheory.discLine_eq_zero_of_sq_factor` and
`Root.CodingTheory.no_sq_factor_of_discLine_ne_zero` this is *equivalent* to "`R` has no
repeated factor surviving the specialisation at `x₀`", i.e. the interpolant has no repeated
**non-affine** factor.

Removing it appears to need a Hilbert-irreducibility / Bertini–Noether-type transfer for
function fields (specialisations of an absolutely irreducible bivariate polynomial stay
irreducible outside a small set).  That is not in Mathlib and was not derived here.  It is
assumed **nowhere else** in the project.

## 5. Routes formally refuted

| Route | Status | Lean witness |
| --- | --- | --- |
| "degenerate pencil ⇒ correlated agreement" (the WB dichotomy step) | **false** | `wbDet_eq_zero_of_rationalLine` + `not_isCloseOn_of_not_dvd` |
| "no affine factor ⇒ squarefree in `Y`" | **false** | `exists_affineFactorFree_not_squarefree` (`SquarefreeKernelResidual.lean`) |
| "replace `R` by its squarefree kernel and bound the double-root locus by `(2b_Y(R_sf) − 2)·d_Z`" | **false**, by a margin of `\|F\|` | `sqfreeKernel_bound_fails`, `doubleRootLocus_card_unbounded` |
| the Fitting-ideal route to the Johnson gap | **blocked** | `RESULTS.md` §55 |
| the resultant dichotomy's degenerate branch ⇒ formal witness | **false** | `degenerate_branch_without_correlatedAgreement` (`ResultantDichotomy.lean`) |
| Chojecki-style *constant* shortening depth at a constant post-Johnson radius | **false** | `not_constant_shortening_for_positive_slack` (`ChojeckiRadius.lean`) |
| dimension-based (rather than length-based) sub-Johnson bad-set shape | **false** | `RESULTS.md` §60 |

## 6. Routes still open

* **Subresultant probe.**  Replace `Disc_Y(R)` by the first non-vanishing principal
  subresultant of `(R, ∂_Y R)`.  `analysis/subresultant_bad_locus_check.py`: 9 usable instances
  out of 56, all passing containment and the degree bound.  Too thin to be evidence; no Lean
  target attempted (D63.5, D64.3).
* **Factorwise localisation.**  `card_badSet_le_affineSplit_twoFactor` splits the hypothesis
  into `Disc_Y(R₁) ≠ 0`, `Disc_Y(R₂) ≠ 0`, `Res_Y(R₁,R₂) ≠ 0`.  The third is exactly what a
  repeated factor destroys.  Localised, not discharged.
* **A linear deterministic bound for generalised RS lines at the full Johnson radius**, which
  is what would upgrade §2's binomial fallback to a polynomial post-Johnson threshold.  The
  project has it only under the pair-resultant non-degeneracy hypothesis of §54.
* **Chojecki shortening as a separate programme** — at *linear* depth
  (`exists_linear_shortening_for_positive_slack`) the arithmetic works, but the transfer factor
  is `2^{Θ(n)}` (`two_pow_le_choose_div_choose`); a different mechanism is needed to pay it.
* **Connecting the WB pencil with the folded-RS root** — the folded strand reaches capacity
  unconditionally, the WB pencil is sharp and unconditional but only up to unique decoding; a
  formal bridge between them has not been attempted.

## 7. Relation to the Proximity Prize targets

* The prize-style certificates at `K = 2¹⁸` in
  `RequestProject/Root/CodingTheory/PrizeCertificates.lean` (`prize_certificate_rate_*`) are
  true implications but were shown in §60 to rest on the **mis-shaped** dimension-based
  numerator; as stated they are vacuous, and are retained with header notes.
* The corrected, length-based table is `prize_len_certificate_rate_*` together with
  `prize_budget_exceeded_rate_*` (`PrizeCertificatesLen.lean`): certification succeeds only
  over fields of size `2²⁶¹`–`2²⁷³`, i.e. either the prime must be larger than the table's or
  the sub-Johnson constant must be strictly smaller (`DISCREPANCIES.md` §8.13, D62.4).
* Every prize-relevant polynomial post-Johnson statement therefore still rests on the residual
  hypothesis of §4.  Nothing in this milestone changes that; the WB pencil improves the
  *unique-decoding* regime, which is below the radius the prize targets.
* Unconditional and prize-independent: the folded-RS capacity result
  (`MILESTONE_FOLDED_RS_CAPACITY.md`), the binomial fallback of §2, the pair-cover bound, and
  the WB pencil results of §1.

## 8. Freeze list

Not to be modified by later work without an explicit decision recorded in
`DISCREPANCIES.md`: the seven WB statements of §1, all folded-RS results, the definition of
strong MCA, and the axiom discipline (no new `axiom`, no `sorry`).

## 9. Next phase — to be decided explicitly

Two candidates, neither started:

1. **Chojecki shortening as a separate programme** (pay the exponential transfer factor by a
   different mechanism, or replace shortening altogether);
2. **formally connecting the WB pencil with the existing folded-RS root** (does the pencil's
   rank certificate have a folded analogue that survives past unique decoding?).

Per the consolidation instruction, neither is begun in this phase.
