# GRAND MCA — final RS grading gate

Continue from the audited `RSGradedGlobalLoadGate` chain. Do not re-prove the
downstream implication
\[
\sum_R\mu_R\Phi(R)\le19559298652205332
\Longrightarrow \#Bad\le B^*.
\]

The binomial calculation
\[
\binom{32}{17}\binom{16}{9}=6471867916800
\]
is only a conditional result for the graded/coset class. Do not claim that all
official extremal families are graded unless this is proved from the official
definitions.

Attack exactly one of these statements:

1. prove an unconditional grading lemma: every official root witness and every
   captured child witness can be normalized to unions of the deployed smooth
   blocks, with at most 54 blocks in total;
2. prove any unconditional two-level list bounds L and M satisfying
   L*M <= 19559298652205332;
3. produce an exact official counterexample to the proposed grading lemma.

Use the smooth-domain normal form and the divisors of X^k-1 and X^k+1 only
when their connection to the official witnesses is proved. Preserve exact
support, finite challenge, nondegeneracy and captured multiplicity. Do not use
arbitrary kernels, arbitrary subspaces, raw support counts, coordinate counts,
or circular assumptions about the extremal family.

The already proved fact that distinct challenges cannot share one witness
window is not enough; do not attempt another injective charging argument.

Return exactly one status:
`RS_GRADING_LEMMA_PROVED`, `ALTERNATIVE_RS_LIST_BOUND`,
`RS_GRADING_COUNTEREXAMPLE`, or `RS_GATE_OBSTRUCTION`.

Separate PROVED, COMPUTATIONALLY_CHECKED, CONDITIONAL and HEURISTIC claims.
If formalising, add only a sorry-free, axiom-audited additive module outside
the submission roots. No Grand MCA SAFE claim is allowed unless (1) or (2) is
fully proved.
