# GRAND MCA — collective high-load stability gate

The unconditional grading of an individual official witness is false: for
every E subset D of size e, choose nonzero q in V_E and s1 outside V_E, set
s0=q-gamma0*s1. Then s0+gamma0*s1 lies in V_E and the rank-two line is not
contained in V_E. Therefore do not try to prove that every official witness is
a union of fixed cyclotomic blocks.

Continue from the audited global-load implication and the conditional bound
for the graded subclass. The only viable grading target is collective:

If the captured load exceeds
T=19559298652205332, prove that the many witnesses for one common received
pair admit a common smooth/coset normal form, or prove alternative list bounds
L and M with L*M <= T.

The stability hypothesis must quantify over the actual captured multiplicities
mu_R and child bad sets Phi(R). It may use repeated challenges, common
syndrome data, root divisors of X^k-1 and X^k+1, or rank-two compatibility,
but it must not assume the grading it is trying to prove.

Return one of:
HIGH_LOAD_GRADING_PROVED,
ALTERNATIVE_LOAD_BOUND,
HIGH_LOAD_GRADING_COUNTEREXAMPLE, or
RS_GLOBAL_LOAD_OBSTRUCTION.

The single-witness construction above is not a deployed counterexample; it is
only a guard against an invalid universal premise. Preserve exact official
support, finite challenge, nondegeneracy and captured multiplicity. Separate
PROVED, COMPUTATIONALLY_CHECKED, CONDITIONAL and HEURISTIC claims. Do not
reopen raw charging, arbitrary-kernel counting, or the already proved
downstream implication.
