# GRAND MCA — collective high-load stability gate, corrected arithmetic

Universal grading of one official witness is false. Work only with many
witnesses for one common received pair and captured multiplicities.

The downstream load implication is already audited. The target is
\[
\sum_R\mu_R\Phi(R)\le T,
\qquad T=19559298652205332.
\]

If a collective grading theorem gives root/child unions of blocks with exactly
(17,9) blocks, the combinatorial count is
\(\binom{32}{17}\binom{16}{9}=6471867916800\). If it gives only a total of at
most 54 blocks, use the exact worst case
\[
\max_{a+b\le54}\binom{32}{a}\binom{16}{b}
=\binom{32}{16}\binom{16}{8}=7735904619300<T,
\]
with floor slack factor 2528. Do not silently substitute the (17,9) count for
the weaker total-block statement.

Prove one collective theorem:

1. load exceeding T forces the common received pair into the stated graded
   normal form with a valid block-count profile;
2. or derive alternative RS list bounds L and M with L*M <= T;
3. or construct an exact official high-load counterexample violating both.

The proof must derive grading from common rank-two syndrome data, captured
multiplicity, split locators, and root divisors; it may not assume grading,
count arbitrary kernels, or count raw supports. Preserve official
nondegeneracy, finite challenges, and the residual transition.

Return HIGH_LOAD_GRADING_PROVED, ALTERNATIVE_LOAD_BOUND,
HIGH_LOAD_GRADING_COUNTEREXAMPLE, or RS_GLOBAL_LOAD_OBSTRUCTION. Separate
proved, computational, conditional and heuristic claims.
