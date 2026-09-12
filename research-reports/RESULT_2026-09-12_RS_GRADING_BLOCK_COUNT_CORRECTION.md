# Exact block-count correction for the RS graded gate

## Status

`EXACT_NUMERICAL_CORRECTION`

If the proposed grading theorem fixes exactly 17 root blocks and 9 child
blocks, the count is
\[
\binom{32}{17}\binom{16}{9}=6,471,867,916,800.
\]

However, if the theorem only guarantees a total of at most 54 blocks, the
correct worst-case count is the exact maximum
\[
\max_{0\le a\le32,\ 0\le b\le16,\ a+b\le54}
\binom{32}{a}\binom{16}{b}
=\binom{32}{16}\binom{16}{8}
=7,735,904,619,300.
\]

This remains below the frozen load threshold
\[
T=19,559,298,652,205,332
\]
by the exact factor
\[
\left\lfloor T/7,735,904,619,300\right\rfloor=2528.
\]

Therefore the conditional graded route still has substantial numerical slack,
but any formal proof must state whether the block counts are fixed at (17,9)
or only bounded by a total of 54. The latter requires the maximum above.
This arithmetic does not prove the grading lemma itself.
