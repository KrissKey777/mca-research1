# Exact replay: full six-moment key map is injective in the mu32 surrogate

## Status

`EXACT_FINITE_SURROGATE_INJECTIVITY`

## Tested model

Work in \(\mathbb F_{257}\) with a primitive 32nd root \(\zeta\), domain
\(D=\mu_{32}\setminus\{1\}\) of size 31, and weight 8. Enumerate every
\(\binom{31}{8}=7,888,725\) subset and record
\[
\left(\sum_{x\in U}x^j\right)_{j=1}^6,
\qquad \sum_{x=\zeta^a\in U}a\pmod{32}.
\]

## Exact output

The exhaustive run `loop/exact_mu32_key_fibre.py` returned:

```text
subsets = 7888725
nonempty_fibres = 7888725
max_fibre = 1
average_over_nonempty = 1.0
histogram_top = [(1, 7888725)]
```

All arithmetic is exact modulo 257; there is no sampling or floating point
step. Thus the complete key map is injective in this surrogate. The separate
degree-eight locator-signature scan in `RESULT_2026-09-12_MU32_D8_TRADE_EXHAUSTIVE.md`
also finds no \(P_A-P_B=cX\) trade.

## Interpretation

This is not a theorem for the deployed \(\mu_{256}\) row and does not imply a
Grand MCA bound. It does establish a clean falsification of the hypothesis
that a large fibre is automatic from six moments plus the cyclic label. Any
deployed unsafe construction must use a genuinely larger/nonperiodic collision
mechanism, not merely the direct scaled \(\mu_{32}\) analogue.

The result is suitable as a small-model regression test for Aristotle(new): a
proposed universal construction or claimed periodic collision mechanism must
first explain why it does not contradict this exact surrogate.
