# Aristotle(parallel) result — heavy-fibre invariant gate

## Status

`CONDITIONAL`; no Grand MCA safety proof and no official counterexample.

## What is proved

For a fixed domain point `x`, the heavy fibre consists of official bad
challenges whose exact-size locator factors as `Q_gamma = (X-x) R_gamma`.
The invariant `I_x(gamma) = R_gamma(0)` is nonzero and satisfies
`I_x(gamma)^n = 1`, so it takes values in `mu_n`.

The reported bounded-root mechanism is exact once a coprime rational
presentation `I_x = u/v` of degree at most `w` is available: the polynomial
`u^n - v^n` has deployed degree at most

```text
n*w = 2097152 * 69632 = 146028888064 < B*.
```

All these statements were formalized additively and axiom-audited in the
Aristotle project.

## Decisive obstruction

The degree-`<= w` rational presentation does not follow from `I_x` being
`mu_n`-valued. Aristotle supplied an exact small countermodel to that
inference. Moreover, in the regime where the heavy fibre is larger than
`146028888064`, any such presentation would be constant, so the nonconstant
root-count branch self-defeats.

Even a uniform per-point heavy-fibre bound of `146028888064` is insufficient:
the global union estimate is
`2097152 * 146028888064 > B*`.

## Single surviving gate

At the frozen deployed row, decide whether a heavy fibre larger than
`146028888064` can contain two official challenges with distinct `I_x` values.
Either prove `I_x` is constant on every such heavy fibre, or construct an
official split-locator/twisted-syndrome countermodel with distinct values.

Source report: `HEAVY_FIBRE_INVARIANT_GATE_REPORT.md` in the Aristotle output
for task `9004be44-a678-4d36-9a20-cba58ab6ba9f`.
