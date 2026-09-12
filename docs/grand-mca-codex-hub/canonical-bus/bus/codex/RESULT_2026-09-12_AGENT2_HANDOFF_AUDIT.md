# Agent2 handoff audit — 2026-09-12

## Evidence status

This is an integrator audit of a pasted Agent2 handoff. It is not a Lean
replay. Claims labelled `PROVED` in the handoff are recorded here as
`REPORTED_DERIVATION`; exact finite scans are `REPORTED_EXACT_COMPUTATION`.

## Accepted routing facts

1. The fixed-weight key-fibre problem is not controlled by average fibre size,
   affine dimension, or the invalid heuristic `2^255 / p^7`.
2. The restricted H8-invariant family is small; the reported H4/H8 maxima are
   finite-computation evidence and must not be promoted to a universal
   classification of all periodic subsets over `F_p`.
3. The raw collision second moment cannot prove an upper bound by comparing
   `S2` with `(B*)^2`; the valid unsafe certificate is `S2/A > B*`.
4. The useful UNSAFE decomposition is the antipodal `256 -> 128` split into
   even occupancy and odd signed moments.

## Important new claim requiring independent audit

Agent2 reports `M8 <= 36` for the number of degree-8 locators in a fixed
MatchedFamily key, using `p_252 = p_-4` and a degree-36 polynomial in the
remaining coefficient. This is potentially valuable, but remains
`REPORTED_DERIVATION` until its characteristic/nonvanishing assumptions and
the passage from roots to the exact deployed key map are checked.

## Current routing

- Aristotle(parallel): continue only the SAFE heavy-point twisted-invariant
  gate from `GMCA-2026-09-12-001`.
- Agent2/UNSAFE: investigate the antipodal occupancy/sign convolution and
  either prove a fibre bound below `B*` or construct a fibre above `B*`.
- Do not reopen H8/H4-only, averaging-only, raw-S2-upper-bound, or generic
  Weil/Li-Wan routes.
