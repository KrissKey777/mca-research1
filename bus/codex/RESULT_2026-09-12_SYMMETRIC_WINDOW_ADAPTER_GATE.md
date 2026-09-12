# New SAFE gate from review — symmetric-window mechanism

## Evidence status

`REPORTED_NOT_REPLAYED`. The Aristotle output archive reports a Lean-proved
factorization `badSet_subset_image_newtonChallenge` in
`SYMMETRIC_WINDOW_MECHANISM_REPORT.md`, with standard-axiom audit.

## Exact scope

The theorem applies to received words represented as `polyWord D P0/P1` with
`natDegree <= k+c` and requires `k+1+e <= |D|`. It factors bad challenges
through the first `c` elementary symmetric functions of a support window.

At the deployed row with `c=w=69632`, the degree threshold is
`k+c=1118208`, whereas arbitrary official received words may have degree up
to `n-1`. A fixed-x locator `Q_gamma` has degree `e=978944`, but no replayed
adapter currently identifies the official challenge family with the bounded-
degree polynomial-word hypothesis.

## Single SAFE gate

Prove the exact adapter from official `badSet`/split-locator data to the
bounded-degree `polyWord` hypothesis, or produce a formal obstruction showing
that `Q_gamma` cannot substitute for the received-word polynomial. Do not
claim the symmetric-window theorem applies to arbitrary official pairs until
this adapter is proved.
