# Exact mu32 projected even-sector replay

## Status

`EXACT_FINITE_SURROGATE_PROJECTED_BOUND`

In \(\mathbb F_{257}\), take \(D=\mu_{32}\setminus\{1\}\), \(|D|=31\), and
enumerate all \(\binom{31}{8}=7,888,725\) subsets.  Record only the projected
data
\[
(p_2(U),p_4(U),p_6(U),\operatorname{label}(U)\bmod16).
\]

Exact output:

```text
subsets = 7888725
nonempty fibres = 7791190
max fibre = 4
average over nonempty fibres = 1.0125186268079716
histogram top: (1,7694262), (2,96322), (3,605), (4,1)
```

All arithmetic is exact modular arithmetic and the enumeration is exhaustive.
Thus the projected even-sector analogue does not develop a large fibre in this
surrogate. This is not a deployed theorem and cannot replace the 128-point
weighted occupancy problem, but it is a useful falsification/regression test
for claims that the projection alone forces heavy fibres.
