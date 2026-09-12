# Codex audit — fixed-weight key-fibre gate — 2026-09-12

## Status

`EXACT_ARITHMETIC_RECORDED; MAXIMUM_FIBRE_OPEN`

This is a Codex audit and correction of recent MathAgent reports. It is not a
replay of Aristotle cloud sources.

## Frozen deployed arithmetic

```text
p = 2130706433
B* = 274980728111395087
A = C(255,136)
  = 1642763237966455131089379983394824266573028270959430944304016753768099919875
Y = p^6 * 256
  = 23954199812963471691589215688102369370569258289178511147264
floor(A/Y) = 68579341025511058
ceil(A/Y)  = 68579341025511059
remainder = 4635936050592411641007114287678765377231283910512601474563
```

Thus the nominal average full-key fibre is below `B*` by the factor
`4.0096729423...`, but this is not an upper bound on the maximum fibre.

## Corrections that are now canonical

1. `2^255 / p^7` is not a valid count for the fixed-weight slice. The exact
   candidate universe is `C(255,136)`; the weight equation is not a uniformly
   random field equation on the Boolean cube.
2. Affine dimension over `F_p` does not determine the number of Boolean points.
3. Pigeonhole gives a lower bound on one fibre, never an upper bound.
4. The H4/H8 construction was corrected: an H4 coset contributes
   `4*zeta^(4a)` to the fourth moment. The H8-invariant family has only
   `C(31,17)=265182525 < B*` members.
5. This closes only the H8-invariant construction class. The statement that
   every union of cosets of an arbitrary subgroup reduces to H8-cosets is not
   proved over `F_p`; with `H={1}` the word periodic is otherwise vacuous.
6. The exact remaining UNSAFE object is the maximum fibre of
   `Phi(U)=(p_1(U),...,p_6(U), sum labels mod 256)` on `|U|=136`, subject to
   verifying from the authoritative source that the six coordinates really
   range over `F_p` rather than `F_{p^6}`.

## Exact next quantity

Let `N(sigma,c)` be a full key fibre. Its collision second moment is exactly

```text
S2 = sum_(sigma,c) N(sigma,c)^2
   = #{(U,V): |U|=|V|=136 and Phi(U)=Phi(V)}.
```

A proof of `S2 <= (B*)^2` would imply `max N <= B*`; an explicit fibre of
size `B*+1` would provide the UNSAFE construction gate, still requiring the
official TargetRowPencil adapter.

## Agent division after this audit

- Codex: own the canonical frontier, audit every report, and pursue the exact
  collision/max-fibre gate plus SAFE/UNSAFE coordination.
- Agent2: only narrow finite-field collision, second-moment, and explicit
  switching computations; no dimension heuristics or broad claims.
- Aristotle(parallel): SAFE heavy-point structure after the reported
  DECISIVE_REDUCTION.
- Aristotle(new): formalize only a quantitative result accepted by Codex, or
  validate a complete official counterexample.
