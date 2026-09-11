# GRAND MCA QUANTITATIVE BRIDGE — 2026-09-07

## Exact inputs

p = 2130706433
p+1 = 2130706434
B* = 274980728111395087
e = 981104
a = n-e = 1116048
k = 1048576
t = a-k = 67472
n-2e = 134944

Projective-plane counts:
N = p^2+p+1 = 4539909905758289923
each line/pencil has p+1 = 2130706434 points
each point lies on p+1 lines
the incidence matrix satisfies A A^T = p I + J
and the Levi graph has eigenvalues ±(p+1), ±sqrt(p).

## A. Globalization threshold

Use the existing deployed ambiguity inequality:
  #Bad <= (e+2) + (p+1) + (p+1)*|Amb(U)|.

If X is the number of exceptional/non-globalized ambiguous directions, the exact
largest integer still implying #Bad <= B* is

  X_max = floor((B*-(e+2)-(p+1))/(p+1))
        = 129056129.

This is the operative threshold. If a future theorem instead charges each
exception directly with coefficient one, the alternate budget is
B*-(e+2) = 274980728110413981, but that is not the current deployed dichotomy.

## B. Conflict-energy threshold

Let E_conf = sum_lambda E_lambda over the N projective directions. Pure
pigeonhole gives

  max_lambda E_lambda >= ceil(E_conf/N).

Therefore forcing some direction to have E_lambda >= T requires exactly

  E_conf >= (T-1)N + 1.

No stronger concentration follows from the identity alone. The proof must provide
a lower bound on E_conf or an additional structure theorem.

## C. Pencil-size threshold

Do not identify m with s.

- m = number of code-good covectors in one pencil.
- s = number of distinct forced interpolants at its common direction.

The quotient theorem must be stated with its actual input map. If it consumes a
quotient-visible family of size L, the 3-chart prize threshold is

  L >= L_3 + 1 = 302754427,

because 3 L_3^2 <= B* and 3 (L_3+1)^2 > B*.

Thus the weakest useful concentration conclusion is not m>=s; it is:
there exists a pencil and an explicitly injective quotient-visible witness family
of cardinality at least 302754427, derived from m and s with the exact fibre loss.

If the current theorem proves L <= min(m,s), require
min(m,s) >= 302754427.
If it proves L <= s with m only supplying existence, require s >= 302754427.
If it proves L <= m, require m >= 302754427.

Forcing a raw conflict edge count T=302754427 by pigeonhole alone requires
E_conf >= 1374477817609565160379449199214079708.

## D. Quotient-locus thresholds

For M charts:
  L_max(M) = floor(sqrt(B*/M)).

Exact values:
  M=1: L_max = 524386048
  M=3: L_max = 302754426
  M=6: L_max = 214079707
  M=9: L_max = 174795349

Checks:
  3*(302754426)^2 = 274980727387768428 < B*
  3*(302754427)^2 > B*
  6*(214079707)^2 = 274980725695235094 < B*
  9*(174795349)^2 = 274980726288286209 < B*.

## E. Weakest theorem worth proving

RelativeConflictAgreement should not promise a huge raw conflict graph.
It should promise directly:

If #Bad > B*, then there exists one projective pencil P and a
quotient-visible certificate set Q(P) with |Q(P)| >= 302754427, after all
explicit exceptional classes and chart/fibre losses are accounted for.

This is the minimum theorem that can close the 3-chart Rank2QuotientFunctionalDescent.

