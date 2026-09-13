# Grand MCA — DECISIVE_SINGLE_BRIDGE: correlated-core ledger

Status: `REPORTED_NOT_REPLAYED`.

This packet records the Aristotle(parallel) report and an independent exact
arithmetic recheck. The claimed Lean modules and axiom audits were not present
in the canonical checkout at recording time, so this packet is not a proof
record and does not claim `GRAND_MCA_SAFE` or `GRAND_MCA_UNSAFE`.

## Frozen deployed constants

```text
n       = 2097152
k       = 1048576
e       = 978944
t       = 1118208
w       = 69632
LOAD*   = 19559298652205332
B*      = 274980728111395087
c       = 596231
```

The reported root escape threshold satisfies

```text
t^2 = n * 596232
t^2 - n*c = n.
```

## Reported machine-checked join

The report claims an unconditional root dichotomy: either the deployed line
has at most `t = 1118208` bad challenges, or a codeword pair explaining two
distinct bad challenges agrees with the received pair on at least `596232`
positions. It also claims the recursive child dichotomy with residual
threshold `4624` and a correlated-cover ledger.

Let `N` be the number of distinct canonical root correlated cores of size at
least `596232`, and `N'` the corresponding child count. The reported frozen
ledger is

```text
(1118208 + 1500920*N) *
(1048576 + 1043952*N') <= LOAD*.
```

Absence of the relevant cores is reported to imply the frozen downstream
`#Bad <= B*` chain. The exact source definition of “same core” remains a
mandatory replay obligation: support, codeword pair, pencil, and canonical
representative must not be conflated.

## Arithmetic recheck

The following endpoint values were independently recomputed with integer
arithmetic:

```text
N  = 12427, N' = 0:
    product = 19559141655707648
    slack   = 156996497684

N  = 12428, N' = 0:
    product = 19560715484397568 > LOAD*

N  = 0, N' = 16754:
    product = 19559046204751872
    slack   = 252447453460

N  = 0, N' = 16755:
    product = 19560213560229888 > LOAD*
```

Thus the reported numbers are numerically non-cosmetic. They do not by
themselves establish the core-count theorem.

## Current single missing bridge

The highest-value remaining theorem is a source-level bound on distinct large
correlated cores, preferably one of:

```text
N <= 12427,
```

or the joint root/child hyperbola above. A strictly stronger intersection or
rigidity theorem is useful only when its exact downstream implication to the
ledger is written and checked.

The reported small-family probe is discovery evidence only. Its range from one
core to approximately `0.67 * binom(#Bad,2)` shows that naive pair counting
does not solve the bridge.

## Required replay checks

Before promoting this packet:

1. replay the two Lean modules and both axiom audits;
2. define canonical core equality and prove deduplication;
3. replay the root/child cover inequalities and exact endpoint arithmetic;
4. verify the frozen downstream chain without rebuilding it;
5. retain the reported pruning of Hankel/key-equation rank-drop and direct
   Johnson counting on pairs as route-specific no-go evidence only.

No Grand MCA endpoint is decided by this packet alone.
