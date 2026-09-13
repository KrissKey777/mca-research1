# Aristotle(parallel) — next gate: correlated-core count

Work only on the reported deployed `DECISIVE_SINGLE_BRIDGE` branch. Do not
return to the generic root bound `#Bad <= 2^34`, generic Johnson/list-size
theorems, or global SAFE load experiments.

The frozen endpoints are:

```text
n=2097152, k=1048576, e=978944, t=1118208, w=69632
LOAD*=19559298652205332, B*=274980728111395087
c=596231, large-core-size=596232
```

The reported ledger is

```text
(1118208 + 1500920*N) *
(1048576 + 1043952*N') <= LOAD*.
```

The root-only endpoint is `N <= 12427` when `N'=0`; the child-only endpoint
is `N' <= 16754` when `N=0`. These are exact numerical thresholds, not yet a
replayed theorem.

## Phase 1 — freeze the exact object

Recover from source the exact definition of a correlated core and prove when
two bad-pairs define the same core. Distinguish:

- support set;
- codeword pair;
- pencil or residual object;
- canonical core representative.

Prove the map from official pair/challenge data to canonical cores and the
deduplication theorem used by `N` and `N'`. Do not count labelled witnesses if
the ledger counts canonical cores.

## Phase 2 — intersection spectrum

For distinct large cores `R_i,R_j`, derive the strongest source-level bound on
`|R_i ∩ R_j|`. First compute exact spectra on the already available small
extremal families, exporting:

```text
core_size,
pairwise_intersection,
pairwise_symmetric_difference,
bad_pairs_per_core,
residual_or_shadow_label.
```

Small computations are discovery evidence only. Search for a theorem of the
form

```text
|R_i ∩ R_j| >= T -> same core / same pencil / rigid branch.
```

Find the smallest provable `T`. Do not infer a packing bound from a histogram
without a source-level separation theorem.

## Phase 3 — algebraic rigidity

For two core-generating codeword pairs, identify the lowest-degree polynomial,
determinant, wedge, or residual object that vanishes on `R_i ∩ R_j`.

Do not automatically use degree `k`. If the pair-correlated structure yields
an object of degree `D`, compare `D` with the proved intersection threshold
`T`: vanishing on more than `D` distinct evaluation points is the point at
which a polynomial identity or rigidity conclusion may fire.

The target is not a heuristic “large overlap”; it is a formal implication to
same core, same pencil, or a quantitatively restricted intersection.

## Phase 4 — packing or joint ledger closure

Once an exact intersection ceiling `lambda` is proved, instantiate an
applicable finite theorem with all hypotheses and deployed parameters. Test
only methods that can actually imply `N <= 12427` or the joint ledger:

- Ray–Chaudhuri–Wilson / Frankl–Wilson;
- Johnson-scheme LP or constant-weight code bounds;
- Fisher/Deza-type inequalities;
- EKR/stability only if its hypotheses match the core family.

Do not cite a theorem without translating its set size, intersection,
uniformity, and ambient-domain hypotheses.

If root-only counting is too strong, derive directly a root/child tradeoff that
implies

```text
(1118208 + 1500920*N) *
(1048576 + 1043952*N') <= LOAD*.
```

## Phase 5 — constructive branch

At every stage search for an explicit family with `N > 12427`, `N' > 16754`,
or a violation of the joint hyperbola. Such a family is an UNSAFE candidate
only after the official correlated-core-to-challenge adapter is replayed and
the resulting `#Bad` or deployed cost is checked.

## Accepted outcomes

Return only:

1. `CORRELATED_CORE_COUNT_LE_12427`, with a complete replayable proof;
2. `JOINT_ROOT_CHILD_HYPERBOLA`, with the exact downstream ledger closure;
3. `CORRELATED_CORE_COUNTEREXAMPLE`, with an official adapter;
4. `DECISIVE_SINGLE_BRIDGE`, only if exactly one quantitative theorem remains
   and every downstream step is already machine-checked.

Failure of one packing theorem, one degree estimate, or one numerical probe is
not a no-go result. Do not return `GRAND_MCA_SAFE` or `GRAND_MCA_UNSAFE` unless
the frozen downstream chain actually reaches that endpoint.

Lean policy: no `sorry`, no new axioms, no `native_decide`, and no changes to
existing declarations, manifests, lakefiles, toolchain, or submission roots.
All reported Aristotle modules must be replayed in the canonical source bundle
before their status changes from `REPORTED_NOT_REPLAYED`.
