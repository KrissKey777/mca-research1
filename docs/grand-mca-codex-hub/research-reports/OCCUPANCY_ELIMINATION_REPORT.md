# Occupancy elimination test on collision pairs

Experimental round. **No Lean, no formalisation, no axioms, no `sorry`** — nothing in the Lean
sources was touched. Script: `analysis/occupancy_elimination_test.py`; saved exact output:
`analysis/occupancy_elimination_test_output.txt` (10 s runtime once the Phase-1 cache in
`analysis/second_order_phase1/` exists; the script regenerates that cache automatically if it is
absent). All arithmetic is exact: Python integers mod `p` and `fractions.Fraction`. **No float
enters any verdict.**

Phase 1 (instance enumeration) and Phase 2 (collision-pair construction) are reused verbatim from
`analysis/second_order_slope_geometry.py`, so the pairs tested here are exactly the pairs of
`SLOPE_GEOMETRY_SECOND_ORDER_REPORT.md`: 38 084 gap instances, and collision pairs
**256** (regime I, `A` free), **291** (regime II, `A` pinned), **291** (regime III, `A` and the
list-distance multiset pinned). 221 distinct instances occur in those pairs.

---

## STEP 1 — the definition of `c(γ,q)`

**1. Is the witness codeword unique for each bad parameter?**
**No.** Over the 1 460 bad parameters occurring in the collision-pair instances, **481** admit more
than one witness codeword (maximum 3 witnesses for a single parameter), and **151 / 221**
instances contain at least one such parameter. Any definition of `c(γ,q)` that goes through
"the" witness therefore needs a convention.

**2. What convention is used?**
Three conventions are computed, so that no verdict depends on the choice.

| tag | columns | `c(γ,q)` | convention-dependence |
| --- | --- | --- | --- |
| `W1` | realised slopes `q` against the base point `γ₀ = min Bad`, computed from the **lex-least** witness of each bad parameter | `1` iff `γ ∈ class(q)` | depends on the lex-least choice **and** on the base point; this is the object of §4 of the second-order report |
| `W2` | slopes `q = (c_γ − c_{γ₀})/(γ − γ₀)` over **all** witness pairs | number of witness pairs `(c_γ, c_{γ₀})` realising `q` | base-point dependent, witness-choice free |
| `W3` | the affine lines `γ ↦ u + γq` (`u, q` codewords) carrying witness points of at least two bad parameters | `1` iff some witness of `γ` lies on that line | **fully canonical** — no convention at all |

**3. Is `c(γ,q)` a count or an indicator?**
`W1` and `W3` are indicators (`max` entry `= 1` on every instance tested); `W2` is a genuine count
(entries up to `2` occur, e.g. in the RS[5,2]/F₅ pair of §4 below).

An unambiguous `c(γ,q)` therefore exists — `W3` — and the test proceeds.

---

## STEP 2 — full occupancy matrix on the collision pairs

Full matrices `C` were computed for all 221 instances in all three conventions and compared **up to
row and column permutation** (exhaustive over column permutations whenever there are ≤ 8 columns;
for wider matrices a refinement-based canonical order is used, which is a strong invariant only —
this is flagged in the output and never affects a verdict, because every pair is already separated
by shape).

The two explicit witness pairs of `SLOPE_GEOMETRY_SECOND_ORDER_REPORT.md` §4, printed in full in
the saved output:

RS[6,2]/F₇, `e = 2`, `w = 3`, `A = 2`:

```
X₁ (#Bad = 3)                  X₂ (#Bad = 4)
W1 (3×2)  colsums (2,2)        W1 (4×2)  colsums (2,3)
   1 1                            1 1
   1 0                            0 1
   0 1                            1 0
                                  0 1
W3 (3×3)  colsums (2,2,2)      W3 (4×4)  colsums (2,2,2,3)
   0 1 1                          1 1 0 0
   1 1 0                          0 1 0 1
   1 0 1                          1 0 1 1
                                  0 1 1 0
```

RS[5,2]/F₅, `e = 2`, `w = 1`, `A = 2`:

```
X₁ (#Bad = 4)                  X₂ (#Bad = 5)
W1 (4×2)  colsums (2,3)        W1 (5×2)  colsums (3,3)
W2 (4×2)  max entry 1          W2 (5×4)  max entry 2, rowsums (2,2,2,2,8)
W3 (4×4)  colsums (2,2,2,3)    W3 (5×6)  colsums (2,2,3,3,3,3)
```

---

## STEP 3 — the decisive test

**Does the complete occupancy matrix separate every collision pair?**

**Yes — 256/256, 291/291, 291/291, in all three conventions and all three regimes.**

**But the separation is forced and carries no information.** In every single one of the
838 pair-comparisons the matrices are already separated by their **shape**:

```
separated by matrix shape alone : 256/256, 291/291, 291/291   (all conventions)
pairs of equal shape             : 0
```

The rows of `C` are indexed by the bad set, so `#rows = #Bad`; a collision pair is by definition a
pair with different `#Bad`. Occupancy therefore "separates" for exactly the reason the
parameter-indexed family `PE` of the previous report separated: it is a statistic **of** the object
to be bounded, not a constraint **on** it.

Two exact identities, verified with **0 violations on all 221 instances** (STEP 3a of the output),
make this precise for `W1`:

```
#columns(C) = A            and            Σ_q |class(q)| = #Bad + A − 1.
```

With `A` pinned (regimes II and III) the occupancy data and `#Bad` determine each other by an
identity. So the "YES" is an arithmetic tautology, not evidence of a mechanism.

### Reduced statistics (pairs separated, regime II / 291, regime I / 256)

| statistic | `W1` II | `W2` II | `W3` II | `W1` I | `W2` I | `W3` I |
| --- | --- | --- | --- | --- | --- | --- |
| number of nonzero entries | 291 | 231 | 286 | 250 | 222 | 253 |
| maximum entry | **0** | 108 | **0** | **0** | 100 | **0** |
| row-sum multiset | 291 | 291 | 291 | 256 | 256 | 256 |
| column-sum (occupancy) multiset | 291 | 227 | 286 | 256 | 223 | 253 |
| row concentration `max rowsum / Σ` | 291 | 223 | 263 | 227 | 196 | 230 |

Reading: for `W1` the nonzero count is `#Bad + A − 1`, i.e. the identity above, so its 291/291 is
the same tautology; the maximum entry is constantly `1` and separates **nothing**; the row-sum and
column-sum multisets separate everything only because their length is `#Bad`, resp. their sum is
`#Bad + A − 1`. The only statistics that are not pure size accounting — the maximum entry, and the
counts under `W2`/`W3` — are the ones that separate *worst*.

### STEP 3b — size-free test: is there anything in occupancy beyond `#Bad`?

The decisive non-tautological question is the converse one: at **fixed** `#Bad` (and fixed
first-order signature and `A`), does occupancy still vary? Grouping the 221 instances by
`(first-order signature, A, #Bad)` gives 125 groups, 96 of them with ≥ 2 instances:

```
W1 : 96 testable groups,  0 with more than one occupancy matrix
W2 : 96 testable groups, 56 with more than one occupancy matrix
W3 : 96 testable groups, 69 with more than one occupancy matrix
```

So under the canonical-witness convention `W1` — the occupancy notion that §4 of the previous
report pointed at — **occupancy is an exact function of the already-pinned data together with
`#Bad`**: it contains no state beyond `#Bad` itself, in either direction. The convention-free
refinements `W2`, `W3` do carry information beyond `#Bad`, but that information is again indexed by
the bad set (rows = bad parameters, columns = witness lines), so it cannot serve as an upper bound
for `#Bad` either.

---

## Answer to the stop-rule question

> **Is occupancy the actual missing state variable?**

**No.**

* It separates every collision pair (256/256, 291/291, 291/291, all conventions), but does so
  purely by size: `#rows = #Bad`, and for the canonical convention `Σ_q |class(q)| = #Bad + A − 1`
  exactly, with 0 violations.
* In the reverse direction it is empty: on all 96 testable groups the `W1` occupancy matrix is
  constant once `(first-order signature, A, #Bad)` is fixed. Occupancy is thus a re-encoding of
  `#Bad`, i.e. book-keeping, and not an independent quantity that could explain or bound it.
* The only occupancy statistics that are not pure size accounting — the maximum entry (blind:
  0/291 and 0/256) and the count-valued conventions (worst separators in the table) — do not
  support any inequality either.

**The occupancy direction is closed.** Any bound sharper than the proved
`A − 1 ≤ #Bad ≤ (e+1)·A + 1` must come from data that is *not* indexed by the bad set: the
per-class packing bound `|class(q)| ≤ cap(e, d(f₁,q))` (`Alphabet.card_le_chargeCap`, already
proved) is the last statement of this kind that constrains occupancy from outside, and everything
in this experiment sits inside it.

Per the mission's stop rule, no step was taken towards `A_E`, intrinsic geometry, spectral width,
Johnson/list-decoding bounds, or topology.

## What is *not* claimed

* No theorem, and nothing formalised. These are exact finite computations over the families
  RS[4,2]/F₅, RS[4,3]/F₅, RS[5,2]/F₅, RS[5,3]/F₅, RS[6,2]/F₇, RS[6,3]/F₇, RS[6,4]/F₇, RS[7,3]/F₇,
  RS[5,2]/F₁₁, RS[6,3]/F₁₁, RS[6,2]/F₁₃ with `e ∈ {1,2}`, on the collision pairs of the previous
  report only.
* No claim for larger `n`, larger fields, `e ≥ 3`, or the M31 parameters.
* The negative conclusion is about *these* occupancy notions (`W1`, `W2`, `W3`); it does not
  exclude some other, differently indexed statistic of the witness configuration.
