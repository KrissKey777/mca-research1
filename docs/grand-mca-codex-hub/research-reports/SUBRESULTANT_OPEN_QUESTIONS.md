# Subresultant core — questions deliberately left open

The certified chain

  Bad → Close → canonical algebraic locus → degree → cardinality

is now machine-checked in `RequestProject/Root/CodingTheory/SubresultantCore.lean`
(no `sorry`, no new axioms).  The following three questions are **frozen**: they
were not investigated in this round and nothing in the file depends on them.

**Q1 — correlated agreement.**  What can be said about `#Bad` when the canonical
subresultant degenerates, `W_can = 0`?  The present theorems all carry the
hypothesis `W_can ≠ 0`; the degenerate branch is exactly the correlated-agreement
regime and is untouched.

**Q2 — sharp `ν`.**  Gate 1 gives `ν ≤ e` under `k + e ≤ |D|`.  Is there a sharper
bound of the shape `ν ≤ Φ(k + 3e − n)`?  Note that the stronger claim
`k + 3e ≤ n ⟹ ν = 0` is *false* (it fails for `2 ≤ ν ≤ e`), so it was not
formalised.

**Q3 — sharp degree.**  Gate 5 bounds `deg W_can ≤ (k+1)ν + 1` from the column
`Z`-degrees.  Is `Θ(kν)` actually attained, or does systematic cancellation in the
minors reduce the true degree?
