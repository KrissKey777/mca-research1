# Literature audit: finite-field moment-subset-sum bounds do not close the deployed gate

## Status

`LITERATURE_QUANTITATIVE_NO_GO`

## Exact comparison

The relevant result is Lai--Marino--Robinson--Wan, *Moment subset sums over
finite fields*, arXiv:1910.05894.  Their evaluation-set theorem applies to an
image of a monomial or Dickson polynomial.  The deployed root set is contained
in such an image: with

\[
d=(p-1)/256=8,323,072,
\]

the image of \(x\mapsto x^d\) on \(\mathbb F_p\) is
\(\{0\}\cup\mu_{256}\).  Removing \(0\) and \(1\) changes an exponential sum by
at most two terms.

For a degree-\(m\) phase, their generic estimate has scale
\[
(md+1)\sqrt p.
\]
At the relevant moment degree \(m=6\), this is
\[
(6d+1)\sqrt p
=49,938,433\sqrt{2,130,706,433}
\approx2.3051\cdot10^{12},
\]
whereas the deployed set has only 255 points.  Thus the theorem gives no
nontrivial character-sum bound at this row; even the trivial bound 257 is
stronger.  The smaller formal expression \(6\sqrt p\) that one might obtain
after incorrectly cancelling the image multiplicity is not licensed by the
theorem.

## Consequence

The generic moment-subset-sum literature cannot provide the needed pointwise
bound
\[
N(g)\le B^*=274980728111395087
\]
or the required signed Fourier budget.  It is therefore a genuine quantitative
no-go for the generic Weil/Li--Wan route, not evidence for or against the
Grand MCA claim.

The remaining viable Fourier route must use additional deployed structure:
the exact 256th-root subgroup, the deleted root, antipodal/dyadic orbit
structure, and phase cancellation across characters.  A generic theorem about
moment subset sums must not be cited as a solution without a new estimate
whose numerical constant is evaluated at the deployed parameters.

## Source

Primary source: <https://arxiv.org/abs/1910.05894>.
The paper's character-sum estimate is explicitly of the form
\((mn+1)\sqrt q\), where \(n\) is the degree of the image polynomial.

## Scope

This report is a literature/computation audit, not a Grand MCA proof and not a
counterexample.  It should be treated as a permanent `DO_NOT_REOPEN` item for
the generic finite-field moment-sum route.
