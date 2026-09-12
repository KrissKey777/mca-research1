# Universal grading of individual RS witnesses is false

## Status

`UNIVERSAL_GRADING_FALSE; HIGH_LOAD_GRADING_OPEN`

## Exact statement

Let \(C\) be the deployed Reed--Solomon code with syndrome space
\(F^r\), parity-check columns \(v_x\), and
\[
V_E=\operatorname{span}\{v_x:x\in E\}.
\]
For every subset \(E\subset D\) with \(|E|=e<r\), there exists a received
syndrome line \(L=\operatorname{span}(s_0,s_1)\) and a finite challenge
\(\gamma_0\) such that
\[
s_0+\gamma_0s_1\in V_E,
\qquad L\not\subseteq V_E.
\]

Consequently, official badness alone cannot force the witness window or erasure
set to be a union of fixed cyclotomic blocks.

## Proof

Choose any nonzero \(q\in V_E\) and choose \(s_1\notin V_E\), possible because
\(\dim V_E=e<r\).  Fix any finite \(\gamma_0\in F\) and define
\[
s_0=q-\gamma_0s_1.
\]
Then
\[
s_0+\gamma_0s_1=q\in V_E,
\]
while \(s_1\notin V_E\), so \(L\not\subseteq V_E\).  Moreover \(s_0,s_1\)
are linearly independent: a proportionality would make the nonzero vector
\(q=s_0+\gamma_0s_1\) proportional to \(s_1\), contradicting
\(s_1\notin V_E\).  The syndrome map of the received-word space onto \(F^r\)
is surjective, so these syndromes lift to an official received pair.

Thus every size-\(e\) erasure set is realizable as an official witness for
some rank-two received pencil.  This is a direct finite-dimensional argument;
it does not use probabilistic or generic-position language.

## Consequence for the RS global-load gate

The reported bound based on root/child windows being unions of 32 and 16 fixed
blocks is valid only conditionally for the graded subclass.  It cannot be
promoted to an unconditional theorem about individual official witnesses.
The correct remaining theorem must use a high-load hypothesis, for example:

\[
\text{if }\sum_R\mu_R\Phi(R)>T,
\text{ then the collection of many witnesses admits a common graded
normal form or another list bound }L M\le T.
\]

Any valid grading theorem must therefore be a collective/stability result about
many challenges sharing the same received pair, not a property of one witness.

## Scope

This does not construct a deployed Grand MCA counterexample and does not refute
the conditional graded load bound. It refutes only the unconditional
individual-witness grading implication and identifies the exact repair needed
for Aristotle(parallel).
