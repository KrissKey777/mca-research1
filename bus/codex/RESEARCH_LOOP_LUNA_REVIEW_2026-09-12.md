# Codex Luna review — Aristotle(parallel) heavy-fibre prompt

## Verdict

`REVISE`, then send. The previous prompt was directionally correct but too
broad and contained an invalid quantitative shortcut.

## Required correction

The reported conditional statement “coprime rational presentation of degree
at most `w` implies at most `146028888064` challenge values” is not valid from
degree alone. A nonconstant rational map of small degree may have many values.
The Aristotle task must therefore prove a single applicability theorem for a
fixed heavy point `x`, including: the exact invariant map and target; official
domain/nondegeneracy; denominator nonvanishing; the exact bounded-root or
bounded-fibre polynomial lemma producing `146028888064`; and the numerical
comparison with `B*`. If any interface fails, Aristotle must return the
smallest exact official countermodel, not continue with an informal bound.

## Dispatch policy

This review is a gate on the prompt, not evidence that the Aristotle report
has been replayed. The corrected prompt is stored at
`staging-lean-setup/research-loop/prompts/aristotle/GMCA-2026-09-12-001.md`
and is to be sent to the existing Aristotle(parallel) project only after this
correction.
