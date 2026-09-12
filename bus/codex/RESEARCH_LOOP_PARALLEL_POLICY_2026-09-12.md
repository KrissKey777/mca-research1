# Research loop policy: Aristotle plus parallel work

Aristotle tasks are asynchronous and may take hours. `IN_PROGRESS` is not a
reason to stop the research loop.

While Aristotle runs, Codex/Luna independently audit the current mathematical
gate and prepare the shortest rigorous next proof or counterexample; Sol may
perform adversarial review when available; Leanstral performs only small local
Lean checks; and exact local computations are recorded with their tested range
and never promoted to universal theorems without proof.

The dispatch step is serialized: candidate packets may be written to the bus,
but no new Aristotle task is sent until a new Aristotle output arrives. Then
Codex classifies the output, replays or audits decisive claims, obtains Luna's
adversarial review, merges only non-duplicative progress, and dispatches the
next packet under the standing authorization.

Priority is: unconditional bound below `B*`, official counterexample above
`B*`, then a sharp reduction with one exact remaining lemma. Average fibre
size is not a maximum; rational-map degree alone is not a counting bound; and
finite computation remains evidence only.

## Durable-result threshold

Write to the shared Space/GitHub bus only when a result is substantial: a
proved theorem, an official counterexample, a rigorously refuted route, a
new exact quantitative gate, a material semantic correction, or a verified
change in the Grand MCA frontier. Routine iterations, unchanged status,
failed attempts without a reusable obstruction, and duplicate summaries stay
in the local run log and are not committed.
