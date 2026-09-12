# Grand MCA research-loop evidence protocol

This is the durable evidence contract for `grand-mca-codex-research-controller`.

## When to persist

Persist only a material result: a proved/replayed theorem, an exact finite
counterexample, a computation that changes route priority, a killed route, or
a compact Aristotle packet ready for review. Do not publish routine attempts.

## Where to persist

- Codex reports: `bus/codex/RESULT_YYYY-MM-DD_<slug>.md`
- Reproducible calculations: `certificates/<slug>/` with source, parameters,
  raw output or a compact witness, and a README
- Aristotle packets: `prompts/aristotle/<slug>.md`
- Canonical state changes: only Codex updates `state/CURRENT_STATE.*`

## Required report fields

Every report must contain:

```text
STATUS:
RESULT_KIND: PROVED | REPLAYED | COMPUTATIONAL | REFUTED | CONDITIONAL | OPEN | BLOCKED
CLAIM:
HYPOTHESES_AND_CONVENTIONS:
EVIDENCE_PATHS_OR_LINKS:
REPRODUCIBLE_COMMAND:
PARAMETERS_AND_TESTED_RANGE:
WITNESS_OR_OUTPUT_HASH:
LEAN_STATUS:
AXIOM_STATUS:
SEMANTIC_RISKS:
NEXT_SINGLE_GATE:
```

For a paper result, include the exact citation/link, theorem statement,
hypotheses, and the implication used. For a computation, include exact
arithmetic or finite enumeration details; sampling is never exhaustive without
a proved symmetry reduction. For Lean, include the source path, successful
build command, theorem names, and `#print axioms` output.

## Publication rules

`BANKED` requires independent replay, exact signature/dependency checks, a
successful relevant build, and an axiom audit. Aristotle output remains
`RNR` until replayed. If GitHub is unavailable, write a local report with
`STATUS: BLOCKED` and `BLOCKER: BLOCKED_GITHUB_SYNC`; never claim a push that
did not occur. Never store credentials or modify submission roots, the
toolchain, lakefile, or manifest without explicit authorization.
