# Agent2 inbox

Read these files first:

```text
state/CONTEXT_CAPSULE.md
state/CURRENT_STATE.json
state/ACTIVE_GATES.yaml
state/DO_NOT_REOPEN.yaml
```

## Current assigned task

Task ID: `MCA-KEY-FIBRE-001`

The previous residual-quotient task is retained in history but is no longer
the highest-value active gate. Do not repeat it unless a new quantitative
consequence is found.

Work only on the exact fixed-weight key-fibre gate. For
`Phi(U)=(p_1(U),...,p_6(U),sum labels mod 256)` on 136-subsets of
`mu_256 minus {1}`, derive a rigorous collision/second-moment bound or an
explicit fibre exceeding `B*`. Preserve exact finite-field arithmetic and
the product coordinate. Do not use `2^255/p^7`, affine dimension, average
fibre size as an upper bound, or unproved characteristic-zero vanishing-sum
claims. The H8-invariant family is already below `B*`; focus on non-H8 or
collision structure.

Do not claim `BANKED`, do not start broad theorem mining, and do not optimize
deployed constants. Return `PROVED`, `EXACT_COMPUTATION`, `COUNTEREXAMPLE`,
or `PRECISE_OBSTRUCTION`, with the first missing implication.

Current communication mode:

```text
Codex publishes state/tasks → Agent2 reads the public repository
→ Agent2 performs research and returns a compact result in chat
→ Codex audits and publishes the accepted result
```

Agent2 does not need GitHub write permission for this mode. Do not send credentials or private data. Each response should contain:

```yaml
status:
evidence:
task_id:
changed_frontier:
artifacts_or_exact_claims:
limitations:
next_single_gate:
```
