# Strategic research loop

The loop is priority-driven, not queue-driven. It must repeatedly reconsider
which problem has the highest expected value for the Grand MCA proof.

## Cycle

```text
DISCOVER → RANK → AGREE → ASSIGN → SOLVE → VERIFY → REVIEW → RERANK
```

1. **Discover** candidate bottlenecks from the current state, Aristotle output,
   failed routes, and newly proved lemmas.
2. **Rank** each candidate by dependency centrality, probability of a decisive
   result, value if solved, falsification value, cost, and semantic risk.
3. **Agree**: two independent Luna agents propose rankings; an integrator
   reconciles them. No problem becomes active on one agent's preference alone.
4. **Assign** only disjoint problems from the agreed top slice. Keep one owner
   and one write scope per problem.
5. **Solve** with cheap exact computation and structural reasoning first;
   escalate difficult questions to Sol only when the expected information gain
   justifies it.
6. **Verify** every result as PROVED, COMPUTATIONAL, OPEN, REFUTED, or BLOCKED.
7. **Review** the entire backlog after each completed problem. A new theorem,
   counterexample, or Aristotle result can change the priority order.

## Ranking rule

Use a qualitative score with explicit reasons:

```text
priority = centrality + decisive_value + falsification_value
           - cost - semantic_risk
```

Do not use the score as mathematical evidence. It only selects work. A task
that can kill a major route or expose a semantic mismatch outranks a task that
only improves a constant.

## Governance

- one strategic review after every completed result;
- at most one active problem per worker;
- no duplicate work unless it is an explicitly independent audit;
- no reopening a killed route without a named new hypothesis;
- Aristotle receives only the current compressed gate, not the whole backlog;
- the integrator is the only writer of the canonical priority list;
- old results remain append-only evidence.

## Required problem record

Each record must contain: `id`, `claim`, `dependencies`, `centrality`,
`decisive_test`, `success_value`, `kill_value`, `cost`, `semantic_risk`,
`status`, `owner`, `evidence`, and `next_single_gate`.
