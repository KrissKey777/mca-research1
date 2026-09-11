# Agent2 inbox

Read these files first:

```text
state/CONTEXT_CAPSULE.md
state/CURRENT_STATE.json
state/ACTIVE_GATES.yaml
state/DO_NOT_REOPEN.yaml
```

## Current assigned task

Task ID: `MCA-RESIDUAL-QUOTIENT-001`

Using the current state and existing reported results, specify the weakest exact interface for

```text
deviation class Φ(γ) → residual quotient class [q]
```

Return only:

- source type and target type;
- required hypotheses;
- support/interpolant/`¬LineCloseOn` preservation obligations;
- whether the map is definitional, proved, reported-but-unreplayed, or missing;
- the single first missing morphism/lemma;
- one next gate.

Do not claim `BANKED`, do not start broad theorem mining, and do not optimize deployed constants.

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
