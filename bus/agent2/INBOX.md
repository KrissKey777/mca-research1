# Agent2 inbox

Read these files first:

```text
state/CONTEXT_CAPSULE.md
state/CURRENT_STATE.json
state/ACTIVE_GATES.yaml
state/DO_NOT_REOPEN.yaml
```

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
