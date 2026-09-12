# Grand MCA research bus

Canonical repository for ChatGPT/Agent2, Codex, and Aristotle handoffs.

## Layout

```text
state/             canonical state and context capsule
tasks/             open, active, and completed task manifests
bus/<agent>/       append-only agent handoffs
results/<agent>/   concise reports
certificates/      reproducible computation, algebra, and Lean evidence
prompts/aristotle/ formalization prompts
schemas/           validation schemas
```

Codex integrates state. Agents do not edit `state/CURRENT_STATE.*` or other agents' files.
