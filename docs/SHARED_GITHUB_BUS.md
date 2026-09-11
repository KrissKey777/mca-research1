# Shared bus configuration

```text
repository: KrissKey777/mca-research1
branch: main
visibility: public (temporary connector-access test)
integrator: codex
```

Workflow:

```text
Codex push → Agent2 reads state → Agent2 writes append-only result
→ Agent2 returns a compact result in chat → Codex audits/publishes → Codex updates canonical state
```

Agent2 currently uses read-only GitHub access. No secrets may be stored in this repository. Aristotle reports remain `RNR` until their source is independently replayed.
