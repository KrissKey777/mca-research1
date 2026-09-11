# Shared bus configuration

```text
repository: KrissKey777/mca-research1
branch: main
visibility: private
integrator: codex
```

Workflow:

```text
Codex push → Agent2 reads state → Agent2 writes append-only result
→ Agent2 pushes → Codex audits/replays → Codex updates canonical state
```

No secrets may be stored in this repository. Aristotle reports remain `RNR` until their source is independently replayed.
