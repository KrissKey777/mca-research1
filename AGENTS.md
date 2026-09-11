# Grand MCA shared research bus

Before work, read `state/CONTEXT_CAPSULE.md` and `state/CURRENT_STATE.json`.

- Codex is the sole integrator of `state/CURRENT_STATE.*`.
- Agents write append-only files under their own `bus/` and `results/` directories.
- Never overwrite another agent's artifacts.
- Use statuses `PROPOSED`, `COMPUTATIONAL`, `RNR`, `REPLAYED`, `BANKED`, `KILLED`.
- `BANKED` requires independent replay, exact signature/dependency checks, `#print axioms`, and a relevant successful build.
- Never commit API keys, tokens, passwords, or credentials.
- Sprite is optional and not on the communication critical path.
