# Research loop health — 2026-09-12

## Verified

- Aristotle(parallel) credential and project routing: available.
- Aristotle(new) credential and project routing: available.
- Aristotle(parallel) project: `62630cae-3e85-4c02-b6ce-b636a93e86cc`.
- Aristotle(new) project: `2fe94968-ae7b-4af1-b9b3-d547e4dd7eb4`.
- Two-lane adapter and watcher: syntax-checked and tested against the
  Aristotle(new) project-status command.
- Keys remain outside files and are mapped to the official CLI only in the
  child process.

## Current blocker

The local research worker reports `BLOCKED_NO_MODEL`: no
`MCA_LLM_BASE_URL`/`MCA_LLM_MODEL` is configured. OpenCode is installed, but
the local loop has no configured OpenAI-compatible research endpoint and the
cloud Lean project is not present locally. The loop therefore fails closed
instead of falsely claiming that Codex/Luna/Leanstral are running.

## Intended operation

Cloud Aristotle tasks continue independently. Once a local model endpoint or
an approved worker is configured, use `research-loop.cmd health` as the
preflight; significant results only are promoted to the GitHub/Space bus.
