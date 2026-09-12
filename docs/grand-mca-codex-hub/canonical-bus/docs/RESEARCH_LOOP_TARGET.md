# Research loop target — canonical architecture

## Primary objective

Build the fastest reliable research loop for mathematical theories and Lean
formalisation. The primary intelligence is **Codex/ChatGPT**; formalisation is
delegated to **Aristotle through its API**. Local tools provide computation,
reproducible checks, and small independent Lean validation.

## Roles

- **Codex / ChatGPT** — orchestrator, mathematical researcher, critic,
  integrator, and final decision maker.
- **ChatGPT Luna** — cheap bounded exploration, summarisation, and theorem
  decomposition.
- **ChatGPT Sol** — difficult research and adversarial review only.
- **Aristotle API** — Lean formalisation and full-project compilation in its
  own environment; do not assume local Lean versions match it.
- **Local compute** — Python, SymPy, Galois, Sage, NumPy/SciPy/Numba/Z3 when
  available; never treat experiments as proofs.
- **Local Lean** — optional independent replay and small proof checks.

## Critical-path policy

The critical path is:

```text
Codex/ChatGPT → local computation/checks → compact proof packet → Aristotle API
→ formal result/status → Codex integration
```

OpenCode, Docker, Sprite, DeepSeek browser automation, and local model servers
are optional experiments. They must not block the main loop or be required for
the project state to remain usable.

## State and artefacts

Use the existing local workspace and research bus. Every task produces a small
append-only packet containing:

```text
STATUS: PROVED | REFUTED | OPEN | BLOCKED
CLAIM:
EVIDENCE:
COMPUTATION_STATUS:
LEAN_STATUS:
ARISTOTLE_STATUS:
NEXT_SINGLE_GATE:
```

Never promote a computational observation to a theorem without a proof or a
clearly stated conditional hypothesis. Never put API keys in files or prompts.

## Default operating mode

- one active mathematical gate at a time;
- short Luna passes first;
- Sol only for genuinely difficult or adversarial questions;
- local computation before expensive model calls;
- Aristotle only after the claim and hypotheses are compressed;
- fresh context per task; do not reuse an oversized model conversation;
- bounded iterations by default; stop on `PROVED`, `REFUTED`, or `BLOCKED`.

## Strategic scheduling

The loop must use `docs/STRATEGIC_RESEARCH_LOOP.md` and
`staging-lean-setup/research-loop/state/PROBLEM_BACKLOG.json`. Agents first
agree on the highest-value current bottleneck; they do not simply continue the
oldest task. After every result they perform a backlog review and may replace,
split, merge, defer, or kill problems, while preserving prior evidence.

## Disabled assumptions

- Docker is not required for the research loop;
- OpenCode is not the primary orchestrator;
- local Lean is not a replacement for Aristotle's project/toolchain;
- 9router availability is not assumed for Codex, ChatGPT, or Aristotle;
- a failed optional provider does not invalidate project state.
