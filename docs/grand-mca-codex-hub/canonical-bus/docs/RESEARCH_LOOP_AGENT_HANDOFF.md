# Grand MCA — agent handoff

## Mission and authority

- Goal: research and prepare compact, audited proof packets for Grand MCA.
- SAFE target: `e=978944`; boundary UNSAFE test: `e=978945`.
- Aristotle owns the complete Lean project and final formalization.
- Codex is integrator and evidence gatekeeper.
- Leanstral is only an optional ad-hoc Lean assistant; it does not own the repo.
- Do not reopen: `glue-pencil`, `dyadic-only`, `generic-kernel-dimension`, or `Johnson`.
- Never put API keys in files, prompts, commits, or reports.

## Current mode

The Codex-first research loop is **active**. Six research tracks are
defined in:

```text
staging-lean-setup/research-loop/state/BIG_PROBLEM_ASSIGNMENTS.json
docs/BIG_PROBLEM_ASSIGNMENTS.md
```

Codex review lanes may continue mathematical research and local computation.
Do not dispatch Aristotle from a research cycle; Aristotle dispatch is a
separate serialized step after Codex/Luna review. Current state is in:

```text
staging-lean-setup/research-loop/state/CURRENT_STATE.json
staging-lean-setup/research-loop/state/RESEARCH_LOOP_PROFILE.json
staging-lean-setup/research-loop/state/PROBLEM_BACKLOG.json
```

## Six manual tracks

1. MathAgent + Aristotle(parallel): universal split-locator gate.
2. Aristotle(new): residual algebraic locus dimension/degree.
3. Aristotle(new): boundary stability from `t-1` to `t`.
4. MathAgent: exact high-row multi-challenge elimination.
5. ResearchAgent: transfer MCA geometry to `F_{p^6}`.
6. MathAgent-compute: aperiodic `m=8` / `MatchedFamily` UNSAFE branch.

Each result must state `STATUS`, exact hypotheses, result kind
(`PROVED`, `COMPUTATIONAL`, `OPEN`, `REFUTED`, or `BLOCKED`), evidence,
semantic risks, and one next gate. Finite experiments are evidence only.

## Roles and optimal routing

- **Codex:** read the current state, choose/integrate work, audit semantics,
  run local exact computations, and prepare Aristotle packets.
- **Luna:** cheap independent exploration, compression, ranking, and adversarial
  review. Use low reasoning and disjoint output files.
- **Sol:** only for a hard unresolved mathematical bottleneck after cheap tests;
  do not spend it on routine formatting or duplicate work.
- **Aristotle:** send only a compressed, typed theorem gate with exact hypotheses;
  it is the final Lean authority and may have a different Lean/mathlib version.
- **Leanstral:** one-shot local assistant for a single self-contained lemma,
  proof idea, error, or route check. It has no assumed full-project context.

## Leanstral one-shot usage

9router is tested and exposes:

```text
mistral/labs-leanstral-1-5-1
http://127.0.0.1:20128/v1
```

Use from the workspace:

```powershell
staging-lean-setup\tools\leanstral-ad-hoc.cmd `
  --task "Prove or refute this self-contained Lean lemma: ..."
```

For local context:

```powershell
staging-lean-setup\tools\leanstral-ad-hoc.cmd `
  --task "Repair this theorem" `
  --context-file .\lemma-context.txt
```

Treat the output as a candidate. Verify with the correct local Lean project:

```powershell
lake env lean path\to\File.lean
```

Do not send the whole Grand MCA backlog to Leanstral. Use it for fast
possibility checks before deciding whether Aristotle should receive a packet.
The lower-level launcher is also available:

```text
staging-lean-setup\tools\leanstral-prover.cmd
```

## Research-loop commands

```powershell
# Read current state
staging-lean-setup\tools\research-loop.cmd status

# Validate paused strategic state; do not apply while paused
staging-lean-setup\tools\research-loop.cmd review check

# Only after explicit authorization to resume strategic selection
staging-lean-setup\tools\research-loop.cmd review apply
```

The loop protocol, when explicitly resumed, is:

```text
DISCOVER → RANK → AGREE → ASSIGN → SOLVE → VERIFY → REVIEW → RERANK
```

Never activate more than one canonical problem without an explicit scheduling
decision. Keep agent outputs append-only under their own `agents/`, `results/`,
or `bus/` paths. Codex alone updates canonical state.

## Key documentation

```text
docs/RESEARCH_LOOP_TARGET.md
docs/STRATEGIC_RESEARCH_LOOP.md
docs/BIG_PROBLEM_ASSIGNMENTS.md
docs/LEANSTRAL_AGENT.md
docs/OPENCODE_MODEL_ROUTING.md
staging-lean-setup/research-loop/README.md
```

Before any new work, read `AGENTS.md`, then this handoff and the current state
files. Record uncertainty explicitly; do not promote a theorem to `BANKED`
without independent replay and an axiom/dependency audit.
