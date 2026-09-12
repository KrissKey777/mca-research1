# Hub source manifest

Generated 2026-09-12 from the local workspaces.

## Included

- `canonical-bus/bus/codex/`: 17 non-secret Markdown bus packets from
  `C:\Users\kross\Documents\Codex\mca-research1\bus\codex`.
- `canonical-bus/state/`: the current state capsule, gates, no-go list and
  sync cursor.
- `canonical-bus/docs/`: the research-loop handoff, target and strategy.
- `research-reports/`: 129 top-level Markdown reports from the local
  Aristotle(parallel) output bundle.
- `loop/source-state/`: the prior local loop control/profile snapshots.

## Deliberately excluded

- API keys, account records, environment exports and secret-bearing files.
- Generated build directories and bulk Lean source trees; their canonical
  paths are preserved in reports and can be replayed when the source bundle is
  available.
- Chat transcripts: Codex exposes task handles, not a supported bulk-export or
  move operation. See `chat-index/CHAT_INDEX.md`.

The canonical bus remains authoritative. This hub is a curated, local backup
and navigation layer.
