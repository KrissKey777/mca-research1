# Manual Codex-first research loop

## Start

1. Keep the ChatGPT/Codex desktop app open and the computer awake.
2. Run `START-RESEARCH-LOOP.ps1 -Action start` from this directory.
3. In the desktop app open **Scheduled** and choose **Run now** for
   `grand-mca-codex-research-controller`, or open the main task and send a
   continuation message.

The scheduled controller works from the canonical bus and returns to the main
Codex task. It researches one live gate, writes only material evidence, and
stops for review when a meaningful result or a new Aristotle packet is ready.

## Stop / pause

Run `START-RESEARCH-LOOP.ps1 -Action stop`, then pause the scheduled task in
**Scheduled**. The local control file is advisory state; pausing the Codex
automation is the actual stop.

## Inspect

- `START-RESEARCH-LOOP.ps1 -Action status`
- `canonical-bus/bus/codex/` for result packets and handoffs.
- `canonical-bus/state/` for current gates and no-go routes.
- The Scheduled view for run history and failures.

## Boundaries

This loop is Codex-first and independent of Aristotle. It does not use Paseo,
OpenCode, or an external router. It does not dispatch Aristotle automatically.
Any Aristotle packet must be reviewed by Codex and explicitly sent in the
separate Aristotle lane.
