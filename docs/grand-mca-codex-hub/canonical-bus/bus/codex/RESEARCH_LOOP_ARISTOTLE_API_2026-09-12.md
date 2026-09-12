# Aristotle API and state-cycle update — 2026-09-12

## Verified

The official `aristotlelib 2.1.0` CLI is available through `uvx` and a
read-only `aristotle list --limit 3` call succeeded. Authentication is read
from `ARISTOTLE_API_KEY`; the key was not printed, stored, or committed.

The exact SDK base URL is:

```text
ARISTOTLE_API_BASE_URL=https://aristotle.harmonic.fun/api/v3
```

The v3 REST client uses the `X-API-Key` header. A read-only
`GET /api/v3/project?limit=1` returned HTTP 200. The local loop still uses the
official CLI, which avoids duplicating that REST protocol.

The current integration is therefore the official CLI/SDK contract, not the
previous guessed REST `/jobs` contract. The local adapter uses:

```text
uvx --from aristotlelib@2.1.0 aristotle submit ...
uvx --from aristotlelib@2.1.0 aristotle show <project-id>
uvx --from aristotlelib@2.1.0 aristotle download <project-id> ...
```

## State-machine policy

The local research loop now follows:

```text
research/consensus -> one Aristotle submit -> PAUSED_WAITING_ARISTOTLE
-> watch -> atomic output capture -> adversarial analysis -> NEXT_PROMPT_READY
```

Automatic resubmission is disabled. A failed or incomplete result cannot
silently trigger another paid/limited job. `LOOP_CONTROL.json` and
`ARISTOTLE_JOB.json` contain state only; they never contain credentials.

## Not claimed

No Grand MCA prompt has been submitted by this update. The verified API access
does not make any Aristotle cloud report formally replayed; all cloud outputs
remain subject to the existing `REPORTED_NOT_REPLAYED` policy.
