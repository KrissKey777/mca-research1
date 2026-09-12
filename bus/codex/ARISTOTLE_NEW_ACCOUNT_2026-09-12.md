# Aristotle(new) account and project routing

The separate Aristotle(new) API credential is stored only in the user's
machine-level user environment under `ARISTOTLE_NEW_API_KEY`; no secret is
stored in this repository.

- Project: `proximity-prize-main`
- Project ID: `2fe94968-ae7b-4af1-b9b3-d547e4dd7eb4`
- Last task: `4eb9cefa-779c-4a35-8ae8-3e6fab5b839b`
- Last status: `COMPLETE_WITH_ERRORS`
- Last reported result: `MATCHEDFAMILY_DECISIVE_REDUCTION`

This is a separate UNSAFE/MatchedFamily lane. It must never use the
Aristotle(parallel) credential or project. The loop state records the two
lanes independently and keeps Codex/Luna review between outputs and future
dispatches.
