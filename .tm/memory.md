# Persistent Memory

These are your standing notes — important patterns, decisions, and things to watch for. Only update this file when something IMPORTANT changes (new pattern detected, strategic shift, human instruction). Do NOT append routine status updates — those go in your log file.

# Overseer Memory

## Heartbeat — 2026-02-11T13:54:00Z (Heartbeat #22) — STALE TASK RECOVERED
**Metrics**: 8 sorrys | 7 verified proofs | 6 open | 0 stale | 35 closed | 1 failed
**Status**: ⚠️ Recovered stale task. **Stale-on-build pattern detected (3rd occurrence)**

## Heartbeat — 2026-02-11T17:38:17Z (Heartbeat #54) — STALE DETECTION OVERLY CONSERVATIVE
**Metrics**: 5 sorrys | 9 verified proofs | 2 open | 0 stale (recovered) | 37 closed | 1 failed
**Status**: ⚠️ **64v detected stale at 39 min (30-min timeout). RECOVERED.**

## Heartbeat — 2026-02-11T21:36:14Z — DAG CLEANUP & PIPELINE UPDATE
**Metrics**: 5 sorrys | 7 verified proofs | 1 open | 0 stale | 40 closed | 0 failed
**Status**: ✅ **System healthy. Cleanup performed.**
**Observations**:
- **erdos1094-pef CLOSED**: Manually closed as redundant.
- **erdos1094-64v RESTARTED**: Working on CRT sieve in `Erdos/CrtCheck.lean`.
- **Residual sorry detected**: `u5p` closed its task but left a sorry in `Erdos/KLe28.lean:271` for n ≥ 500,000.

## Heartbeat — 2026-02-12T01:31:00Z — KGe29 AXIOMS UNDER FIRE
**Metrics**: 2 sorrys | 9 verified proofs | 7 open | 1 in_progress | 0 stale | 44 closed | 1 failed (recovered)
**Status**: ⚠️ **Strategic review triggered.**
**Observations**:
- **Axiom Crisis**: `KGe29.lean` formalization closed but relies on 3 axioms now under review.
- **`crt_density_large_k`**: Verified by librarian (`ej8`) as heuristic/asymptotic only.
- **`residual_case_vacuous`**: False as stated; `1ol` found counterexample (17,2). Needs restriction to $k \ge 29$.
- **Action**: Created advisor task (`x3y`) to decide on axiom restriction vs. proof redesign.
- **Recovery**: Reopened `ej8` after parse failure.
