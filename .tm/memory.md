# Persistent Memory

These are your standing notes — important patterns, decisions, and things to watch for. Only update this file when something IMPORTANT changes (new pattern detected, strategic shift, human instruction). Do NOT append routine status updates — those go in your log file.

# Overseer Memory

## Heartbeat — 2026-02-11T13:54:00Z (Heartbeat #22) — STALE TASK RECOVERED
**Metrics**: 8 sorrys | 7 verified proofs | 6 open | 0 stale | 35 closed | 1 failed
**Status**: ⚠️ Recovered stale task. **Stale-on-build pattern detected (3rd occurrence)**

## Heartbeat — 2026-02-11T17:38:17Z (Heartbeat #54) — STALE DETECTION OVERLY CONSERVATIVE
**Metrics**: 5 sorrys | 9 verified proofs | 2 open | 0 stale (recovered) | 37 closed | 1 failed
**Status**: ⚠️ **64v detected stale at 39 min (30-min timeout). RECOVERED.**

## Heartbeat — 2026-02-12T01:39:00Z — STRATEGIC REGRESSION & AXIOM CRISIS
**Metrics**: 2 sorrys | 9 verified proofs | 1 in_progress | 4 open | 46 closed | 0 failed
**Status**: 🚨 **Strategic regression detected in KGe29.lean.**
**Observations**:
- **Axiom Refutation**: Task `1ol` refuted `residual_case_vacuous` with counterexample `(1693, 29)`. The axiom is FALSE.
- **Axiom Audit**: Task `ej8` confirmed `crt_density_large_k` is **heuristic**, not a direct citation of Stewart/Bugeaud with the constant 10000.
- **Formalization Debt**: Task `m36` closed the KGe29 sorries but used these broken axioms.
- **Strategic Review ACTIVE**: Advisor `x3y` is currently conducting a strategic review of the axiom debt.
- **Analytic Search UNBLOCKED**: Task `kgp` (explore) is open to seek a rigorous analytic proof for large-k CRT density to replace the heuristic axioms.
- **$k \le 28$ Pipeline MOVING**: The `tbc → uz7 → g43` pipeline for the $k \le 28$ residual case remains valid and unblocked.
**Actions**: Closed `m36` and `ej8`. Terminated redundant librarian tasks (`5xn`, `g5j`, `d32`, `5mh`). Monitoring `x3y` and `kgp`.

## Heartbeat — 2026-02-12T02:15:00Z — STRATEGIC RECOVERY & ANALYTIC SEARCH
**Metrics**: 2 sorrys | 3 axioms | 10 verified proofs | 1 in_progress | 6 open | 50 closed | 0 failed
**Status**: ✅ **System healthy. Strategic search active.**
**Observations**:
- **Task kgp ACTIVE**: Explorer is performing a deep analytic dive into CRT density to replace heuristic axioms. Finding: δ_k·k² < 1 holds, but exact elimination is needed for a full proof.
- **Formalization Ready**: Backlog (`tbc`, `uz7`, `g43`, `335`) is waiting for worker availability.
- **Axiom Audit Ready**: Librarian tasks `0zv` and `kf2` are open to verify the new KGe29 axioms.
- **Sorry Status**: Sorrys are stable at 2 (CrtCheck soundness and KLe28 residual case).
**Actions**: No intervention needed. Monitoring `kgp` progress.
