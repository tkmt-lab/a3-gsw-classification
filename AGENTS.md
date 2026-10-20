# For AI readers

1. The claim is the theorem in [README.md](README.md). Its machine-checkable form is `ClaudeChallenge.main` in [packet/formal/Formal/ComparatorChallengeMain.lean](packet/formal/Formal/ComparatorChallengeMain.lean): definitions and statement only, with a deliberate `sorry` as the Comparator target. The same definitions without the statement are in [ClaudeChallengeSpec.lean](packet/formal/Formal/ClaudeChallengeSpec.lean). Its header comment is outdated (it still mentions a `sorry` and `main`, which moved to ComparatorChallengeMain.lean); see packet/FORMALIZATION.md.
2. The proof is `ClaudeMain.main_full` in [packet/formal/Formal/ClaudeMainFull.lean](packet/formal/Formal/ClaudeMainFull.lean). Re-run it with the commands in README.md. Do not trust the saved logs if you can run Lean.
3. Every claim, with its evidence type and status, is in [packet/claims.json](packet/claims.json) (schema: `packet/claims.schema.json`). Statuses describe checks that were actually run, not intentions.
4. Detailed reading order: [packet/AGENTS.md](packet/AGENTS.md).
5. What is *not* established: human peer review of the proofs, novelty with respect to the full zigzag/position-mapping theory, a certified algorithm for ray thresholds and periods, a formal proof of the density statement.
6. If you find an error, the corrections table is [packet/P006-corrections.md](packet/P006-corrections.md).
