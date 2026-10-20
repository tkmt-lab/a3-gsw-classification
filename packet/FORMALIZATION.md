# Exact formalization scope and reproduction

P006-15: [owner statement-meaning confirmation](OWNER-STATEMENT-CHECK.md) is recorded separately from proof review. The owner self-reported the check on 2026-10-19; no human proof peer review or novelty review is claimed. This revision changes review metadata and exposition only; all proof sources, saved gate logs, kernel receipts and mathematical statements retain their v7 checkpoint. No new Lean or external-kernel run is made.

The proof is ClaudeMain.main_full in [ClaudeMainFull](formal/Formal/ClaudeMainFull.lean). It proves the independently specified complete classification for natural k,l with 0<l<k; there is no gcd=1 hypothesis. LiteralPath uses distinct vertices, even length, consecutive and skip adjacency, degree-five ends and degree-six next-to-end vertices; it does not exclude internal degree-five vertices. [The definitions](formal/Formal/ClaudeChallengeSpec.lean) are separate from the team's proof and use only mathlib imports. The human reading guide is preserved as [original](challenge-reading-guide-ja.original.log).

Primitive necessity and the closed nonprimitive quotient are connected by proved graph isomorphisms to that specification. Sufficiency comes from ClaudePos.criterion_sufficient. The benchmark module [ComparatorChallengeMain](formal/Formal/ComparatorChallengeMain.lean) contains a deliberately unfinished target, while [ComparatorSolutionMain](formal/Formal/ComparatorSolutionMain.lean) uses main_full. Benchmark stubs are not imported by the proof root. Do not confuse those benchmark target holes with axioms of the proof.

[Minimum](formal/Formal/ClaudeCorMinimum.lean) proves minimum_negative, minimum_below and minimum_at (unique negative at T<=399), together with the norm/primitivity arithmetic. The graph order formula 20T is not itself a theorem in this formal package. Kernel decide, not native_decide, checks the bounded arithmetic table.

[Affine arithmetic](formal/Formal/ClaudeCorRays.lean) proves criterion periodicity. [The release bridge and gate](formal/Formal/A3ReleaseCheck.lean) also derives graph path-existence periodicity on all eventually interior integer affine rays, including nonprimitive points. It proves existence of a positive period and threshold, not a certified executable algorithm computing them. The full cor:rays wording therefore remains partially open. Density is intentionally excluded.

## Optional Lean execution in a working copy

The four Python checks only inspect saved metadata. To actually check the proofs, use a separate working copy and the pinned Lean 4.35.0/mathlib environment. No dependency caches are distributed. The standard library Python driver [run_formal_gate.py](run_formal_gate.py) refuses missing or revision-mismatched dependency checkouts. Populate dependencies only by a separately chosen, explicit setup step. In the existing pinned environment run `python3 -B run_formal_gate.py`. The driver uses one Lean process at a time, -j1/-M4096, a preventive RSS stop below 4 GiB, and a 7.5 GiB aggregate Lean stop. It prints the measured peaks; it does not survey all other research applications. The task's overall research allocation is 8 GiB.

The driver builds +Formal:olean, then directly re-elaborates Formal/A3ReleaseCheck.lean. That module freshly prints selected axiom dependencies and rejects every transitive dependency outside propext, Classical.choice and Quot.sound. A temporary custom-axiom declaration is deliberately submitted to the same gate and must fail. No declaration from this control is imported into the proof. The control file is retained under .gate-controls in the separate working copy as an execution record.

The dependency manifest and toolchain are pinned; binaries and .lake caches are absent. The packet source import closure is checked locally. Reusing an existing cache is not a fresh dependency rebuild, OS sandbox or independent specification review.

## Fixed Comparator receipts

The full classification was compared to the independent challenge and accepted by Lean standard, Lean paranoid, lean4lean, nanoda, con-leche and con-ron. See [full receipt](comparator-main-2026-10-19.md.original.log), [raw output](comparator-main-paranoid-2026-10-19.txt.original.log), and [configuration](formal/comparator-main.json). The receipt reports 212.1 seconds and maximum 2.99 GB. The run disabled the unavailable Linux sandbox on macOS. It verifies the same proof with six kernels, not six independent derivations; the minimum and ray proofs were not included in that Comparator target. The v7.1 update checks the fixed receipt bytes rather than rerunning the six kernels. The earlier [primitive receipt](comparator-primitive-2026-10-19.md.original.log) and its outputs are also supplied. [The corollary receipt](corollaries-report-2026-10-19.md.original.log) is preserved with its historical primitive-only graph-ray scope, superseded by the release bridge.

[formalization.json](formalization.json) fingerprints sources, pins, gate outputs and fixed receipts. Historical records listed in REDACTIONS.json are public derivatives; unlisted original receipts remain fixed. Old relative identifiers and original-language prose are inert provenance, not execution instructions. Two independently derived prose proofs (research team and R004) remain distinct from these checks. The owner-reported confirmation of the classification challenge meaning is recorded separately; human proof peer review and novelty against full prior position-mapping theory remain outstanding. Optional further independent-kernel checking does not discharge those obligations.

## Successful gate and rejection control are different records

[T1192](T1192-formal-gate.original.log) records the thirteen successful
allowlist checks. It contains no rejection-control execution; absence of
that line is not evidence that T1192 ran the control.

The supplied [T1202 raw output](T1202-detached-formal-gate.original.log),
[trial metadata](T1202-trial.json.original.log) and
[execution receipt](T1202-execution-receipt.json.original.log) are
**privacy-redacted public derivatives**, not the original byte sequences.
Their original/public hashes and sizes are paired in [REDACTIONS.json](REDACTIONS.json)
and [REDACTIONS.md](REDACTIONS.md). The recorded rejection outcome, return
codes and measurements remain historical facts reported by those records.
The [historical source inventory](T1202-source-SHA256SUMS.original.log) is byte-identical
to the original inventory; its hash is
`81f699514074521ef75206c7f55624ed3e41cb9b77042c0747e96cb1ba9a14f7`.
All 165 Lean source files, their pinned dependencies and the driver remain
byte-identical to the 1.0.3 packet. This edition inherits its historical build
and axiom receipts; it does not run Lean or claim a fresh kernel execution.
The T1202 run reused existing dependencies/build cache; it was not an OS
sandbox or a clean dependency rebuild. Expected rejection output remains
separate from successful gate logs and is not a proof dependency.

## Scoped ray records in claims.json

For `cor:rays`, the `lean` object records `ClaudeCor.criterion_ray` and its `additional_declarations` entry records `R002.A3Release.path_ray`. Both are existence-only, with their exact types, source commits, hashes and saved T1192 axiom output. `effective_algorithm_certified` is false; the entire corollary remains open for a certified executable threshold/period algorithm. The 47 fully Lean-proved claim statuses do not change. This unchanged-source packaging phase runs no Lean; it inherits the 1.0.3 build and axiom receipts without extending their scopes.

The module header in ClaudeChallengeSpec.lean is stale: its `sorry`/`main` target is in ComparatorChallengeMain.lean, while ClaudeChallengeSpec.lean contains definitions only; all Lean bytes are preserved and the previous packet build receipts are inherited without running Lean in this packaging phase.

## Editorial separation in article 9.0

The article uses neutral mathematical names; exact implementation names, Comparator targets and verification history are in VERIFICATION-RECORD.md. All 165 Lean sources and proof scopes are unchanged. The 57 claim records preserve their original status_scope wording (including historical edition references), as exact evidence records rather than newly dated review. No new owner-confirmation procedure or Lean run.
