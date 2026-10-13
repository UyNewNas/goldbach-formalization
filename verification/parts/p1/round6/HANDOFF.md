# Part 1 round 6 — integer-cutoff audit option repair

## Exact branch and frozen dependencies
- Parent HEAD: `043aa217c3848f6ccdffbd587f31d22945ee5d27` (P1 only, `chatgpt/chen-p1-history`).
- Frozen manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
- Shared mathematical baseline: `1a80c1bcce67886f699d097fc37fd245cd3620bf`.
- Lean: `leanprover/lean4:v4.33.0-rc1`; mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; goldbach: `09b97db5764ade1246bfb77206baa1b124760958`. Pins and the proof source are unchanged.

## Actual prior verification (not inferred from earlier handoff)
- Core run https://github.com/UyNewNas/goldbach-formalization/actions/runs/38336495842, job `115097646206`, exact head `043aa217c3848f6ccdffbd587f31d22945ee5d27`: **FAILURE**, completed 2026-10-13 03:18 UTC. Stage `Build the full project` failed; original leanchecker and root axiom audit **SKIPPED**. Original job logs and artifact: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38336495842/artifacts/11787215370 (SHA256 of zipped artifact `f7e2abd6730b0e7306b53c696248afde38acc732f1a115785815781f456bbc3a`).
- Precise failure: `ImbalancedChen/HistoricalFifthIntegerCutoffAudit.lean:7:0: Unknown option \`pp.maxDepth\``. The source `ImbalancedChen.HistoricalFifthIntegerCutoff` itself showed `✔ [9782/9786] Built ... (4.2s)` immediately beforehand, but successful leaf elaboration is **not** yet full three-gate acceptance.
- Despite that unrecognized option, the audit run printed a complete defining-module census with **7 declarations**, actual pretty-printed compiler types and transitive axioms `[propext, Classical.choice, Quot.sound]` on every item; however **the audit module exited 1**, so this output is **not** an accepted certificate.
- Exact-head specialized run https://github.com/UyNewNas/goldbach-formalization/actions/runs/38336495825, job `115097646663`: **SUCCESS**; do not substitute that specialized success for failed core verification.

## Targeted change this round
Remove **only** the unsupported `set_option pp.maxDepth 100000` line from `ImbalancedChen/HistoricalFifthIntegerCutoffAudit.lean`. The allowed axiom set, defining-module enumeration (including generated/private declarations), compiler-type printer, count and proof statements remain identical. No new mathematical assumption, theorem, `sorry`, `unsafe` or `native_decide` has been introduced.

**Verification status for this new commit: PENDING**. This run has no local Lean or Lake toolchain; do not claim local strict compilation, original checker replay, or core CI acceptance for the repaired revision. Receive exact-SHA core and specialized CI; if the root passes, record full three-gate logs and artifacts. If another failure occurs, inspect the exact compiler message instead of starting a duplicate heavy build.

## Unclosed mathematical/physical bridge
Real adopted `J/I/old/nu/cap` rows and actual ancestor identities, all earlier/later history pieces, global truncation and boundary bridges, and prime-tuple physical counting remain pending. No equivalence between P2 `exact_Z` fibre cutoff and the stored cap is asserted. The earlier independently reported fifth-layer source remains `SOURCE_PENDING` rather than being conflated with current fifth-cell modules. This isolated audit repair does **not** complete 1+1.75.
