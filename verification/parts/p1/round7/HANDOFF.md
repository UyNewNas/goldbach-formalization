# Part 1 round 7: verified integer cutoff, exact-head evidence intake

## One independently accepted batch

The source commit **b416a21d70255a94dfc44c03aade3bd118de2f6e** on branch `chatgpt/chen-p1-history` has now passed the previously pending Lean core and specialized CI. This batch **accepts the existing conditional integer strict-cutoff proof**, rather than introducing an uncompiled additional mathematical claim.

Core CI: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38345607447, job 115126187673. Head SHA exactly matches the proof source. The original job log records (2026-10-13 UTC):
- **Build full project**: exit 0, elapsed 3519s. Both `ImbalancedChen.HistoricalFifthIntegerCutoff` and `ImbalancedChen.HistoricalFifthIntegerCutoffAudit` built.
- **Original bundled leanchecker**: exit 0, elapsed 506s. The log explicitly includes replaying the proof module.
- **Root transitive-axiom audit**: exit 0, elapsed 32s. The independent compiler-type audit reports **seven actual defining-module declarations** on both build and later audit, with identical records and no forbidden axioms.
- Specialized CI: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38345607444, SUCCESS on the same source HEAD.

The archived complete compiler-pretty types and transitive axioms are [DECLARATION_TYPES.json](DECLARATION_TYPES.json), obtained from original `Meta.ppExpr info.type` output, not source extraction. [VERIFICATION.json](VERIFICATION.json) binds the run/job/artifact, stage return codes, frozen manuscript, repository source blobs and dependency pins. The original GitHub job log is linked above. Its associated short-retention artifact has SHA256 `ad0ec47c5f9917aa87961b28577a56617544c782c525860ef31baac230bed63f`; expiry 2026-10-27. Original failure at proof-source commit `043aa217c3848f6ccdffbd587f31d22945ee5d27` was the unknown `pp.maxDepth` option in the audit; it is fixed in the now accepted proof HEAD.

Mathematically this discharges the previously **unverified** endpoint safety for `historicalIntegerCutoff N b = floor(N^b)+1`, and accepts the already supplied exact normalized saving identities and two fifth integral-limit specializations using that integer cutoff. It does **not** prove the specific manuscript adopted-cap instance.

## Exact scope of this documentation-only commit

The mathematical baseline is `1a80c1bcce67886f699d097fc37fd245cd3620bf`; frozen manuscript commit `ba6ec11d800eccc54406490631895e174de85766`. Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, and goldbach `09b97db5764ade1246bfb77206baa1b124760958` are unchanged.

This commit contains only immutable evidence documents. Its resulting SHA is **not** asserted to have undergone fresh CI. The exact accepted **proof source** SHA is given above. There is no local Lake/Lean toolchain in the current execution environment; the recorded strict validation is the GitHub Actions run, not a fabricated local re-execution. CI's retrieved job log does not supply direct-import `.olean` SHA256 values; do not invent them or imply that all imports were separately kernel-replayed in this run.

## Remaining obligations

The actual adopted historical `J/I/old/nu/cap` rows and their old-ancestor identities are still required. The finite H/h `certify_finite_step_table.json` is not such a table, and P2's `exact_Z` fiber cutoff is not the adopted stored cap. The independently reported fifth module remains `SOURCE_PENDING`, separate from the now validated joint fifth geometry/integral. Full multilevel correction, physical prime-tuple distribution, boundary/global truncation and the final 1+1.75 count remain open. Next batch should pursue a concrete source-backed bridge, or ingest and validate the missing adopted-cap rows; do not replicate old conditional interfaces.
