# P1.4 — recover complete physical rho on the SAME full modulus q

## Frozen baseline
Verified predecessor commit: `ce7321d9178b2acad5d905acd57002295a963a72`, branch `chatgpt/p1-full87-stopped-modulus-fibres-20261109`. Previous REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and full Lean proof source were read. This task branch is `chatgpt/p1-full87-full-rho-q-bridge-20261109`.

Frozen manuscript pin: `9731290e8f53cffda44129906cde6a965eaa869b`; path `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` verified by connector. Toolchain preserved: Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Constants c=49044063/25000000; K=8452171/1250000.

## Mathematical delta (candidate, not kernel-accepted)
Source: `docs/source-only/20261109-full87-full-rho-q-bridge/P4AOriginalFull87FullRhoQBridge.lean`; Git blob `c1999d3d50dd72807b646445a5d8f6c0bd867e6a`, 189 LF lines, six theorem bodies; source commit `733906dbce8728fcd78f9ab680dc45c38ae305af`.

The predecessor grouped the genuine stopped physical q-fibres, but they are not the COMPLETE original physical coefficient. The new source takes the actual physical rho already defined through `actualSmallRoughRho (R false)` on its actual supported modulus Finset, extending it by zero off support. It probes positive full q through the exact Kronecker test `highQTest 0 (qProbe q)`. For each ACTUAL even-retaining policy and each q>0, the existing original physical split at depth eight plus previous occurrence-preserving stopped-q pushforward give the candidate pointwise identity:

`supportedPhysicalRho(R,q) = rootStoppedRho(R,q) + rootRankEightRho(R,q)`.

Here `rootRankEightRho` is explicitly computed on the SAME policy's original `firstExitDepthFrontier 8 R`, with `signedTest R` on the real selectedPrefix, sign, mass, and remaining carrier, and the identical small Rosser attachment and complete full q. It does NOT reuse the other policy's eighth frontier.

At the same q>0 this is specialized to both ACTUAL P1.4 producers:
`rho_full_raw(q)-rho_full_licensed(q) = [rho_stop_raw(q)-rho_stop_licensed(q)] + [rho_rank8_raw(q)-rho_rank8_licensed(q)]`.
Both genuine policy-even witnesses are cited. There is no independent sieve-bound subtraction, no new analytic input, no numeric archive authentication, and no H_N budget payment. The pointwise theorem deliberately excludes q=0, where strict X<q would suppress the probe.

## Real checks, limitations
- Read prior branch's full 261-line source and handoff; read original physical ledger, signed test, stopped split, rank-eight invoice and concrete RAW / LICENSED policy-even sources. No applicable AGENTS.md appeared in the repository tree.
- Source commit created on separate task branch; exact remote file readback confirmed Git blob `c1999d3d50dd72807b646445a5d8f6c0bd867e6a`, six candidate theorem bodies, no forbidden syntax or holes.
- 1,800 deterministic integer multi-occurrence two-policy toy models, 1,781 with duplicated q labels and 1,682 with unequal producer populations; 21,038 nonzero individual q differences; zero violations of `(full R - full S) = (stop R - stop S) + (rank8 R - rank8 S)`. This tests finite regrouping only, NOT actual saved87 or Lean elaboration.
- Local tool check `lean --version`, `lake --version`, `elan --version` failed with command-not-found (exit 127). No pinned mathlib or matching toolchain available here. No Lean/Lake compilation, kernel replay, transitive-axioms audit, independent mathematical review or saved87 replay. Mark `SOURCE_ONLY / UNEVALUATED / UNCOMPILED`.
- No CI workflow dispatch, Codex, user-PC access, dependency upgrade, reserve payment, branch merge, force-push or master modification.

## Exact remaining obligations and next action
First stage source-only module imports inside an existing exact pinned Lean/Lake environment and run narrow `lake env lean`; fix elaboration failures and repeat, saving real exit status. Then prove a FINITE full-q reindex of the genuine rank-eight continuation occurrences if required for quantitative applications, rather than introducing a second rho. Keep the original RAW/LICENSED q-fibred difference and quantify actual first-exclusive high-q terminal plus five eighth-frontier classes under one fixed legal PP integer X, same rho_N and H_N, with one payment only.

Still yellow: saved 87-domain affine witnesses, dynamic parent and common actual histories / signed saving gain; raw/finite/filtered losses; legitimate PP X, primitive discrepancy, modulus primes/central prime/endpoint, Gevrey, ordinary residual integrals, rank9, changed/tagged arithmetic and two independent compiler/density reserve ledgers. External inputs remain unproved and unused.
