# P5 resume: corrected actual Upsilon6 product restriction

State: WAITING_FOR_P0. Request: REQUESTED. Verification: SOURCE_ONLY.

- Baseline: 1337e2db4712fb4a9f86add073f771f84b66d0c8; branch codex/chen-resume-p5.
- Candidate: ImbalancedChen/CurrentChenUpsilon6ProductRestriction.lean (177 lines; 2 definitions, 6 theorems).
- Source SHA256: 94d2280862aa1d62dc6ccbc041944a79b1ab63b98371429d7c0d3e7392ff35fa.
- Local Git commit was not created because author identity is not configured. The selected file is staged and frozen; no other source was changed.
- Complete locally readable project-source import graph: 34 modules, fingerprint c8147a6186e5126deb04dcf6c341383de01cda02a54ef1142b08c566d6bb3bb3. External modules are pinned but actual objects are unavailable here; P0 must bind them for verification.

## New result (not compiled)

For actual current Upsilon6, retain the original pairs outside E only when p1*p2 <= N^(1/2 - 2*(417/5000) - eta). The source proves exact retained-plus-discarded decomposition and retained <= actual Upsilon6 by nonnegativity of the actual quotient cardinalities. Upsilon11 and every negative ledger term are unchanged.

For each fixed real B and eta>0, one threshold precedes every retained pair and every E. Reusing the accepted arbitrary-beta quotient-level geometry, the source proves N^(eta/2) < D/z^2, hence D/z^2>1 and actual s>2, where Q=floor(sqrt N/(log N)^B), D=Q/(p1*p2)+1, z=N^(417/5000). The logarithmic loss and both natural floors are therefore inside the imported actual-level argument. No assertion is made at eta=0 or s=2.

## Existing supply reviewed

The new baseline contains current-source InitialSource, InitialRosser and InitialRosserRemainder successful compilation receipts. They remain component-level evidence, not a completed mean or hLower. CurrentChenMeanLedger exactly matches its accepted source hash in the round2 receipt. ChenQuotientLevelGeometry exactly matches beb8a4d, whose full verification is recorded in PROOF_STATUS; its older source-header candidate comment is stale. The arbitrary-beta theorem is reusable despite historical old-exponent specializations later in that file. No old MovingInterval task was blindly repeated.

## Static checks and scope

Whitespace and forbidden-token screens passed, as did exact Fraction checks of the buffer coefficient. These are not Lean verification. A real exponent witness x=7/50, y=11/50 lies in the full current pair rectangle but has x+y=9/25 > 833/2500 and model s=700/417<2; this is only a region calculation, not a prime-existence claim.

No Lean/Lake/checker/audit/CI was started, and nothing was pushed. The frozen request includes source-only theorem types, exact project-source closure, pins, prior receipt pointers, and all missing acceptance stages.

## Remaining proof obligations

The retained-region analytic mean and integral must still be proved and numerically recomputed. Boundary loss must be controlled before eta tends to zero. Strong causal weights, every negative-row estimate, error absorption and the common threshold remain unpaid. currentC stays 49044063/25000000; actual D12 is unchanged; hLower is still OPEN. P4 small-sieve supply may be used, but final hUpper is not a dependency.

Next: P0 verifies the frozen leaf; repair concrete diagnostics if any. Do not extend this unverified layer during this round.
