# P1.4 root weighted frontier — scope and external input register

## Pinned sources and local theorem dependencies

- Original manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, Git blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, §4. Relevant: same first-exit policy with physical `g_N(p) = 1_{p>2, p∤N}/(p-1)`, common signed residual weight and asymptotic identification. No changes to parameters.
- Root finite recursion: `ImbalancedChen/FirstExitDepthSplice.lean` (`firstExitDepthFrontier`), `ImbalancedChen/FirstExitTree.lean` (`firstExitCorrection`), `ImbalancedChen/FirstExitFrontierInvariants.lean`. Existing fixed root modules, not reproved.
- New parent and owner: `docs/source-only/20261104-full87-licensed-sixth/P4AOriginalFull87LicensedSixthPolicy.lean` and `P4AOriginalFull87LicensedSixthRealization.lean`, `docs/source-only/20261105-full87-eighth-arithmetic/P4AOriginalFull87OwnedEighthSource.lean`; these are SOURCE_ONLY and their imports require staging.
- Failure enumeration/weight: `docs/source-only/20261106-full87-failed-attempts/P4AOriginalFull87FailedAttempts.lean`, `docs/source-only/20261106-full87-physical-failed-weight/P4AOriginalFull87PhysicalFailedWeights.lean`.
- Finite physical prime density: `ImbalancedChen/ChenInitialPrimeSource.lean`, already existing `chenInitialBoundingSieve_prime_density`; no new density axiom.
- Exact target-factor deletion power gap is recorded in source-only predecessor `44731a0`; **not paid again**.

## Internal proof scope and exact status

NEW SOURCE_ONLY/UNEVALUATED proof body: for identical parent/policy, changing unit weights to `halfProductDensity` changes only the actual selected-prefix incoming mass of the entire ordered root-to-eight frontier. The unchanged owner/trim filter acts on history and commutes with reweighting, including all occurrences. The corresponding physical owned-state first-exit correction is expanded by the same rejected-event recursion, not by a substitute weighted average. No root saved87 archive validation, no full signed physical saving, no rank-nine inherited-square estimate, no primitive/modulus/centre error or asymptotic ordinary residual integral has been inferred.

## External inputs, registered but NOT PROVED OR INVOKED

1. Ordinary Rosser upper/lower density (§4, `eq:current-raw-density`): same normalized raw `V_N^+(R,y)/V_N(y) = F(log R/log y) + o(1)` at fixed s>1, lower f for s≥2. Exact independent theorem reference, uniformity, domain and coefficient hypotheses: **UNVERIFIED**.
2. Mertens/PNT (§4, `eq:current-mertens`): `V_N(N^u) = (2 exp(-gamma) C_N)/(u log N) * (1+o(1))` for fixed u>0 with claimed even-target uniformity. Independent provenance, hypotheses, normalization and variable endpoints: **UNVERIFIED**.
3. Signed prime-product progression (§3 `eq:current-PP`): the same `rho_N(q)` in AP and exact coprime mean for original allowed smooth families, claimed `O_{A,W}(N(log N)^(-A))`. Validated independent source theorem and uniformity not established: **UNVERIFIED**.

None are implemented as new lemmas, axioms or admitted proof terms. The needed internal owner/correction/physical density coupling remains in scope. Source: `docs/source-only/20261106-full87-weighted-root-transport/P4AOriginalFull87WeightedRootTransport.lean`; source blob `0afbb97b6f5ba621f7a0c75a8b4868575f5186c7`. Verification: SOURCE_ONLY/UNEVALUATED; COMPILED=false, KERNEL_REPLAYED=false, TRANSITIVE_AXIOMS=false, INDEPENDENT_REVIEW=false, CI_DISPATCHED=false.
