# P1.4 signed physical deletion ledger — internal/external boundary

## Frozen primary source

Manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, Git blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, §4. We keep the original actual sixth parent, eighth owned state list, frozen levels, full modulus attachment, physical weights `halfProductDensity` and the signed count convention. No parameter changes.

## Internal inputs reused as literal code, not new hypotheses

- `ImbalancedChen/FirstExitTree.lean`: original `firstExitCorrection`; `docs/source-only/20261106-full87-failed-attempts/P4AOriginalFull87FailedAttempts.lean`: actual ordered rejected occurrences and signed `value`.
- `docs/source-only/20261106-full87-weighted-root-transport/P4AOriginalFull87WeightedRootTransport.lean` at blob `0afbb97b6f5ba621f7a0c75a8b4868575f5186c7`: same actual root-to-eight physical state list and correction.
- `docs/source-only/20261106-full87-physical-failed-weight/P4AOriginalFull87PhysicalFailedWeights.lean`: weight-independent ordered event labels, true `g_N` source.
- `docs/source-only/20261106-full87-actual-deletion-once/P4AOriginalFull87ActualDeletionOnce.lean`: same-source integer gap and `targetDeletionFactor` bound at ranks ≥11; `P4AOriginalFull87TargetPrimeDeletion.lean`: finite exact factor itself.
- `docs/source-only/20261105-full87-eighth-arithmetic/P4AOriginalFull87OwnedEighthSource.lean`: original owner/trim and `frontier_sign_mass`, `physical_saving_eq_owned_sources`.
- Existing `RealizedHistory` comes from `P4AOriginalFull87ActualCommonHistory`; full original87 instance supply is **not established** by this packet. No new result-equivalent structure field was introduced.

## Exact interpretation of this packet

The comparison term `v(a)*targetDeletionFactor N a.rejected hi` is deliberately introduced as a finite ledger, NOT as an asserted identity for the original physical arithmetic sieve coefficient. The new proof concerns actual signed physical failure values `v(a)` from the original recursion and same physical occurrence keys. Only the rank≥11 sublist is controlled and only one factor is inserted per event. Absolute-value sum bounds are used; there is no monotonicity assertion for signed saving or arithmetic-zero inference from geometric null sets.

## Outside number-theoretic inputs — REGISTERED / UNVERIFIED / NOT IMPLEMENTED / NOT INVOKED

1. **Ordinary Rosser upper/lower density**: manuscript §4 `eq:current-raw-density`, asserted normalized relation `V_N^+(R,y)/V_N(y)=F(log R/log y)+o(1)` for fixed `s>1` (lower `f` for `s≥2`). Independent source version, exact hypotheses, parameters, coefficient support and claimed uniformity remain **UNVERIFIED**. Planned use only in identifying the original ordinary continuation with a residual integral; no theorem introduced or called.
2. **Mertens/PNT**: manuscript §4 `eq:current-mertens`, fixed-`u>0` relation `V_N(N^u)=(2e^{-γ} C_N)/(u log N)*(1+o(1))` with proposed even-target uniformity. Reference, normalization and changing endpoint hypotheses **UNVERIFIED**. No proof or use in this finite comparison.
3. **Same-rho signed prime-product progression**: manuscript §3 `eq:current-PP`, original same `rho_N(q)` AP and exact coprime mean difference `O_{A,W}(N(log N)^{-A})`. Applicable actual source domain, smoothing/coefficients, uniformity, independent version **UNVERIFIED**. Not proved or invoked.
4. **Already internal finite density identity**: `ImbalancedChen/ChenInitialPrimeSource.lean` has `chenInitialBoundingSieve_prime_density` at actual primes, reused via prior source packet. This is NOT recorded as an outside analytic theorem.

None of (1)-(3) has been asserted as an axiom or admitted Lean statement. Same-source coupling, `RealizedHistory` actual supply, signed reserve, residual integral, errors, and numeric archive remain manuscript-INTERNAL obligations even when external inputs are eventually applied.

Verification: SOURCE_ONLY/UNEVALUATED, COMPILED=false, KERNEL_REPLAYED=false, TRANSITIVE_AXIOMS=false, INDEPENDENT_REVIEW=false, no CI. Code SHA `1e35586fa6965bc14229bfabf7a62b1ce4407ada`, blob `6b431f93f528258f0b72a13e30a9ee24473f0e22`.
