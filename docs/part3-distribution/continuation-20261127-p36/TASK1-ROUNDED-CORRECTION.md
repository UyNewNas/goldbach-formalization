# Rounded original U5 exact mean and correction cost

The module `ImbalancedChen.P3OriginalU5RoundedPrimeCorrection` applies the exact-coprime prime identity in the 1106 manuscript’s sieve appendix (`sv:coprime-prime-error`) to the finite rounded U5 estimator. For each original ordered pair and quotient, the modulus is precisely `(t.1 * t.2) * k`. The exact row mean is the complete prefix cardinality times that row’s signed reciprocal-totient density minus its signed modulus-prime correction.

The absolute value of the combined modulus-prime and centre corrections is at most the sum of `atomCost` over active rounded coefficients. The primitive discrepancy stays signed in the count inequality. Each active quotient is a positive integer. Under the actual cap it lies in the interval from one to the floor of `X / (t.1 * t.2)`, where `X = N^(599/1000)`. The two elementary prime error contributions cost at most `2 * log N / log 2` per quotient. The original selector’s reciprocal-totient mass bound then pays the sum of pair reciprocals uniformly in the policy and both real parameters. For every positive `eta`, the resulting upper bound is eventually at most `eta * singularNormalization N`.

This argument bounds the two errors for the pair-labelled count at order `N^(599/1000) * log N`. The manuscript’s `log² N` estimate concerns a squarefree physical coefficient counted at each modulus. The present argument keeps the pair labels and their multiplicities. The sharp logarithmic order, a lower bound on the original main term, and common-Q distribution of the signed primitive discrepancy require additional arguments.

## Source identity

The source of the sieve appendix used here has SHA-256 `99eb5be7f5ba3c7c8a03729e1ee47efba7e9a3fa75796aeb13059837909c61ec`. The following local files were byte-compared with Git commit `525747fe88f8a6847c479bfe4a5bcc15aa13003a`.

| Accepted module | SHA-256 |
| --- | --- |
| P3OriginalU5PairNormalizedDensityReserve | `737f3c895dcf91546eebfd8e96a4225c33cf2598595527c913385a325d257463` |
| P3OriginalU5RoundedCountInsertion | `7a05c1899cb6048e2b6c169556d33ac07c0d4899f28167e87117824ca434c1ed` |
| CurrentChenP5CausalPrimeCorrectionPayment | `35200e9b6ffb98528136068f64c5dc22f6efb41d40cab08d04985aa7513b7d51` |
| ChenInitialPrimeSource | `330fab9edc70b63f56fb28b7b83748427b269c42da54ee67dd14a812a36720f2` |
| P2LowerFiniteCellBetaCompiler | `879483a8f7ed1d9e17b5c80f6023f0043f715a5f48ffc25b9227ee7a8d58bc15` |
| PowerErrorBudget | `d4b65c0a99377bf3cfb4807bd418f427d03d98791919852e5822094843ed5e82` |

The project pins Lean `v4.33.0-rc1` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Exported statements

- `rowExactMean_eq` gives the finite identity for every pair and every real rounding parameter.
- `abs_row_corrections_le` and `abs_corrections_le` bound the absolute combined signed correction at row and family level.
- `original_U5_rounded_main_sub_correction_lower` inserts the exact total-prime mass and signed discrepancy into the actual U5 inequality.
- `correctionCost_le_power_log` gives the finite quantitative payment with the actual full-modulus cap and a pair harmonic bound.
- `eventually_uniform_correction_payment` fixes an arbitrary positive error budget before the integer threshold and all choices of rounding parameters and pair policy. Its only row premise is the strict full-modulus cap for nonzero coefficients.

## Strict compilation

P1 preflight job `job_75b3df00a11742cd8e1cab5d9e3fe4df` verified 286 accepted source files and 286 object hashes. It installed the isolated overlay at `/workspace/p36-rounded-correction-20261127`. The compilation command, with that path as `root`, was:

```bash
source "$root/env.sh"
cd "$root"
lean -t0 -j1 -DwarningAsError=true -R "$root" \
  -o "$root/objects/ImbalancedChen/P3OriginalU5RoundedPrimeCorrection.olean" \
  "$root/ImbalancedChen/P3OriginalU5RoundedPrimeCorrection.lean"
```

P1 job `job_a5d9344407cb44998e911a48f7b30483` verified the transferred source checksum and compiled all 13 user-written declarations on attempt 001. Exit code was 0, elapsed time 15.498 seconds and peak memory 6,867,619,840 bytes. The compiler emitted no diagnostics. Job `job_cb4d195aa4fa4db68c861b9fdcc580c2` read back these SHA-256 values.

| Item | SHA-256 |
| --- | --- |
| New Lean source | `1b3201297cbe21fca9bbd980a7042c38d86371c87bc864238f5601549b44af52` |
| Compiled .olean | `ed583082dfd0c51fa33aa1b8787627fb8f7ba7cd472a26542f8abdbad9eee02d` |
| Compiler diagnostics | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

The combined continuation verification records the independent kernel replay and transitive axiom inventories for this module and its count assembly.
