# Actual atlas mass versus the original ordinary seed source

Status: **SOURCE_ONLY_UNCOMPILED**. Formal, kernel, endpoint and new-native credit remain **0**. The source has been read back exactly; no compiler, cloud job, ref update or edit to an accepted module was performed.

## Deliverable

| Module | Git blob | SHA256 | Bytes | Lines |
|---|---|---|---:|---:|
| `P2FiniteMarkedGamma5SeedAtlasOrdinaryComparison` | `c9d5255f97eff22d18d06b5f3296b58dd90ecc03` | `78693a468892c956790bfdc2b6a9ee54c4271076d3677d707bb51c96b70f19ec` | 2823 | 55 |

Path: `docs/source-only/20261125-p2-9-seed-atlas-ordinary-comparison/ImbalancedChen/P2FiniteMarkedGamma5SeedAtlasOrdinaryComparison.lean`.

## Actual conclusion

`atlas_mass_le_original_ordinary_plus_epsilon` fixes the original root precision `n` with `1/(n+1)≤11/384`. For every positive epsilon it constructs a physical width parameter `h∈(0,1/8]` and a native mesh function `m : Index 430→Nat`. Eventually in `N`, for all `tau∈[0,1/12]`,

`norm N * Σ v : Entry n, fixedWeight v.shape * Σ u∈Part3.labelledPrimeTuples (rank v) (2*N), weight v (planAt m v) (radialWidth h) ... (acceptAt U4 tau m v) N u`

`≤ norm N * seedMass N n U4 tau (fun p w => ordinaryBad N (rootQ N n U4 tau p) w.prod) + epsilon.`

This is the existing actual Family weight, the original finite seed marks and the original `ordinaryBad` source. The main coefficient is **one**. No complete-product coprime assumption, distribution licence or desired ordinary-quality bound is an input.

## Three existing steps, with exact quantifiers

1. `SeedAtlasOrdinaryExcess.atlas_mass_le_exact_cell_plus_epsilon`, source **5b7090a10e0ac1a707a4119acae3f02ea170c109**, is used with `epsilon/2`. It fixes the mesh before `N` and works uniformly in every later `h∈(0,1/8]`.
2. `SeedOrdinaryReindex.literalMass_eq_seedMass`, current source **189a61645dd730f8a6297e54b9e66f24334b5c9d**, is an exact same-target finite sum identity. It charges no error and preserves old-coordinate order, repeated primes, empty tails and the original same-Q cell.
3. `SeedOrdinaryPrice.profile_le_ordinary`, source **1e46d63390ee2cecdfca55b6a4642eac6451b8b1**, is used with `epsilon/2`. It fixes the physical width before `N` and retains the original marked sharp source with coefficient one.

The proof intersects the two eventual bounds after selecting the same `h` and `m`. The final target and root loss are chosen afterwards. No sum of errors over moving primes or moving history positions is introduced.

## Source selection and qualification

The registry inherits the exact OrdinaryExcess packet **b73912cc5043c2eff53fbd56ef0a24938e636c8c** and selected-wall packet **656fb16b6015a522adfb038ca400bc5ccc7f35aa**, including all current owner postimages.

Select the current Reindex **189a61645dd730f8a6297e54b9e66f24334b5c9d**, not its earlier subtype-sum proof. Retain RootStrips **521b485f8167c760d816aa2e01ec137bad8a9bac**, CellAtlasStrips **9a0a6ad021f3ae1c455c2731d0451bf9011b7cee**, the readout-core owner removals, Tuple **56572a3ad02bb9c35c535d87800b164542cd3d2f**, ProfileCollar **33196c7c3fc1c4aeac651871482bb142e55deca8**, and NaturalMass **5a22a4e7aeb47b39b7052e9a184703d577e5c112**.

The assembled historical and finite-fallback receiving closure still needs its normal compilation, kernel replay and full owned-declaration audit. This packet records exact source composition and does not infer qualification from any earlier thin-module acceptance.

## Manuscript boundary

The frozen [1106 argument, 359–407](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex#L359-L407) fixes finite positive families and their ordinary mass before the prime-product estimate. The [1106 selected-family and limit discussion](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L1090-L1101) fixes the queries and approximation before the target tends to infinity. This source supplies the final ordinary-mass composition for the actual constructed atlas family.

It does not define a replacement `J`, prove the separate prime-tested majorization, invoke PP or distribution, or assert that P2.9/W1/W2 or a native H247 compatibility branch is complete.
