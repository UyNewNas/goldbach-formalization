# Existing primitive Eisenstein analytic suppliers: scope and sources

Baseline: `3193c2dfda0f05c334b918da3a4724907660311f`.

## Actual endpoint

The three existing modules construct the literal nonholomorphic seed
`Im(z)^s / ||c*z+d||^(2*s)`, its actual primitive complex sum with factor `1/2`,
and the actual period-one Fourier integral with phase `exp(-2*pi*i*n*x)`.
The intended final interfaces are `actualPrimitiveFourier_hasDerivAt` and
`actualPrimitiveFourier_analyticOnNhd`, for fixed `y > 0`, arbitrary `n : Int`,
and the initial half plane `Re(s) > 1`.

The first module has no project import. The second imports the first and the
third imports the second. The exact closure contains three project sources and
nine distinct source-level Mathlib imports. Implicit Init and the owner's audit
dependency are bound separately by the actual compiler import output.

These are already-existing internal construction suppliers for the manuscript's
continuous-spectrum implementation. They are not three separately numbered
claims in the frozen 1106 paper. This continuation verifies those actual source
objects; it creates no replacement spectral theorem or additional conjecture.
The existing source-only comments record their original October provenance;
current acceptance must be read from the dated verification receipt.

## Manuscript correspondence

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes at
`8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`,
`paper/release-20261106/en/analytic-appendix.tex`, SHA-256
`e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`.

| Manuscript lines | Relevant object | Boundary of this supplier scope |
|---|---|---|
| 951–958 | Actual level, cusps and Fourier normalization conventions | No level-N Gamma0 or Fricke/cusp-one conversion supplied here |
| 977–982 | Actual continuous term and its positive spectral measure | Initial primitive series only; no general character-pair fibers or measure theorem |
| 994–996 | `R^E(n,t) = n^(it) * phi(n;1/2+it)` | Actual Fourier left-hand side in Re(s)>1 only; no critical-line phi identification |
| 1008–1024 | Continuous norm with `dt/pi` | No new all-cusp sum, Plancherel normalization or large-sieve estimate |

The positive base can be either below or above one. The original logarithmic
majorant handles both cases using neighboring real exponents; no artificial
global base <= 1 assumption is added. Zero lattice vectors remain permitted in
the all-pairs majorant. The source comment that the zero term vanishes is used
only in the relevant s > 1 range; it is not an assertion about s = 0.

## Real downstream interfaces

`Part3ActualComplexEisensteinCanonicalFourier.actualPrimitiveFourier_eq_complexCanonical`
uses the Fourier analytic endpoint in its existing identity-theorem argument.
It separately requires `Part3ActualEisensteinCanonicalFourier` and
`Part3ActualRamanujanBesselNormalConvergence`. Those evaluated right-hand inputs
are not silently accepted by this three-module check.

`Part3PrimitiveEisensteinParameterAutomorphy.primitiveComplexEisenstein_SL2_analytic_eqOn`
uses the parameter analytic endpoint and genuine primitive-pair reindexing.
Its automorphy proof is outside this scope.

The original R22 prefix uses `horizontalPoint` directly, while its critical
level invariant still requires `completedLevelOldform_Gamma0_invariant` and
`criticalParameter_mem_completedRegularDomain` from Part3AllLevelContinuedMaass.
Initial-half-plane analyticity cannot replace those actual all-level inputs.
The original `completed_fricke_nonzero_integral_critical` amplitude boundary
also remains separate.

## Prior-evidence survey

An exact-name local search of docs/ and verification/ found only the static
source recovery catalog, R22_PROJECT_SOURCES.json and the previous endpoint
audit. No matching report, acceptance JSON, declarations inventory or log was
found in that bounded search.

P1 diagnostic task `job_ebe10753532840d1a0a8e0d270f35cb2` then checked 17 current
conventional loose project-object roots for these exact three module paths.
It found no candidates. This is a bounded survey, not a global historical
nonexistence claim, and no compressed recovery packages were searched again.

## Original-source diagnostic and first repairs

The same task strictly compiled the exact original first module and failed at
two proof-expression steps. No project object was accepted or reused from it.
The original archive is diagnostics/original-r1.zip, 23,976 bytes, SHA-256
`3cf53a8f80f7ee6187a0587e26a34104f2aaaa3408dfb55b5a06e777e49e7174`;
all 48 manifest members were checked.

At original line 100, positivity did not supply nonnegativity of the strip
majorant. The repair explicitly combines r_pos, norm_nonneg and real-power
nonnegativity. At original line 129, strict lint requested simp instead of
simpa for the empty compact set branch. The actual statements, definitions and
all hypotheses are unchanged. SOURCE_INTAKE records exact original/repaired
fragments; reversing them recovers each original whole-file hash.

The first formal run, `job_36b2b2b90d654e08be15882c06be9672`, then passed
strict compilation of the repaired real-seed module and failed in the original
parameter module. Its archive is diagnostics/formal-r1.zip, 40,214 bytes, SHA-256
`2e0a107f206608f52bd03d6996152595b821805de06f56941a6306110dc159dc`;
all 66 manifest members were checked. This is compilation evidence for the
first module only, not a completed analytic-scope acceptance.

The three parameter repairs use Real.rpow_two for the actual real numeral
exponent 2, use the already constructed exponential chain-rule proof via simpa,
and supply the required neighboring-exponent inequality by binary addition
monotonicity. The pinned Mathlib source at
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`,
Mathlib/Analysis/SpecialFunctions/Pow/Real.lean, was inspected; rpow_two is
exactly the real-exponent-to-natural-square equality. No exponent domain,
positive-base assumption, derivative definition or endpoint type was changed.
These five proof sites are recorded as exact reversible changes in SOURCE_INTAKE.

Formal R2, `job_6459fcf2122749bea91b558c0ea6147d`, authenticated and reused
the seed object, then stopped at the remaining parameter derivative expression.
The generic composition proof and the original target displayed different
HasDerivAt instance paths. Its full archive is diagnostics/formal-r2.zip,
43,103 bytes, SHA-256
`c59ddb211e05f83042a15e1cd0f9b98c26b81cf0e77e57ecb70bd46874a9bede`;
all 71 payload members and archive CRCs were checked. No new full module or
kernel replay passed in that attempt.

The final candidate at the same derivative site explicitly unfolds the original
functions and uses hasDerivAt_mul_const followed by the dedicated cexp chain
rule. A diagnostic reduction copied the original four definitions/abbreviation
and the exact theorem head. P2 task `9bd41b1d44a04fff8a0756d9a85398a9`
strictly compiled this reduction under the same Lean executable hash and Mathlib
commit. Its source, authored launcher, exact log and report are in diagnostics/.
It supplies diagnostic evidence only and grants no full-module acceptance.
The candidate was independently reviewed and applied to the original module.
There are now six ordered repair records at five distinct proof sites, and
reversing them still reconstructs the original source files exactly.

R2 produced no additional successfully compiled module, so continuation keeps
the direct R1 checkpoint rather than adding an unnecessary intermediate copy.

The successfully compiled seed prefix is eligible for authenticated checkpoint
reuse to avoid repeating valid compilation. Current source hashes, the actual
strict log, pinned environment and every object part must match before reuse;
the eventual full run still performs all three kernel replays and the complete
endpoint, owner, type and axiom checks.

## Source-level accounting before compilation

| Module | def | abbrev | theorem | private theorems included | Explicit total |
|---|---:|---:|---:|---:|---:|
| Real seed convergence | 1 | 0 | 8 | 1 | 9 |
| Complex parameter analytic | 4 | 1 | 18 | 1 | 23 |
| Fourier parameter analytic | 7 | 0 | 18 | 0 | 25 |
| Total | 12 | 1 | 44 | 2 | 57 |

These are source declarations, not a prediction of the generated compiler
inventory. Any eventual acceptance must distinguish explicit private declarations,
public declarations and generated constants using actual owner/type evidence.
