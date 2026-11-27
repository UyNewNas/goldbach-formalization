# P3.4: existing primitive Eisenstein analytic suppliers accepted

**The selected three-module scope passed strict source-bound compilation,
three bundled kernel replays, exact endpoint checks and the complete
defining-module/type/axiom audit. P3.4 as a whole remains incomplete.**

- Accepted source: `28f5523656d57c02a5e8eee3ed5667726d7062d2`.
- Source tree: `75ddcbe16ab1b904f6abb78ad82b09b9dac3409e`.
- P1 task: `job_8fc68a9dfac243f29e1ecd968c735209`.
- Verification finished: 2026-11-27 17:14:21, UTC+08:00.
- Draft PR: <https://github.com/UyNewNas/goldbach-formalization/pull/8>.
- Final independent evidence review: **passed**; no critical or important findings.

The receipt is [verification/report.json](verification/report.json), with exact
source/tree/clean provenance in
[provenance/worktree-provenance.json](provenance/worktree-provenance.json).
[ACCEPTANCE.json](ACCEPTANCE.json) gives the machine-readable scope and counts.

## Mathematical endpoint

The original real seed, primitive complex sum and actual Fourier integral are
preserved. The primitive index is `EisensteinSeries.gammaSet 1 1 0`, the series
has its original `1/2` orientation factor, and the period-one Fourier multiplier
is the negative phase `exp(-2*pi*i*n*x)`.

For every fixed `y > 0`, every integer frequency `n`, and every complex parameter
with `Re(s) > 1`, the actual Fourier integral has its stated complex derivative
and is analytic on the initial half plane. The two final interfaces are:

```lean
actualPrimitiveFourier_hasDerivAt
actualPrimitiveFourier_analyticOnNhd
```

The first retains the integral of the actual derivative integrand as its
derivative. The second retains
`AnalyticOnNhd ℂ (actualPrimitiveFourier y hy n) {s : ℂ | 1 < s.re}`.
Seven direct theorem-type assertions and four definitional equalities compiled
under the strict flags, fixing the actual objects and their domains.

These are existing internal construction suppliers for the frozen 1106
manuscript's continuous-spectrum implementation. They are not additional
separately numbered manuscript theorems or new external spectral estimates.
[SOURCE_SCOPE.md](SOURCE_SCOPE.md) records the exact manuscript correspondence,
downstream interfaces and exclusions. [PROOF_ROUTE.md](PROOF_ROUTE.md) explains
the real lattice bound, neighboring-exponent derivative majorant and dominated
differentiation of the actual interval integral.

## Exact declaration accounting

| Actual defining module | Original explicit declarations | Original theorems | Original def / abbrev | Generated records | Compiler records |
|---|---:|---:|---|---:|---:|
| Part3RealEisensteinSeedConvergence | 9 | 8 | 1 def | 4 | 13 |
| Part3PrimitiveEisensteinParameterAnalytic | 23 | 18 | 4 def + 1 abbrev | 7 | 30 |
| Part3PrimitiveEisensteinFourierParameterAnalytic | 25 | 18 | 7 def | 9 | 34 |
| **Total** | **57** | **44** | **12 def + 1 abbrev** | **20** | **77** |

The 57 explicit declarations include two private theorems,
`latticeMajorant_summable` and `primitive_real_pair_nonzero`; they are not added
again to the total. The complete origin classification is **55 explicit public,
2 explicit private and 20 generated**. All 20 generated records have compiler
kind theorem. Thus the compiler inventory contains **64 theorem constants and
13 definition records**. `PrimitivePair` is a source abbreviation and a compiler
definition record.

Ownership is determined by serialized defining-module metadata. In particular,
`ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic.primitiveComplexEisenstein.eq_1`
is generated in `Part3PrimitiveEisensteinFourierParameterAnalytic`; it belongs
to Fourier's 9 generated records and 34 total records. Its namespace prefix
does not move it into the parameter module's count.

[verification/declarations.json](verification/declarations.json) contains all
77 unique names, complete types, owners, kinds, origins and transitive axioms.
[verification/theorem-types.txt](verification/theorem-types.txt) renders the
complete types of all 64 theorem constants. Neither count is a claim of 64 or
77 new explicit mathematical theorems. No explicit mathematical declaration,
definition body, hypothesis or theorem conclusion was added or changed.

## Actual compilation and replay coverage

The final run reused two authenticated compiled modules and freshly compiled
one. All three were then replayed in the final environment.

| Module | Actual successful strict compile | Final-run treatment | Final kernel replay |
|---|---|---|---|
| Real seed convergence | R1, source `dc1a6cc766e519c6b54ed410707cc6b400715656` | Authenticated reuse | Passed |
| Primitive parameter analytic | R3, source `914a01e1197a9a7e7cad47f3054c6fb6e1f295e4` | Authenticated reuse | Passed |
| Fourier parameter analytic | R4, source `28f5523656d57c02a5e8eee3ed5667726d7062d2` | Fresh strict compile | Passed |

The final receipt has **108 stages, all with exit code 0**. Each stage's exact
command and log hash is retained. Compilation used the pinned Lean executable,
`-t0 -j1 -M12000 -DwarningAsError=true`; replay used the pinned bundled
`leanchecker --verbose` and recorded each target's replay output.

The R3 checkpoint retains the parameter module's real successful command and
recursively traces the inherited seed to R1. The gate rechecks both old live
checkouts, all their bound sources, strict/import logs and object parts before
copying ordinary files into a fresh object tree. Both checkpoints are checked
again at the end. Failed-module objects never supply the new run.

The final run binds **20 current source/configuration/verification inputs**,
plus the original bindings authenticated through its two checkpoints. It checks
11 configured package pins. The actual direct external inventory is **11
objects and 33 object parts**: nine source-level Mathlib imports, implicit Init,
and the audit's Lean.Util.CollectAxioms import. The checkpoint union is a subset
of this final union. These configured-package and actual-import counts describe
different things.

Final checks passed for current and checkpoint sources, the exact project
object inventory, dependency owners and object parts, tools, package roots and
pins, and clean source HEAD/tree identities. The previously accepted classical
support scope's **69 proof-input hashes remain identical**; it was not recompiled.

## Trust and proof integrity

The actual transitive axiom union of the complete inventory is exactly:

```text
Classical.choice
Quot.sound
propext
```

No new axioms or proof escapes were used. The audit rejects unsafe declarations,
axiom declarations and any transitive axiom outside that standard allowlist.
The scope uses `NORMAL_IMPORTED_ENVIRONMENT_TRUST` for the pinned external
environment. The three selected project modules were replayed; full external
Mathlib/Lean library replay is not claimed.

Lean executable SHA-256:
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Bundled leanchecker SHA-256:
`ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a`.
Mathlib is pinned to `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Repairs and retained diagnostics

There are **eleven ordered proof-expression edits at ten distinct sites**:
two real-seed sites, three parameter sites (one revised twice), and five
Fourier sites. Exact old/new fragments and diagnostic task IDs are recorded in
[SOURCE_INTAKE.json](SOURCE_INTAKE.json). Reversing those edits recovers the
three original Git blobs from baseline
`3193c2dfda0f05c334b918da3a4724907660311f`. The gate separately compares all
explicit declaration names, privacy, definitions and theorem types.

The original diagnostic and failed formal R1/R2/R3 archives are retained under
diagnostics/. R1 compiled seed successfully; R2 added no successful module;
R3 compiled parameter successfully. These partial compilation results did not
grant whole-scope acceptance. Targeted P2 source reductions diagnosed the
complex chain-rule expression and horizontal-coordinate measurability; their
reports explicitly carry `diagnostic_only=true` and `acceptance_credit=false`.
The failed coordinate-only reduction is retained alongside the successful one.

The original source-only comments remain historical provenance. Current proof
acceptance is given by this dated final receipt. The verification implementation
passed twelve focused Python tests and independent implementation and source
reviews; their scope is explained in [VERIFICATION_REVIEW.md](VERIFICATION_REVIEW.md).

## Evidence package

[evidence.zip](evidence.zip) is the lossless final archive: **87,276 bytes**,
with **128 payload members**. The archive checksum, each member's byte length
and SHA-256, all stage commands/logs/exit codes, and ZIP CRCs were checked.

SHA-256:

```text
7b591097e92a168bbe8dd7655b66296eb0b45ca46f1bfa1d41ac5f92e184adcc
```

The declaration JSON SHA-256 is
`370ffb593862830cf658a09458814fe440b17fc2f12d5a139e0bc07dc4f03484`.
The complete theorem-type text SHA-256 is
`21f1d3df3db5ccb2c6d284f2e75e55d2768739d32a5c9be924b9c6c76607d798`.
Additional artifact checksums are in ACCEPTANCE.json.

## Remaining P3.4 boundary

This acceptance does not establish the separate canonical Fourier-K right-hand
normal-convergence and identification inputs. It does not continue the initial
series to `s = 1/2 + i*t`, establish all-level Gamma0 automorphy, close R22 or
the Fricke/Whittaker amplitude chain, or prove DI/Whittaker normalization, ABL
dilation, or the full continuous Plancherel normalization.

**The PR remains a draft, no merge is requested, and the overall P3.4 board is
not promoted to green.** This is one completed internal supplier scope with
its original downstream boundaries preserved.
