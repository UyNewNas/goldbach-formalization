# Part 4: one physical upper weight, density and real bad count

## Status and fixed sources

This checkpoint contains candidate proofs of finite same-weight bridges,
exact normalization, and explicitly conditional assembly theorems. **The
new Lean sources have not yet passed compilation and kernel replay. This
checkpoint does not prove the manuscript's sharp K bound or the final
hUpper.** A successful compilation
of an assembly theorem does not discharge its displayed analytic inputs.

- Accepted base: `1a80c1bcce67886f699d097fc37fd245cd3620bf`.
- Accepted base tree: `1fd54b8b4d5fd89abc767ee7e8d814453453b29c`.
- Working branch: `chatgpt/chen-p4-upper`.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes` at
  `ba6ec11d800eccc54406490631895e174de85766`.
- Body: `paper/source/manuscript-body.tex`, Git blob
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- `currentK = 8452171 / 1250000 = 6.7617368`.
- Lean: `leanprover/lean4:v4.33.0-rc1`; all eleven dependency revisions and
  the bytes of the three toolchain/dependency files remain frozen.

The verification artifact records its own complete checked-out commit SHA,
source hashes, final object hashes, declaration inventory and actual gate
results. Use that SHA and its run result when forwarding this checkpoint.
No change to `ImbalancedChen.lean`, existing modules, existing workflows or
Lake configuration is required by these additions.

## Second round: actual verification status, 12 October 2026

**This round does not upgrade any of the five modules to verified status.**
The proof-source checkpoint is still
`262f69822a386a9d44efc059bceba11049668d68`, tree
`0b55ec4f1e9dc98a2b90e9511d8997a711815eae`. The local branch and remote
branch were both checked at that commit, with a clean local working tree.
This round changes this handoff document only. All five Lean modules, the
audit module, runner, workflow, manuscript map, definitions and dependency
pins retain their exact first-round bytes. The document's enclosing commit
is a documentation checkpoint, not a newly verified proof checkpoint.

The fixed Part 0 record is
[`9fe1d6b8b68a97cad3a122410ad7fde1701eed35`](https://github.com/UyNewNas/goldbach-formalization/blob/9fe1d6b8b68a97cad3a122410ad7fde1701eed35/docs/CHEN_175_BASELINE_INTERFACES.md),
`docs/CHEN_175_BASELINE_INTERFACES.md`, blob
`fd97c85489ce1613245a65e0c9f21736bc8cb7dc`, SHA-256
`eecc2a876f45ab54f58d59718768961b75553b215daa798d5ac06bccd360c139`.
Its section 9 explicitly records source checks only, with no Lean run.
Its historical baseline success descriptions do not include reusable raw
logs for these five new modules. It does not change the accepted proof
baseline or supply the missing complete Part 1 construction.

### Executed checks and stages that did not run

| Check | Actual result in this round | Proof significance |
|---|---|---|
| `git merge-base --is-ancestor 1a80c1bcce67886f699d097fc37fd245cd3620bf HEAD` | Exit 0 after restoring the authenticated original parent object `08d6e1385f747f8a0e45e77689f7c714653ac8f4` | The original ancestry gate now passes; no gate or history link was changed. |
| `python3 verification/verify_part4_upper.py --check-lockfiles` | Exit 0: `Frozen configuration hashes match; proof verification has not run.` | Configuration identity only. |
| Existing `check_dependency_heads` and `import_closure` functions, called from Python | Exit 0; all eleven exact revisions and clean dependency sources; 710 non-Mathlib source files; required Mathlib import is `Mathlib` | Dependency/source identity only; no cache retrieval or build. |
| Existing lexer and forbidden-source scan on the five modules | Exit 0; no forbidden proof escape found | A textual check, not a transitive axiom audit. |
| Python comparison of all 15 Part 4 theorem signatures printed below with the fixed source; exact-byte checks of the five modules and unchanged verification/configuration files | Exit 0; all signatures match, and only this document differs from the first-round checkpoint | Source-extracted types only. |
| `git diff --check` | Exit 0 | Whitespace only. |
| Official pinned `lean --version`, one short probe | Exit 1 before option parsing; raw output below | No source elaboration or Lean error location was produced. |
| Five strict source compilations | Not run | No module is compiler-confirmed. |
| Five bundled `leanchecker --fresh --verbose` replays | Not run | No kernel receipt. |
| `Part4UpperAudit.lean`, complete types and transitive axioms | Not run | No compiler-printed type or axiom inventory. |

The once-executed local probe was:

```text
argv = ["/workspace/scratch/8c23f867e026/lean-toolchain-local/lean-4.33.0-rc1-linux/bin/lean", "--version"]
timeout_seconds = 5
exit_code = 1
stdout = ""
stderr = "error: failed to locate application\n"
executable_sha256 = e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

The probe transcript did not retain its launcher working directory; this
is not reconstructed as if observed. Repository identity was checked
separately. The official tag resolves to
`62eed1db4d67327ec8120be05f1a1b0847d74561`.
The pinned [`Path.lean`](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Util/Path.lean),
[`shell.cpp`](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/util/shell.cpp),
[`io.cpp`](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/runtime/io.cpp)
and [`InstallPath.lean`](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/lake/Lake/Config/InstallPath.lean)
were checked against their Git blobs. Internal startup calls `getBuildDir`
and `IO.appPath` before parsing options. `LEAN_SYSROOT` and `LAKE_HOME`
configure other discovery paths; `LEAN_PATH` is read after the failing
internal lookup. None replaces this startup step. The prior `/proc` denial
was not probed again, and no runtime permission workaround was attempted.

### Existing fixed-commit Actions receipts, read without rerunning

Every job below completed with `failure`, `runner_id = 0`, empty runner
name, `steps = []`, and artifact count 0. These are absence-of-execution
records, not Lean compilation failures. Their pre-step failure cause is
not exposed by the inspected records and is not guessed.

| Fixed source | Workflow run | Job |
|---|---|---|
| P0 `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` | [Core 38193659310](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38193659310) | `114631558052` |
| Same P0 source | [Variable envelope 38193659252](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38193659252) | `114631558092` |
| P4 `262f69822a386a9d44efc059bceba11049668d68` | [Part 4 38194874181](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38194874181) | `114635212674` |
| Same P4 source | [Variable envelope 38194874170](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38194874170) | `114635212363` |
| Same P4 source | [Core 38194874169](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38194874169) | `114635212661` |

No workflow dispatch or rerun, full-verifier rerun, new toolchain/cache
download, or Codex task was performed in this round. An automatic workflow
event caused by publishing this documentation would not be a proof receipt
and is not used here. The existing verification runner remains the next
command for a normal environment where the pinned Lean actually starts;
its full build, strict builds, fresh replays and inventory gates remain
required. No successful batch receipt can be supplied from this environment.

The five exact proof-source SHA-256 values are:

| Module | SHA-256 | Compilation / kernel / axiom status |
|---|---|---|
| `ActualUpperPolicyDensity` | `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6` | Not run / not run / not run |
| `UpperCoefficientPerturbation` | `59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef` | Not run / not run / not run |
| `ActualUpperDensityAssembly` | `241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d` | Not run / not run / not run |
| `RealPhysicalUpperWeightBridge` | `f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d` | Not run / not run / not run |
| `RealUpperCountingAssembly` | `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96` | Not run / not run / not run |

The local diagnostic transcript is retained at
`.lake/part4-upper-verification/round2/environment-diagnosis.json`, SHA-256
`ab572c6b6fb29efda0eaecfc94756aa0fe10d51e0b4ed73ead05b3f0cd0d74fc`;
the raw probe transcription is `round2/lean-version-probe.log`, SHA-256
`2fd3a0237f3e152f95ab02a2065ad6119a6c681d038e89260a46ab67ce4be845`.
These local logs are not claimed to be committed CI artifacts; the actual
commands, outputs, hashes and job identifiers needed for the status decision
are transcribed above.

## Owned files and real outputs

| Module | Output | What it does not supply |
|---|---|---|
| `ActualUpperPolicyDensity` | Identifies an even-retaining Boolean policy with its actual odd-first-exit coefficient, support and physical attachment; proves the selected and historical policies preserve this parity. | A complete adopted policy, its certified integral, or a boxed-compiler identity. |
| `UpperCoefficientPerturbation` | Transports coefficientwise rough domination to the actual sign-attached majorant and bounds physical density changes by a weighted absolute coefficient difference. | A numerical compiler-error bound or legal factorization support. |
| `ActualUpperDensityAssembly` | Exact manuscript-scale identities; correct precision-before-target limit-to-density assembly; a separate compiler budget transport. | Instantiation of the full-policy integral and certificate premises. |
| `RealPhysicalUpperWeightBridge` | Exact real-b source Fubini and three-term decomposition; finite RealB bound with both losses; positive outer-source comparison; raw actual-rho strict-ceiling and support adapters. | An analytic signed distribution theorem or legal smooth outer approximation. |
| `RealUpperCountingAssembly` | The exact epsilon/eventual real hUpper conclusion from precision-indexed same-weight inputs, using the already proved source mass and endpoint absorption. | Proofs of its displayed density, coprime-error and signed-distribution inputs for the final compiled weight. |

## Weight identity and normalization

For a raw odd retention predicate, the actual coefficient is the existing
`actualSmallRoughRho retainOdd N cap w z L`. It is the literal

```lean
smallRoughRho
  (actualSmallRosserSupport N cap w)
  (fixedRoughSupport retainOdd N cap w z)
  (fixedRoughCoefficient retainOdd N cap w z)
  (actualSmallRosserMinus N cap w L)
  (actualSmallRosserPlus N cap w L)
```

The sign of the rough coefficient selects beta-plus or beta-minus before
the small/rough pair is uniquely reindexed by its product. For every use,
the density is exactly

```lean
physicalDensitySum Q rho = ∑ q ∈ Q, rho q / (Nat.totient q : ℝ)
```

The manuscript coefficient is measured by
`physicalDensitySum Q rho * Real.log N / singularSeries N`.
For `N >= 2`, bounding this by `k` is equivalent to bounding the unnormalized
density by `k * (singularSeries N / Real.log N)`. The source scale multiplies
it exactly:

```lean
((N : ℝ) / Real.log (N : ℝ)) *
  (singularSeries N / Real.log (N : ℝ)) = singularNormalization N
```

The existing `ActualNormalizedRhoError` already proves the conversion from
`D = N^nu`, including the factor `nu`; it has not been reproved or replaced.
For the manuscript's upper cutoff the parameters must satisfy
`nu * sieveR = 19/96`. Neither internal exponent is the imbalance `b`.
There is no Chen quarter, extra factor two or ordering factorial in this
upper density. The ordered source mass is exactly `log (1/b)`.

The real strict prime cutoff `p < z` is precisely the natural strict
cutoff at `Nat.ceil z`, including an integral value of z. The new indicator
identity also covers all integer test arguments, zero and negative ones.
The raw actual coefficient's prime-product support divides this same sieve
product; that divisibility does not imply the manuscript's modulus exponent.

## Raw policy and compiled coefficient are separate obligations

The manuscript boxes an ideal policy into a rough coefficient `a_N(d)`
that dominates the raw coefficient. A boxed support need not be prefix
closed. Therefore `a_N` is not silently identified with
`fixedRoughCoefficient` for another policy.

If Part 1 proves such a literal equality, `ActualUpperPolicyDensity` provides
the exact attachment identification. Otherwise the final coefficient must
be the generic `smallRoughRho small rough a_N betaMinus betaPlus`, on a
common rough carrier. `UpperCoefficientPerturbation` proves both the
domination and density-perturbation transports for that generic coefficient.

One sufficient compiler budget is

```lean
M * reciprocalTotientDensity rough (fun d => |a_N d - raw_N d|)
  <= compilerReserve * (singularSeries N / Real.log (N : ℝ))
```

where both actual small densities have absolute value at most M. This is a
sufficient absolute-error interface, not a claim that the manuscript's
adopted boxes satisfy it. A direct proved one-sided density transport for
the same compiled coefficient can serve the same role.

### Second-round audit: carrier, slopes, and the remaining reserve

The source audit found no definite mismatch between the three density
modules, but it did identify a finite connection that has not been made.
The raw density theorem returns the retained carrier `Rraw`; the compiler
theorem uses one common carrier `R`. If the compiler enlarges support,
`Rraw ⊆ R` and zero extension of the raw coefficient must be proved and
used to transport both the rough divisor sum and the sign-attached physical
function/density. The fact that the current generic theorem accepts a common
carrier does not perform this transport automatically.

In particular, with `S = actualSmallRosserSupport N cap w`,
`Rraw = fixedRoughSupport retainOdd N cap w z` and the literal zero-outside
`raw = fixedRoughCoefficient retainOdd N cap w z`, the finite missing
connections include the following expressions under `Rraw ⊆ R`, with the
same actual `betaMinus` and `betaPlus`:

```lean
supportedDivisorSum R raw = supportedDivisorSum Rraw raw

smallRoughRho S R raw betaMinus betaPlus =
  smallRoughRho S Rraw raw betaMinus betaPlus

physicalDensitySum (smallRoughModuli S R)
    (smallRoughRho S R raw betaMinus betaPlus) =
  physicalDensitySum (smallRoughModuli S Rraw)
    (smallRoughRho S Rraw raw betaMinus betaPlus)
```

These are pending finite adapter obligations, not new declarations or
compiler-confirmed types. The definition of `smallRoughRho` is a finite
fibre sum, so zero extension can be handled without asserting uniqueness
of arbitrary new fibres. The later compiler/density factorization requires
`∀ d ∈ R, RoughPrimeSupportedAt w d` and the unchanged small support;
that cutoff separation supplies its unique small/rough factorization.
The existing baseline supplies the finite ingredients. This is a suitable
Part 4-A next step after the existing modules pass their actual proof gates;
it is not an additional analytic hypothesis to charge to Part 2.

The two small-density absolute bounds can likewise use the existing
`exists_actualSmallRosser_density_sandwich`. With its actual even-target
Euler product `V > 0` and relative error `Esmall ≥ 0`, one can take
`M = V * (1 + Esmall)` for both slopes, including a possibly negative lower
density. This is a finite consequence of the existing sandwich, not a new
analytic supplier. The compiled error must still control the product
`M * ∑ d ∈ R, |compiled d - raw d| / φ(d)`. A signed coefficient difference
or a bound normalized only by `V` does not supply that product for free.

The current assembly's reserve is correctly explicit: choose
`rawBound = E`, `densityCap = E + u`, then pay `compilerReserve = u`
once an actual compiler-error bound is proved, using `E + 2*u ≤ currentK`.
Within the first step, each of the raw-limit and attachment errors uses
`u/3`, so its output is even at most `E + 2*u/3`. The displayed cap remains
`E + u` for the separate compiler step. No actual integral or compiler
estimate is supplied merely by this bookkeeping. The raw-at-K specialization
does not supply a positive compiler reserve.

If an upstream bound has already charged finite-partition or historical
truncation errors, those costs belong in the first u. They cannot be charged
again after renaming `E + u` as a new raw endpoint. Fixed attachment precision
also leaves a fixed exponential part of the small relative error; it does
not disappear merely by increasing N.

The final exponent/normalization dictionary is also still an instance
obligation. If an upstream main-term limit is normalized by `log D` with
`D = N^nu`, its coefficient `U` becomes `U / nu` on the `log N` scale,
because `log (N^nu) = nu * log N` for `N > 0`, `nu > 0`. The existing
`ActualNormalizedRhoError` correctly chooses its attachment tolerance as
`eta * nu` before this conversion. That attachment-error result does not
convert an unrelated upstream main integral, nor establish its bound by E.
The current density assembler demands the main limit already in
`log N / singularSeries N` units. No new Euler-product or singular-series
normalization is introduced in this round.

## Minimal unresolved handoffs

### Part 1 to Part 4: complete actual construction

Supply the full adopted causal policy and its actual compiled coefficient,
with support and coefficient identities. This includes all adopted stages,
inherited decisions, tails, owned endpoints and the one-time accounting of
each saving. The fixed-family fifth-prefix limit is already available but
does not cover the complete adopted historical construction.

For the raw-attachment path, the new
`exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits`
expects the actual full reciprocal-totient density, multiplied by
`log N / C_N`, to tend to an explicitly defined integral. If the policy
depends on attachment precision, this must hold for every sufficiently
small positive precision. The attachment theorem then chooses a precision
in that interval before taking a common target threshold. A theorem at an
unrelated single precision is insufficient.

This `Tendsto` premise is a sufficient interface, not a claim that every
upper certificate computes the exact raw-density limit. If an actual P1
result supplies only an upper envelope after dropping nonnegative savings,
that envelope must not be substituted as the exact limit. The eventual
inequality or limit comparison must be connected explicitly when that
producer is available. No second conditional assembler was added to hide
this distinction.

The more general
`exists_actualSmallRoughRho_density_le_of_full_policy_limits` retains an
explicit `densityCap`. For example, after the true integral is bounded by
E, a cap of E+u allocates u to the limit/attachment step and leaves the
second u for compilation. The two internal approximation errors each use
one third of `densityCap - rawBound`. Returning only a raw bound at K
would discard the reserve needed by a later compiler step.

For the compiled path, also supply coefficient domination, an actual
compiler-error budget, cutoff-separated support, squarefreeness,
target-coprimality, bounded coefficients and the physical/support
factorization gates needed by Part 3. Raw support divisibility alone does
not supply `theta_* = 599/1000` or the auxiliary local factorization cover.

### Part 2 to Part 4: the adopted upper certificate

Supply the Lean inequality for the real integral of that exact full
construction and the adopted data, with fixed source/data hashes. The
manuscript endpoint is

```text
E = 9979702576710911234850619807816847864907359959
    / 1475913550962201227946780619099353215139840000
u = 145007961227048312210593427530128000784681
    / 11807308407697609823574244952794825721118720000
K - E - 2u = 71229286727542131248758574547050908572431
    / 737956775481100613973390309549676607569920000000 > 0
```

The two u budgets pay different finite operations: density approximation
and compilation. The already proved small-prime attachment reserve must
be allocated within this chain, not treated as proof of the entire
compiler budget. The rational identity above is not the integral theorem.
The 17,572-cell lower certificate is not an upper-K supplier.

A read-only check of Part 2 at
`195f19cfcedeaf7793ccce3f1d42d27fcfe4f815` confirms that its new first-row
paired-fibre integral certificate is a lower-side result. Its
[`docs/part2/PART1_INTERFACE.md`](https://github.com/UyNewNas/goldbach-formalization/blob/195f19cfcedeaf7793ccce3f1d42d27fcfe4f815/docs/part2/PART1_INTERFACE.md)
explicitly excludes certification of the whole upper K. It does not supply
the missing upper integral premise here. Its independent workflow
`38193423556` failed before any job steps ran and has no successful
compilation artifact. That snapshot has not been imported or used as an
accepted replacement baseline.

The later Part 2 snapshot
`b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` adds an upper-side candidate:

```lean
theorem ImbalancedChen.Certificates.AboveMuSecondCoarse.adopted_coarse_lower :
    (640339 / 15210735000 : ℝ) ≤
      ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral
```

This is the adopted `above_mu_second_coarse_only` saving, with a negative
sign in E. Its [fixed handoff](https://github.com/UyNewNas/goldbach-formalization/blob/b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e/docs/part2/HANDOFF.md)
explicitly retains the other adopted integrals, full policy-to-integral
dictionary, coverage, signed ledger and both actual reserve bounds as
unfinished. The new candidate has no successful Lean verification. It is
useful partial input, but it does not instantiate `hIntegral` or the full
`hCertificate` in the density assembler.

The second-round read kept that exact Part 2 commit. Its handoff blob is
`c9f673fa356a480960b76c8cc2f5b34f21cc71ff`, and the
[`AboveMuSecondCoarse.lean` source](https://github.com/UyNewNas/goldbach-formalization/blob/b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e/ImbalancedChen/Certificates/AboveMuSecondCoarse.lean)
blob is `ec2814fba4aa3ddc204847fc34a9f1f2f052a358`. Its physical pullback
has the factor 4 matching the existing initial upper-residual saving's
normalization. This is a compatible local expression, not yet a theorem
identifying a full-policy saving with that chart integral. The actual
first-exit domain, change of variables, arithmetic ownership and boundary
reserve still need a proved dictionary. At the closed chart corner
`k = 1, u = v = 1`, `chartY = oldResidual = newResidual = 19/96`, so the
residual ratio is exactly 1. That corner cannot satisfy the baseline compact
supplier's strict condition `1 < s`; an admissible interior approximation
and arithmetic boundary reserve cannot be replaced by a null-volume claim.
No Part 2 source was imported as an accepted supplier in this round.

### Part 3 to Part 4: the same final physical weight

Supply the signed physical modulus sum for the exact real ordered source,
or a proved transfer from a licensed smooth outer source. The sharp-source
spelling is `realPhysicalDistributionError b N T (Q N) (rho N)`, with
`T = manuscriptHalfProductCutoff kappa N`. Its center retains the actual
coprime source mass divided by the actual totient.

The outer-source bridge compares nonnegative complete divisor sums before
using the signed expression
`sum d in Q, rho d * finitePrimitiveDiscrepancy S weight N d`.
It does not replace this by the sum of moduluswise absolute discrepancies.
That bridge explicitly assumes `m <= N` on its outer carrier. A licensed
outer approximation crossing `m > N` still needs the integer-shift Fubini
adapter; natural subtraction cannot be used there.

The real half-product coprime correction is exactly zero if the displayed
roughness and active-support gate holds. Otherwise its normalized error
remains a visible input. A general labelled product family still needs its
own coprime-mask estimate; it is not covered by this zero-correction claim.

The read-only Part 3 snapshot
`d5d1fffbf9e74061985da31d82dedaeab02d9659` has a
[`UniformPrimeProductTarget` definition and a handoff](https://github.com/UyNewNas/goldbach-formalization/blob/d5d1fffbf9e74061985da31d82dedaeab02d9659/docs/part3-distribution/README.md).
That definition is a pending error conclusion, not a proved supplier.
The high physical-modulus signed prime-product estimate and the licensed
rough/smooth construction are still absent, and its new code is also
uncompiled. Its square-root prime BV and unweighted long-integer-slot
results cannot replace the required same-rho error theorem.

The second-round fixed Part 3 handoff is
[`64598da177adf861df3763d7c465ff941388b6d6`](https://github.com/UyNewNas/goldbach-formalization/blob/64598da177adf861df3763d7c465ff941388b6d6/docs/part3-distribution/README.md),
README blob `c405fdca22a9c17993ced130fe1d02d578ee15c4`.
Its new current-lower-band candidate still has a full below-half physical
modulus condition. The high physical-modulus signed prime-product estimate
and full actual-policy insertion remain open. `UniformPrimeProductTarget`
is still a target definition, not a proof of the required error bound.

For its eventual exact-source adapter, fix one `delta` first and pass
`Q delta` and `rho delta` together. Use two labelled prime slots with the
literal gates `r <= q`, `T <= r*q`, `r*q <= N` and `q^b < r`. Ordered
factor uniqueness must identify its signed error with
`realPhysicalDistributionError`, including squares and with no division
by two. A proved smooth outer target instead needs the actual weighted
outer-source transfer described above; a pointwise sandwich does not
bound each sharp signed discrepancy separately.

The existing conditional counting theorem fixes `kappa` and
`sieveExponent` before `∀ delta > 0`. A supplier selecting either parameter
only after precision is fixed does not directly instantiate that theorem.
Within each precision all four inputs must use the identical parameters,
cutoff, support and final coefficient. The displayed `epsilonMax` interval
in the density assembler is not itself a geometric licence or a proof that
Part 3 works for the same chosen precision. If such additional dependence
appears in the actual supplier, it must be handled in the finite quantitative
application; no further conditional counting theorem was added this round.

### Part 4 to Part 5 and Part 0

**No unconditional current-K conclusion is handed to Part 5 in this
checkpoint.** Part 5 must not instantiate its upper-product cost from the
conditional limit or counting assemblers. After Parts 1 and 2 supply the
construction, full integral certificate and compilation budget, Part 4 can
apply these interfaces to the same final coefficient and forward the
result immediately, without waiting for the final bad-semiprime count.

The fixed Part 5 handoff
[`3b8ab5eb2041af1906ecdb108f5edd2dd61f19aa`](https://github.com/UyNewNas/goldbach-formalization/blob/3b8ab5eb2041af1906ecdb108f5edd2dd61f19aa/docs/CHEN_P5_HANDOFF.md),
blob `d4b95cf296c14d61132cd960df80be80e0c1b5bb`, confirms that Part 5
needs Part 4-A's actual weight, majorant, support, coefficient controls and
true K density. Its separate positive switched-family count also needs the
same-weight Part 3 estimate and marked-product masses. Part 5 does not
depend on Part 4-B. Neither the K number nor a RealB-specific conditional
bound supplies that general family estimate, and no `hLower` is used here.

Part 0 can integrate these independent modules when their actual proof
gates pass. The five-module verification target is intentionally independent
of the root import list, to avoid conflicting ownership of that list.

For this second round, Part 0 receives only the candidate-source identity,
failed-startup/nonexecution records, and precise outstanding interfaces.
Parts 1, 2 and 3 receive the carrier/reserve/parameter matching requirements
above. Part 5 receives a status update with **no usable K export yet**.
The selected next independent finite task is the common-carrier zero-extension
adapter described above, which directly serves Part 4-A's compiler transport.
Its finite ingredients are available, but the user's prerequisite that the
existing five modules first pass actual verification has not been met.
Consequently it is not implemented in this batch; no additional Lean
candidate or duplicate conditional assembly theorem is introduced.

## Verification scope

The local official Lean archive and all fixed dependencies were obtained
and checked, but Lean's `/proc/<pid>/exe` lookup is denied by this execution
environment. No runtime permission bypass or patched Lean is used.

The standalone `part4-upper.yml` workflow checks the exact source commit,
fixed pins, explicit module builds, strict individual source elaboration,
fresh bundled-kernel replay of all five modules, and every defining-module
declaration's safety and transitive axioms. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Full elaborated types,
including private/generated declarations, are retained with the run logs.
A failed, skipped, incomplete or only statically scanned run is not a
verified proof. Existing full-project checks remain independently visible.

### Observed attempts

- The complete local runner reached `lean-version.log` and failed with
  `error: failed to locate application`; its report status is `FAILED`.
- First candidate commit:
  `4befa13602117435a3a64dfca001c20bbbb7d4c2`.
  [Part 4 run 38193908304](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38193908304)
  failed with no jobs. The job-level cache path used a `runner` context
  where GitHub does not permit that context; the present workflow moves
  that assignment into the existing shell step through `GITHUB_ENV`.
- At the same first candidate commit, existing core run `38193909112` and
  variable-envelope run `38193909046` each failed with `steps = []` and
  `runner_id = 0`. No Lean log exists for those attempts. This is not
  evidence of either proof success or an elaboration error.
- Static checks passed: three frozen configuration hashes, all eleven
  dependency HEADs and source cleanliness, Python syntax, YAML parsing,
  five shell-block syntax checks and whitespace checks. All 303 baseline
  source blobs remain byte-for-byte identical.
- After the startup repair, commit
  `03fea836685ecbce838b9fa272b53b4212d6952f` generated
  [Part 4 job 114633685373](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38194363333/job/114633685373).
  It failed with `steps = []`, `runner_id = 0` and zero artifacts, just
  like the existing core and variable-envelope jobs. The workflow now
  parses, but no proof stage ran. The API available in this session does
  not expose the annotation text, so no billing, quota or other cause is
  asserted.
- A further local runner attempt at that same commit stopped at the
  ancestry check because the reconstructed local snapshot lacks the
  baseline's parent object. No verification gate was disabled. A separate
  invocation of the unchanged official `lean --version` still failed with
  `error: failed to locate application`. The hosted workflow requests a
  full-history checkout; it remains blocked before even that step runs.

Use the final handoff's fixed SHA and its own actual workflow result for
the latest attempt. The candidate source types below are copied from the
source; they are not an elaborated type inventory.

## Candidate key declaration types

All declarations are in namespace `ImbalancedChen`; `Filter` and
`Topology` are open. These are complete source signatures with every
hypothesis retained. They remain uncompiled candidates at this checkpoint.

### Exact density normalization

```lean
theorem density_le_manuscriptScale_iff_normalized {N : ℕ}
    (hN : 2 ≤ N) (density coefficient : ℝ) :
    density ≤ coefficient * (singularSeries N / Real.log (N : ℝ)) ↔
      density * Real.log (N : ℝ) / singularSeries N ≤ coefficient
```

### Exact main-term product

```lean
theorem same_rho_normalized_mainTerm (N : ℕ) (mass : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (mass * physicalDensitySum Q rho) / singularNormalization N =
      (mass * Real.log (N : ℝ) / (N : ℝ)) *
        (physicalDensitySum Q rho * Real.log (N : ℝ) / singularSeries N)
```

### A raw density cap that preserves the compiler reserve

```lean
theorem exists_actualSmallRoughRho_density_le_of_full_policy_limits
    (nu sieveR epsilonMax rawBound densityCap : ℝ)
    (hnu : 0 < nu) (hr : 0 < sieveR) (hepsilonMax : 0 < epsilonMax)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (integral : ℝ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * sieveR) ≤ (cap N : ℝ))
    (hIntegral : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR)))
          (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR))) *
          Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
        (𝓝 (integral epsilon)))
    (hCertificate : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      integral epsilon ≤ rawBound)
    (hgap : rawBound < densityCap) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ sieveR ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (nu * sieveR)
        let L := (N : ℝ) ^ (nu * epsilon)
        physicalDensitySum (actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
            (actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L) ≤
          densityCap * (singularSeries N / Real.log (N : ℝ))
```

### The currentK specialization for the raw attachment

```lean
theorem exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits
    (nu sieveR epsilonMax rawBound : ℝ)
    (hnu : 0 < nu) (hr : 0 < sieveR) (hepsilonMax : 0 < epsilonMax)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (integral : ℝ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * sieveR) ≤ (cap N : ℝ))
    (hIntegral : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR)))
          (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR))) *
          Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
        (𝓝 (integral epsilon)))
    (hCertificate : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      integral epsilon ≤ rawBound)
    (hgap : rawBound < currentK) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ sieveR ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (nu * sieveR)
        let L := (N : ℝ) ^ (nu * epsilon)
        physicalDensitySum (actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
            (actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L) ≤
          currentK * (singularSeries N / Real.log (N : ℝ))
```

### Transport to the compiled physical coefficient

```lean
theorem compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget
    {N : ℕ} (hN : 2 ≤ N) {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ) (M rawBound compilerReserve : ℝ)
    (hminus : |reciprocalTotientDensity small betaMinus| ≤ M)
    (hplus : |reciprocalTotientDensity small betaPlus| ≤ M)
    (hraw : physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough raw betaMinus betaPlus) ≤
      rawBound * (singularSeries N / Real.log (N : ℝ)))
    (hcompiler : M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) ≤
      compilerReserve * (singularSeries N / Real.log (N : ℝ)))
    (hbudget : rawBound + compilerReserve ≤ currentK) :
    physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough compiled betaMinus betaPlus) *
        Real.log (N : ℝ) / singularSeries N ≤ currentK
```

### Actual raw weight majorant

```lean
theorem actualSmallRoughRho_sieveProduct_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℕ) :
    (if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n
```

### Actual raw weight in the finite real count

```lean
theorem RealB_cast_le_actualSmallRoughRho_main_add_errors
    {b T : ℝ} (N cap : ℕ) (retainOdd : List ℕ → Bool) (w z L : ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    (RealB b N : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) *
        physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
          (actualSmallRoughRho retainOdd N cap w z L) +
      realPhysicalCoprimeCorrection b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) +
      realPhysicalDistributionError b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) + (Nat.ceil z : ℝ) + (T + 1)
```

### Conditional hUpper with the same precision-indexed weight

```lean
theorem eventually_RealB_le_currentK_log_of_same_rho_inputs
    {b kappa sieveExponent : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hsieve : sieveExponent < 1)
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (hmajor : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ sieveExponent)))
        then (1 : ℝ) else 0) ≤ physicalDivisorSum (Q delta N) (rho delta N) n)
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum (Q delta N) (rho delta N) ≤
        (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N)
    (hdistribution : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + epsilon) * singularNormalization N
```

## Additional finite component types checked against the source in round 2

These complete signatures are extracted from the unchanged five-module
source checkpoint `262f69822a386a9d44efc059bceba11049668d68`. They are in
namespace `ImbalancedChen`, with `BigOperators` available where needed.
They are source signatures, not Lean `#check`, `#print`, or a kernel receipt.
The round did not add these declarations; it made their existing hypotheses
explicit for the handoff.

### Exact attachment of the same Boolean policy

Source: `ImbalancedChen/ActualUpperPolicyDensity.lean`.

```lean
theorem actualSmallRoughRho_eq_firstExitAttachment
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z L : ℝ) :
    actualSmallRoughRho (retained false) N cap w z L =
      smallRoughRho (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli retained (roughPrimeUniverse N cap w z))
        (fun d => (firstExitRetainedCoefficient retained
          (roughPrimeUniverse N cap w z) d : ℝ))
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
```

### The actual policy polynomial is its reciprocal-totient density

Source: `ImbalancedChen/ActualUpperPolicyDensity.lean`.

```lean
theorem firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    firstExitRetainedPolynomial retained
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap w z) =
      reciprocalTotientDensity (fixedRoughSupport (retained false) N cap w z)
        (fixedRoughCoefficient (retained false) N cap w z)
```

### Absolute perturbation of the same physical density

Source: `ImbalancedChen/UpperCoefficientPerturbation.lean`.

```lean
theorem abs_physicalDensitySum_smallRoughRho_sub_le
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ) {M : ℝ}
    (hminus : |reciprocalTotientDensity small betaMinus| ≤ M)
    (hplus : |reciprocalTotientDensity small betaPlus| ≤ M) :
    |physicalDensitySum (smallRoughModuli small rough)
          (smallRoughRho small rough compiled betaMinus betaPlus) -
        physicalDensitySum (smallRoughModuli small rough)
          (smallRoughRho small rough raw betaMinus betaPlus)| ≤
      M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|)
```

### Compiled rough domination gives the same physical majorant

Source: `ImbalancedChen/UpperCoefficientPerturbation.lean`.

```lean
theorem actualAttachedRho_majorant_of_rough_domination
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ) (raw compiled : ℕ → ℝ)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (hraw : ∀ n : ℤ, actualIntervalRoughIndicator N w z n ≤
      supportedDivisorSum rough raw n.natAbs)
    (hdom : ∀ d ∈ rough, raw d ≤ compiled d)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ))
    (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough compiled
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) n.natAbs
```

### Exact decomposition of the same signed physical count

Source: `ImbalancedChen/RealPhysicalUpperWeightBridge.lean`.

```lean
theorem sum_rho_mul_realHalfProductCongruenceMass_eq
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d) =
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho
```

### The active-support gate for zero coprime correction

Source: `ImbalancedChen/RealPhysicalUpperWeightBridge.lean`.

```lean
theorem realPhysicalCoprimeCorrection_eq_zero_of_gate
    {b T : ℝ} {N z : ℕ} (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : 0 < b) (hT : 0 < T) (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hsupport : ∀ d ∈ Q, rho d ≠ 0 → d ∣ sieveProduct N z) :
    realPhysicalCoprimeCorrection b N T Q rho = 0
```

### Raw support divides the exact same strict sieve product

Source: `ImbalancedChen/RealPhysicalUpperWeightBridge.lean`.

```lean
theorem actualSmallRoughModuli_dvd_sieveProduct_ceil
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) {d : ℕ}
    (hd : d ∈ actualSmallRoughModuli retainOdd N cap w z) :
    d ∣ sieveProduct N (Nat.ceil z)
```
