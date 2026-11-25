# P3.5 continuous spectrum: accepted whole-height component

**The three modules below passed exact-commit strict compilation, bundled
kernel replay and the complete owned-declaration/type/transitive-axiom
gate. The full physical-family P3.5 `7/32` estimate remains open.**

## Acceptance and exact scope

| Item | Evidence |
| --- | --- |
| Mathematical commit | [`94cff537f2e60173aaf936c2345d5af0ee5e6585`](https://github.com/UyNewNas/goldbach-formalization/commit/94cff537f2e60173aaf936c2345d5af0ee5e6585) |
| Mathematical tree | `6e25b4118a5d08806da224876dfc230492bafb08` |
| Cloud service | P3, `Workspace Compile 27f68009` |
| Verification task | `cbcebb66105f4036a00789cc806ce176` |
| Verification group | `p35-continuous-height` |
| Compiler | Lean `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561` |
| Mathlib | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| Finished | 2026-11-25 17:49:05 Asia/Shanghai / 09:49:05 UTC |
| Complete owned inventory | 81 declarations: 72 theorems, including helpers, and 9 definitions |
| Allowed and observed transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Integrity checks | 51 source/configuration hashes and all 37 stage-log hashes match |
| Original evidence archive | 80,665 bytes; 46 members |
| Archive SHA-256 | `5dc72b2127e2cb7925692bc344c26288d5991f07e4ddfc626b064d0d56166c19` |

| Module | Source relation | Complete owned declarations |
| --- | --- | ---: |
| [`Part3RegularCumulativeShellPayment`](../../../../ImbalancedChen/Part3RegularCumulativeShellPayment.lean) | Recovered historical proof; compiler compatibility repairs | 46 |
| [`Part3RegularPositiveMeasureExhaustion`](../../../../ImbalancedChen/Part3RegularPositiveMeasureExhaustion.lean) | Recovered historical proof; compiler compatibility repairs | 31 |
| [`Part3ContinuousTraceExhaustion`](../../../../ImbalancedChen/Part3ContinuousTraceExhaustion.lean) | New consumer of those proofs and the accepted finite Cauchy core | 4 |

Each of the three owned modules was freshly compiled with
`-DwarningAsError=true` and checked with the pinned installation's
`leanchecker`. The generated audit enumerates serialized owned declarations,
including private and generated helpers, and records complete types and
transitive axioms. The final source and object hashes were checked again,
and the cloud worktree remained clean. The independent review also matched
the audit source byte-for-byte to the existing audit generator and rebuilt
the declaration inventory and theorem-type text from the raw audit log.

The final cloud gate took 337.474 seconds, with sampled peak aggregate RSS
8,365,068,288 bytes. It used one CPU thread and a 13,107 MiB task limit.
The initial two-thread ordinary build exceeded its smaller memory limit;
the accepted run uses the subsequent serial configuration. No failed build
is counted as acceptance.

## Mathematical result

For a finite cusp family, continuous complex rows `M_i(t)`, `S_i(t)` and
a continuous complex test `H(t)`, define

$$P(t)=\sum_i\frac{\overline{M_i(t)}S_i(t)}{\pi}.$$

The two energy hypotheses are separate. For every `T >= 1`, they bound
the integrals of `sum_i |M_i(t)|^2/pi` and
`sum_i |S_i(t)|^2/pi` on `[-T,T]` by `(T^2+u) A2` and
`(T^2+v) B2`. With `Y > 0` and nonnegative coefficient budgets, the test
has the low-height envelope

$$|H(t)|\le C\frac{1+|\log Y|}{1+Y}
\quad (|t|\le\max(1,2Y))$$

and the high-height envelope

$$|H(t)|\le C\bigl(|t|^{-5/2}+Y|t|^{-3}\bigr)
\quad (\max(1,2Y)\le|t|).$$

The new consumer proves global absolute integrability and

$$
\int_{\mathbb R}|H(t)P(t)|\,dt
\le516C\frac{1+|\log Y|}{1+Y}
\sqrt{\bigl((1+Y^2+u)A2\bigr)\bigl((1+Y^2+v)B2\bigr)}.
$$

Its three public theorems are:

1. `printed_trace_regular_integrable`: global integrability and the
   absolute-integral bound above.
2. `printed_trace_regular_integral_norm_le`: the same bound for the norm
   of the full complex integral.
3. `printed_trace_regular_integral_exhaustion`: for every `K >= 1`, the
   actual signed complex integrals over `[-4^j K,4^j K]` tend to the full
   integral.

The fourth owned declaration in this module is a private identification
of the generic height cut with `Icc (-T) T`. The conjugate stays on the
original left row, and each energy retains its `1/pi`. Local L2 membership
of the scalar square-root majorants is proved from continuity. Their
whole-line L1 property is established by the historical positive-measure
exhaustion theorem, then transferred to the actual pair by pointwise
Cauchy. Neither global L1 nor an absolute paired-trace estimate is a premise.

The constant 516 comes from the existing geometric-shell calculation:
the two tail ratios are `1/2` and `1/4`; the low-plus-tail coefficient is
bounded by 129, and comparison of the base-height pair budget contributes
at most 4. This realizes a regular-height implied constant in the manuscript;
it does not supply the later `7/32` exponent or the actual family inputs.

## Existing work preserved

The two historical proofs were copied from their exact registered donor
blobs before any repair. [SOURCE_REUSE.json](SOURCE_REUSE.json) retains
the donor paths, hashes and all compiler-diagnostic provenance;
[SOURCE_REPAIRS.patch](SOURCE_REPAIRS.patch) contains the exact complete
donor-to-accepted-source changes. The repairs preserve the mathematical
hypotheses, bounds, endpoints and named proof parameters. Six pure set
helpers omit an unused measurable-space instance; no measurable-set or
integration premise was removed.

Seven intermediate suppliers, covering 378 historically accepted declarations,
are imported with unchanged source bytes. Their historical owned receipts
are bound in [HISTORICAL_REUSE.json](HISTORICAL_REUSE.json). The previous
continuous Cauchy core from `de24ecdd`, with 5 owned declarations, is also
unchanged. Missing compatible objects were ordinarily rebuilt as imports.
Those eight modules were not subjected to a second owned strict/replay
acceptance and are not counted among this increment's 81 declarations.

`SOURCE_REUSE.json` is the preflight manifest hashed by the successful
verification. Its pending status describes the submission stage. It is
retained unchanged so its recorded hash remains reproducible; the current
acceptance status is in [RECEIPT.json](RECEIPT.json) and the original
[report.json](report.json).

## Remaining P3.5 boundary

The [manuscript correspondence](MANUSCRIPT_BOUNDARY.md) locates this
component in the frozen 1106 manuscript's Appendix A.5 and the `dt/pi`
normalization of Appendix B, equation (104). Uniform estimates for the
actual original Bessel tests, the actual row suppliers, divisor payment,
the other spectral lanes, and the level/Fourier/six-scale sums must still
be connected before equations (96) and (97) yield the complete P3.5 target.

The earlier [actual-window adapter](../../../source-only/20261125-p35-continuous-trace/Part3OriginalGeometricWindowEnergy.lean)
remains source-only. Six historically registered source files could not be
recovered from the checked source trees, objects and archives. A new check
of the restored P3 cloud's 27,462 local Git objects, including unreachable
objects, found no match to their registered byte sizes and hashes. The
other checked cloud Git database contained six objects and no match.
[CLOUD_SOURCE_RECOVERY.json](CLOUD_SOURCE_RECOVERY.json) preserves the exact
bounded result. P1 and P2 had active jobs and queued work when inspected;
their cloud files and object stores were not searched in this continuation.
No universal claim of absence is made.

The six registered files are listed with their hashes in the existing
[actual-row reuse manifest](../../../source-only/20261125-p35-continuous-trace/REUSE.json).
They have not been replaced with duplicate implementations. No new proof
of ABL, Kim–Sarnak, Pascadi or another external theorem was introduced.
No substantive contradiction in the manuscript was established. The full
P3.5 parent node is not promoted to completed status by this receipt.

## Retained verification evidence

- [RECEIPT.json](RECEIPT.json): acceptance scope, exact source/object identity
  and retained-file digests.
- [report.json](report.json): original verifier report.
- [declarations.json](declarations.json) and
  [theorem-types.txt](theorem-types.txt): all owned declarations and full types.
- [axioms.log](axioms.log) and [Part3ContinuationAudit.lean](Part3ContinuationAudit.lean):
  raw complete audit and the exact generated audit source.
- Three `*-strict.log` and three `*-replay.log` files beside this README.
- [CLOUD_TASKS.json](CLOUD_TASKS.json): actual task commands, exit statuses,
  timings and sampled resource measurements.
- [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md): mathematical, implementation
  and exact-receipt review.
- [Original cloud evidence ZIP](p35-height-94cff537-cbcebb66105f4036a00789cc806ce176.zip):
  every original verification-stage log plus the ordinary build and bounded
  source-recovery record.

The receipt follow-up changes documentation and evidence only. The accepted
Lean sources, reuse manifests, verification code and pinned configuration
remain byte-identical to mathematical commit `94cff537`.
