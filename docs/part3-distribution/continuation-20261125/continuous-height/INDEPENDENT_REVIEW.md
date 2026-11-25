# P3.5 whole-height continuous trace — independent source pre-review

**Specification PASS. Mathematical and implementation pre-review PASS.** I found no mathematical blocker in the new bridge or the two historical height-payment sources. Formal verification of the three owned targets remains pending at the time of this review. I reviewed the plan and the local Lean text without compiling, calling cloud services, or re-auditing the historical dependency receipts.

| Reviewed module | Source SHA-256 |
|---|---|
| `Part3ContinuousTraceExhaustion` | `84025a6b34f77e919a9148bf87ded3fb38e5e93ec1125b6cd7264e12c3ed7bdd` |
| `Part3RegularCumulativeShellPayment` | `f20f597f6eff9be4814c58eb1ecc2aca6c03aaf443761c1333b198947956471e` |
| `Part3RegularPositiveMeasureExhaustion` | `9cee631c6bdfd388c1d3987b16a495e2550cd94d2912d3a20cbe2eefd62e5d71` |

- The literal integrand is the bounded-at-low-heights, decaying-at-high-heights complex test times the original `sum (star left * right / π)`. Both nonnegative energies have one `1/π` inside the cusp sum. Their square roots supply the two scalar rows of the historical positive-measure theorem. Its conjugation on the second scalar row is harmless because both are nonnegative real values embedded in ℂ. The dominance uses the accepted pointwise finite Cauchy theorem and does not conjugate the original right row.
- The energy hypotheses involve only one row at a time on every `Icc (-T) T` with `T ≥ 1`. The two test envelopes refer only to `‖test t‖`. Continuity on compact intervals gives actual local L² membership of the majorant rows; the norms squared equal the literal energies. No absolute pair bound, bilinear large-sieve bound, global L¹, or convergence is assumed.
- The historical shell `(4^j K, 4^(j+1) K]` and the initial closed cut account for the endpoints exactly, for absolute height on both sides of the real axis. With `K = max 1 (2Y)`, budget growth `16(4^j)²` leaves summable ratios `1/2` and `1/4` under the two test tails. Their sums give `32/(K²√K) + (64/3)Y/K³`. This is bounded by `128/(1+Y)`; adding the low envelope gives the factor 129. Scaling the pair budget to `1+Y²` gives at most 4, hence the stated absolute constant `516 = 129 × 4`.
- Monotone exhaustion of the nonnegative extended integral of the majorant yields global L¹ before taking the full norm integral. The bridge then obtains global integrability of the actual pair by domination, bounds its integral of norms, and passes to the norm of its complex integral by the integral triangle inequality. Finally the increasing measurable intervals `[-4^j K,4^j K]` for any `K ≥ 1` exhaust ℝ. The limit is of actual signed complex cutoff integrals. Only convergence along this geometric sequence is stated, with no claimed common rate.
- Empty finite cusp types, empty shells, zero coefficient budgets, and `C = 0` create no division by a norm or budget. Height zero belongs to the low cut. High-tail denominators have positive base. `Y = 0` is outside the theorem's stated domain.
- The bound is uniform in cutoff height for the supplied constants. To apply it uniformly over the actual original physical family, the corresponding primitive energies and both test envelopes must be furnished with the required parameter dependence. The three stages of this argument do not provide those family estimates or the full `7/32` return. The earlier Y04 actual-row adapter remains source-only. No forbidden proof escape appeared in the three inspected source texts.

## Compatibility patch review, relative to `fa96aa2a5990ff998868d59d10e359c9e2e14bb8`

Reviewed working-source SHA-256 values `62a297f22d9fa2bec97f66f6302926d7f0e1e322aa4a001d048cb43b583a1ab3` (shell) and `8068286168a01ee1d06d749511a6cf6ecacf2e73efa8da1365893252965bca4c` (positive measure). The bridge still has the SHA in the table above.

**Mathematical semantics PASS. Formal implementation acceptance pending.** The shell patch separates the two `convert`/`norm_num` steps for the finite geometric series. The positive-measure patch omits an unused measurable-space instance only around six set-theoretic lemmas. All actual measurable-set, integration and convergence premises remain. The explicit nonnegativity proofs use the existing `pairBudget_nonneg`; addition monotonicity retains the same left summand. Dropping a trailing `ring` requires `field_simp` itself to discharge the same algebraic goal. None of these edits weakens a hypothesis on the spectral integrand, introduces an assumption, or alters the bound or the endpoint conventions.

One source API detail: the public `integral_pair_budget` proof argument `hMB` is renamed `_hMB`. Its type, position and mathematical force are unchanged. A caller using `(hMB := ...)` by name would need the new name. The only caller found in the current project files passes it positionally. Keeping the historical name would preserve named-argument compatibility as well.

The two donor-line elaboration failures remain open in this reviewed patch: donor line 125 (working line 131), identifying the product of pointwise norms in the local L² argument; donor line 280 (working line 286), specializing a proved restricted-measure `Integrable` witness to the base cutoff `IntegrableOn`. Both have the intended mathematical content. Their Lean definitional equalities have not been established by this review. Neither the positive-measure target nor its dependent bridge receives a passing formal verdict here.

The bridge applies `regular_R1_integrable` only to `test`, `A = sqrt L`, `B = sqrt R`, with the nonnegative roots embedded in ℂ. Its right-hand conjugation occurs solely in this scalar majorant. Pointwise finite Cauchy controls the norm of the literal left-conjugated pair by the norm of that majorant, and `.mono'` transfers integrability in the correct direction. Its absolute-integral bound follows by monotonicity. No new identity between the two complex integrands, or assumption bounding the paired trace, is used.

## Final source repair review at `94cff537f2e60173aaf936c2345d5af0ee5e6585`

The checked shell SHA-256 is `11746212f542a0fe085ffc59e802da1c1fd04a62aed782cdb6a4a3a9544ddca0`; the positive-measure SHA-256 is `d1d8e4f659206da1784c7f80fa421d39c8e5c0ee0539f892a53d8d8eae1df93f`; the bridge SHA-256 remains `84025a6b34f77e919a9148bf87ded3fb38e5e93ec1125b6cd7264e12c3ed7bdd`.

**Compatibility and mathematical review PASS.** The public `integral_pair_budget` has its original `hMB` argument name and type again. The proof applies monotonicity of the square root to this hypothesis to obtain `0 ≤ sqrt MB`, then uses that sign for multiplication on the right. The other factor is bounded separately by monotonicity on the left. The resulting bound is the original one.

At donor line 125 the proof supplies `hA2.norm.integrable_mul hB2.norm` directly for the desired product of norms. At donor line 280 it simplifies exactly `4^0*K = K` and supplies the already proved restricted-measure witness `hli`. Both changes reuse the available proofs with their original hypotheses. The `omit` before the docstring, geometric-sum tactic sequencing and corrected module overviews preserve the mathematical statements. The positive-measure overview now describes the actual bridge specialization to Lebesgue measure and the two cusp-summed `1/π` energies. No further source issue is open from the prior compatibility review.

The coordinating agent reported ordinary compilations plus strict compilation and bundled kernel replay for all three modules. The complete owned declaration/transitive-axiom audit and its archived receipt had not been independently checked at this stage. I did not compile. Full P3.5 and application to the actual uniformly bounded physical family remain outside this source verdict.

## Final exact-commit verification receipt

**Formal acceptance confirmed for the three owned modules at `94cff537f2e60173aaf936c2345d5af0ee5e6585`.** I independently checked the archived P3 task `cbcebb66105f4036a00789cc806ce176` without rerunning Lean. The original ZIP contains 80,665 bytes with SHA-256 `5dc72b2127e2cb7925692bc344c26288d5991f07e4ddfc626b064d0d56166c19`. All 46 members passed ZIP integrity and matched the extraction byte for byte. The key files copied into the evidence directory match the corresponding archive members. The 51 recorded source/configuration SHA-256 values match both Git objects at the stated commit and the files checked locally.

All 37 recorded stages matched their log hashes and command headers and exited zero. Each of the three strict compiler commands targeted the expected source with `-DwarningAsError=true`, emitted an object hash, and each bundled `leanchecker --verbose` log explicitly records replay of its matching module. The report and head log bind the run to the reviewed proof commit. The audit command exited zero. The archived generated audit equals `render_audit` for precisely these three modules, byte for byte (SHA-256 `c8d757e74d9ed75d10eba47ceb74516fea2cd5e36feab2e2b15c5ae95bde8c3b`). Its comparison of serialized constants against the defining-module inventory prevents omission of private and generated declarations.

The 81 unique records parsed from the raw audit output match `declarations.json` and its module count rows. All records have complete types. The 72 theorem entries regenerate `theorem-types.txt` byte for byte; the remaining nine definitions have their types and axioms in `declarations.json`. The union of all transitive dependencies on axioms is exactly `propext`, `Classical.choice`, and `Quot.sound`. The audit rejects unsafe or axiom declarations. A separate scan of the three owned source files with comments and strings elided found no `sorry`, `admit`, new `axiom`, `unsafe`, `partial`, `native_decide`, or kernel-check bypass token.

| Owned module | Count |
|---|---:|
| `Part3RegularCumulativeShellPayment` | 46 |
| `Part3RegularPositiveMeasureExhaustion` | 31 |
| `Part3ContinuousTraceExhaustion` | 4 |

The bridge's four are the three public results `printed_trace_regular_integrable`, `printed_trace_regular_integral_norm_le`, and `printed_trace_regular_integral_exhaustion`, plus the private helper `spectralCut_id_eq_Icc`. The seven historical supplier modules (378 prior declarations) and the earlier continuous Cauchy core (five prior declarations) receive no new credit in the 81. The evidence manifest `SOURCE_REUSE.json` carries the preflight `PENDING` text from the verified proof commit; its bytes are among the verified hashes. The later `PASSED` execution receipt supplies the final result for this scope and preserves the preflight record. The original-data adapter remains source-only and the full physical `7/32` estimate remains open.
