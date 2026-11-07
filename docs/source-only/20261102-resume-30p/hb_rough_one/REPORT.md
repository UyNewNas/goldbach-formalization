# P / hb_rough_one: recovered primitive-count supplier; reuse only

The alleged missing source `ImbalancedChen.P5OriginalPrimitiveCoprimeDensity` **already exists** in the frozen local source-review archive. Its intended production module path is absent, which is a materialization/import-resolution issue. Reconstructing its mathematics would duplicate a complete existing source candidate. This packet adds **no new proof or declaration** and does not rewrite O's rough-one, Brun, or rate proofs. At the root's explicit publication instruction it packages **13 exact-byte copies** of necessary historical dependencies under `dependencies/`, each marked `reuse_only=true`.

The focused source/provenance audit is complete. The broad node `P3.6.same_rho_PP` and formal acceptance of the rough-one supplier remain **OPEN**: `task_complete=false`, `compiled=false`, `kernel_verified=false`, `formal_credit=0`. None of the archived sources is promoted from its held status by this report.

## Located source and exact use

The source is:

`.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-OneLong-Phase3/P5OriginalPrimitiveCoprimeDensity.lean`

Raw SHA256: `ce150fc832dd286323d0cb980fd95186d745e0f0f84bc9952e3a1e567176f2be`. This matches both the same directory's `REGISTRY-CORE.json` and the dependency guard in `REGISTRY-FINAL.json`. The original registry specifies `UNCOMPILED_ZERO_CREDIT`, `ready_to_install=false`, and the intended target `ImbalancedChen/P5OriginalPrimitiveCoprimeDensity.lean`. It is local 2026-10-28 source, not a newly found upstream theorem. Search must include hidden/ignored archives, for example `rg --files --hidden --no-ignore`.

Its actual declarations include:

| Declaration | Line | Exact premise/result used in the audit |
| --- | ---: | --- |
| `coprime_indicator_moebius` | 32 | `q>0`; finite Mobius expansion of the literal coprime indicator. |
| `multiples` | 48 | Actual count of `d`-multiples in `Ico A B`. |
| `quotient_length_abs_error` | 57 | `A<=B`, `d>0`; ceil-endpoint length error at most 1. |
| `multiples_abs_error` | 82 | Same conditions; actual multiples count differs from `(B-A)/d` by at most 1. |
| `primitive_coprime_density_error` | 138 | `A<=B`, `q>0`; coprime count differs from `(B-A)*phi(q)/q` by at most `tau(q)`. |
| `primitiveCoprimeDensity_two_tau` | 166 | `q>0`; supplies the archived Phase2 density interface with safe error `2*tau(q)`. |

O does **not** convert the last theorem's `2*tau(q)` bound into `3*phi(q)`. O `P5ActualHBRoughBrunFinite.lean:123` instead uses the already proved production `part3IntervalAPCount_coprimeMean_error` with comparison residue zero, then the archived `multiples_abs_error`. Thus

`|coprimeCount/phi(q) - length/q| <= 2+1 = 3`.

The production theorem permits **every** comparison residue; zero need not be primitive. O multiplies this result by positive `phi(q)` at line 145 and obtains `PrimitiveCoprimeDensity q (3*phi(q))` directly. No estimate of `tau(q)/phi(q)`, new density assumption, or rough/Brun target premise is needed. O then bounds `meanError(q,3*phi(q))=1/q+3` by 4 for `q>0`.

## Recovered dependency chain

All paths and direct imports are machine-readable in `REGISTRY.json`. The essential recovered sources are:

| Intended module suffix | Existing source location | Raw SHA256 |
| --- | --- | --- |
| `P5OriginalOneLongDivisorIntervals` | `.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-OneLong-Phase2/` | `18fc887d1883102b4d5d176b3b1276c106f284fa09ee5b5ee599672aae064cba` |
| `P5OriginalOneLongSharpBrun` | Same Phase2 directory | `baf38607046c3dac86ce7a54c384cc17034e9cd4789b8bf2f7cbf585764a7b89` |
| `P5OriginalPrimitiveCoprimeDensity` | Phase3 directory above | `ce150fc832dd286323d0cb980fd95186d745e0f0f84bc9952e3a1e567176f2be` |
| `P5OriginalOneLongE5FiniteBudget` | Same Phase3 directory | `54ecdef1b7dce276ba9634f2e2e564d1ed244336b133a90a894c2e82e3bc26e8` |
| `P5OriginalOneLongLiteralBrunDictionary` | Phase4 archive and existing content-addressed `docs/source-only/20261028-paper-first/cohort04/primeproducts/sources/` copy | `7c29cea39c2dd7be4bed5623905c4d70f272950093793c9b365107bfe3d13c2e` |
| `P5OriginalOneLongExplicitBrunRates` | Same Phase4 archive and existing content-addressed paper-first copy | `f2ff5f06191c3f3bbc974702c444f10f83f47542474c653b651bcc28553f8ecb` |

The Phase2 interval file defines `PrimitiveCoprimeDensity` at line 170 and `meanError` at line 175. It proves `divisorRemainder_abs_le_two` at line 94 by reindexing the original interval with ceil endpoints and using the production long-slot discrepancy. Its lines 186 and 219 prove the exact-mean and AP atom upper bounds with explicit density error. Phase2 `SharpBrun` supplies the atom identities and exact compatible density sum; O passes its newly derived `3*phi(q)` density proof into the Phase2 bounds. Consequently the Phase2 interface is not left as an assumed Brun estimate in O.

Production `ImbalancedChen/Part3LongSlotDistribution.lean`, SHA256 `67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`, contains `part3IntervalAPCount_abs_sub_le_two:75`, `part3IntervalAPCount_coprimeMean_error:116`, and `part3LongSlotRemainder_abs_le_two:173`. Their written proofs retain the exact coprime count and primitive moving product residue. No production source was modified.

The Phase4 literal dictionary copies are byte-identical by SHA256; the Phase4 explicit-rate copies are likewise byte-identical. These archived modules and the O modules are different, complementary sources: Phase4 supplies finite literal B1/B2 and a scalar factorial inequality, while O supplies the actual real chart cutoff, uniform `3*phi(q)` mean budget, and the actual rough-one prefix result. They must not be counted as new P proofs.

## Exact-byte publication payload

The root reported a GitHub directory-API 404 for the Phase3 archive at the current public baseline and asked for the necessary unpublished source bytes to accompany this delivery. The root-supplied read-only `publication-durable-20261102T064559Z/payload/docs/source-only/20261102-go-takeover/{SOURCE_MANIFEST.json,DEPENDENCIES.json}` was inspected. It packages the Phase4 literal dictionary and explicit rates, but records the primitive-density and divisor-axis imports as unresolved. This packet does not edit that old manifest or claim that a remote publication has occurred.

The new `dependencies/` files, all copied without changing one byte, are:

| File stem | Original archive directory suffix |
| --- | --- |
| `P5OriginalOneLongFiniteBrunReduction` | `20261028-PrimeProducts-OneLong-Finite` |
| `P5OriginalOneLongDivisorIntervals` | `20261028-PrimeProducts-OneLong-Phase2` |
| `P5OriginalOneLongSharpBrun` | `20261028-PrimeProducts-OneLong-Phase2` |
| `P5OriginalPrimitiveCoprimeDensity` | `20261028-PrimeProducts-OneLong-Phase3` |
| `P5OriginalOneLongSmoothAbel` | `20261028-PrimeProducts-OneLong-Phase3` |
| `P5OriginalOneLongModulusMeans` | `20261028-PrimeProducts-OneLong-Phase3` |
| `P5OriginalOneLongE5FiniteBudget` | `20261028-PrimeProducts-OneLong-Phase3` |
| `P5OriginalOneLongSupportAbsorption` | `20261028-PrimeProducts-OneLong-Phase3` |
| `Part3TwoLongBrunComplexGap` | `20261028-PrimeProducts-TwoLong-Fallback` |
| `Part3TwoLongActualBrunProfile` | `20261028-PrimeProducts-TwoLong-Phase2` |
| `Part3TwoLongBrunLiteralDensity` | `20261028-PrimeProducts-TwoLong-Phase3` |
| `Part3TwoLongDivisorAxisClosure` | `20261028-PrimeProducts-TwoLong-Phase4` |
| `Part3BrunFactorialRecurrenceE1` | `20261028-PrimeProducts-TwoLong-Phase5` |

Each suffix is under `.lake/proof-continuation/source-reviews/drafts/`; each file has extension `.lean` and intended module `ImbalancedChen.<file stem>`. The copies total **108334 bytes**. `REGISTRY.json` records the original and delivery paths, raw SHA256, byte count, direct imports, existing declaration anchors, and byte-identity result separately for all 13 files.

The Phase4 dictionary imports the complete E5 module, so its literal import closure includes the existing smooth-Abel and modulus-mean files even though O uses only selected finite declarations. The shared literal B1/B2 imports also require the five TwoLong history files. These imports are retained exactly; no unrelated theorem was newly authored or silently removed to shrink the payload.

Three further historical modules already have exact content-addressed copies in `docs/source-only/20261028-paper-first/` and are **not duplicated**: `P5OriginalOneLongLiteralBrunDictionary`, `P5OriginalOneLongExplicitBrunRates`, and `Part3BrunSymmetricPairCount` (SHA256 `6bb80b6b89463c2e7f2fb56806e12c2946fc3b5e879660e874635613148c902c`, under `cohort03/primeproducts/sources/<sha>/`). The registry resolves all **18 direct project-import edges among these 16 archive modules and their production leaves**. This focused graph stops at the production `Part3LongSlotDistribution` and `BoundaryArbitraryLog` modules and at external Mathlib/MathlibNt imports. It is a source-location closure, not an installed-module or kernel closure. In particular, historical comments saying the B2 pair count is open are preserved verbatim; the separately existing `Part3BrunSymmetricPairCount` source is the later supplier, not an excuse to edit those comments here.

## O audit and unchanged obligations

All three O files were read. Their frozen hashes are:

| O file | SHA256 |
| --- | --- |
| `P5ActualHBRoughBrunFinite.lean` | `cb264cc04c1be342b105ade628a5fbbc81749fe2da53696a7d184d4562dd2e6b` |
| `P5ActualHBRoughBrunRates.lean` | `3da0ddce4183f258d974454c67188d3ff47ae240848afc05455ab3214416ef1b` |
| `P5ActualHBRoughOnePrefix.lean` | `031eb4ebc88715880d127796429188bc1f988ed0160e619b97c4b6d21dc58b0c` |

The focused manual audit found no substantive error requiring a replacement of these three sources. The finite expression keeps the positive comparison gap and exact coprime mean; it does not multiply a negative lower polynomial as positive. The signed comparison retains computed divisor atoms, and the rough-one specialization bounds those atoms using the existing interval theorem. The rates use `z=x^(1/(loglog x)^3)` and next order `2*floor((loglog x)^2)+1`. The final prefix statement chooses the threshold before `U,u,v,q,b`, retains the literal floor endpoints, and requires `xi>0`, `x^xi<=U`, `U<=u<=v<=2U`, `q>0`, and primitive `b`.

O's written endpoint is `prefixNorm(roughOneSlot(roughZ x)) <= 16*U/(log x)^A`; its source does not assume that estimate. This report recognizes that existing proof body and adds no wrapper for it. M's `actual_prefixNorm_le_base` and `eventually_chart_dominates_logPower`, and the production rough-slot/large-modulus declarations named in `PRIOR_TASK.json`, were also inspected as existing reuse sources. The Mobius supplier, complete auxiliary/profile/chart assembly, and all-rank same-rho PP are outside this narrow recovered dependency and remain open here.

The genuinely removed obligations are **source discovery and provenance uncertainty** for the named primitive module and the **publication-copy omission** for the 13 necessary historical dependencies in the stated graph. P discharges no new mathematical theorem. What remains is exact source materialization under the declared modules, held-import resolution, and subsequent elaboration/kernel review. The full transitive Mathlib/goldbach import closure, including the Mertens package source used by O's rates, was not freshly certified by this packet; locating and copying the elementary archive cannot certify that closure.

## Manuscript and difficulty classification

The original current manuscript was read at lines **138-175 and 323-355**, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Those lines require actual chart-rough one/Mobius slots and exact auxiliary coprime means; they do not license arbitrary rough coefficients. The completion source was read at **185-207, 218-248 and 298-306**, SHA256 `a953b3233c1249b4791830da33b76a58b19ca110a5e1b5b6172b3248a00053e1`: these are the actual rough-SW derivation, literal Brun weights and exact mean arithmetic used here.

1. **Lean expression/API and integration gap:** confirmed for unmaterialized archive module paths; complete transitive import/elaboration validation remains open. No new particular proof-script error is asserted merely because compilation was forbidden.
2. **Fillable omitted deduction:** no new missing elementary deduction was found in this focused scope. Both the primitive count proof and O's uniform normalized-mean deduction already have source bodies.
3. **Possible substantive manuscript gap:** none established for this recovered count/Brun link. This is not a conclusion about the separate Mobius route or the full PP argument.

Checks were limited to reading source and provenance, text searches (including hidden archives), declaration/import inventories, path existence, the bounded source-location graph, raw-byte SHA256 and source/copy byte comparisons, and JSON metadata validation. No Lean/lake/compiler, Git operation, CI, proof-guard evaluation, numerical replay, production installation, old-file modification, or sub-agent was used. Every existing finite guard remains **UNEVALUATED**.
