# t30 independent review: enhanced switched mass and terminal suppliers

Status: **HOLD** for the enhanced arithmetic mass target and for P5.6, P4B.4, P6.3. **PASS** below means a narrowly delimited static source review only. No Lean/lake/compiler, numerical replay, finite proof guard, Git operation, or author-file edit was performed. No green node is justified. New/staged code remains `compiled=false`, `kernel_verified=false`, formal credit 0.

Review scope: O/P `enhanced_switch_mass` (t20), manuscript lines 795–970 and 1436–1535, and the actual downstream theorem signatures. This is the final independent static review of the three P Lean candidates and the REPORT/REGISTRY snapshot hashed below. Their frozen source hashes matched the author's stable handoff.

## PASS — exact O finite and algebraic obligations

Paths in this section are relative to `docs/source-only/20261102-resume-30o/enhanced_switch_mass/`.

- `P2EnhancedSwitchedUnsiftedSource.lean:23–25,69–123,167–188,247–304`: the old-mask rough carrier explicitly has `Sifted (d*N) m z`. The count comparisons go in the safe upper-bound direction after removing receiver primality. `4≤N` and `Even N` remove the zero complement by ruling out the prime receiver `ell=N`; no positive quotient is silently assumed. The original selected-prime collision term is retained at lines 180–188.
- `P2EnhancedSwitchedUnsiftedSource.lean:127–163,198–234`: labels use the original half-open prime windows, strict ordered lists, original colour words, and common physical `Q`. The literal 20 occurrences retain the two appearances of each of `112` and `122`. `Gamma20` has word `[2,3,3,3,3]`; `Gamma21` has `[3,3,3,3,3,3]`. Their unit and nonunit parts remain four separate weighted summands. `unitWordMass_eq_product_count` is a finite exact count, not a surface-integral limit.
- `P2EnhancedSwitchedUnsiftedSource.lean:238–312`: bad Gamma5 uses the inherited `a0` cutoff, and the bad square gate includes equality (`Q≤d*p^2*q`). The exact good/bad partition does not create ordinary feedback on the bad part. This respects manuscript 844–855.
- `P2EnhancedSwitchedTrueNormalization.lean:25–72`: `trueAlpha` is exactly `log(N/d)/log(Q/d)`, and at `Q=N^nu` equals `(1-log_N d)/(nu-log_N d)`. With positive residual exponent, `alpha≥2` is equivalent to `2*nu≤1+log_N d`. The source does not replace alpha by 2 or assert that positive residual exponent alone proves this gate. Physical conservation remains at the same total Q.
- `P2EnhancedSwitchedTrueNormalization.lean:92–138`: the raw main atom `N/(d*log(Q/d))*F(alpha)` is converted algebraically into the exact true-li atom with `C(d*N)/phi(d)`. The multiplier is d-dependent. No total marked mass is divided out; the zero-weight identity is exact. This matches manuscript 795–806 and 877 as an algebraic interface, not an analytic supply.
- `P2EnhancedSwitchedTrueNormalization.lean:142–170`: Gamma20 uses its four-coordinate first-elimination chart, Gamma21 its five-coordinate last-elimination chart, both at the actual alpha. `enhanced_last_continuous_envelopes` invokes the continuous integral estimate only. Its supplier `ImbalancedChen/P2SeedOmegaLastFullMassBounds.lean:74–75,154–168` explicitly defines each full mass as nonunit plus its own unit integral. No arithmetic count limit follows from that theorem.

## PASS — genuine new P unit upper-mass supplier

Paths in this section are relative to `docs/source-only/20261102-resume-30p/enhanced_switch_mass/`.

- `P2EnhancedUnitSourceGeometry.lean:44–79,82–180` proves the needed inclusion from the actual unsifted product inequality, without inventing a prime receiver. The injection recovers the complete labelled list; it does not identify different lists by their product. Gamma20 retains five primes/four prefix coordinates and Gamma21 six primes/five prefix coordinates. The strict target-deleted source is bounded by the closed physical carrier, so only an upper mass is claimed.
- `P2EnhancedUnitSourceMass.lean:30–83` proves `(Q/d)^trueAlpha=N/d`, applies the actual native physical prime-fibre supplier, and derives `actual_unit_upper_uniform` for both O `unitWordMass` definitions. The threshold is before N, Q and d. Its remaining primitive conditions are `eta>0`, `epsilon>0`, `d>0` and `N^eta≤Q/d`. It does not assume a unit mass or count estimate.
- This use was checked against the actual native source, not inferred from a declaration name: `SecondFunctionalHighUnitLimit.lean:43–59` quantifies `∃T>1, ∀R≥T, ∀a2 a3 b phi`; its only exponent-window conditions are `a2,a3≥1/10` and `b≤1/2`. Phi is unrestricted. `SecondFunctionalHighUnitBoxedLimit.lean:59–72` unnormalizes an arbitrary R. Thus this route does **not** reuse the classical-Q `boxed_pair_uniform` or `actual_unit_counts_receiver` at a new Q. Not requiring alpha≥2 in this isolated unit theorem is justified by the stronger all-phi native input.
- `P2EnhancedUnitSourceMass.lean:105–156` lifts the two raw upper masses with the actual original nonnegative sigma, d-dependent `thetaConversion`, true-li atom and common Q. Each surface receives epsilon/2, then their combined error is epsilon times Theta. `convertedUnit20/21` are explicitly defined converted raw masses, not a statement that the same-rho PP density equals that conversion. `zero_theta_units:160–176` proves the zero-Theta case exactly through positivity and zero weights; it never divides by a source mass.
- The exact chart identification was also inspected: `ImbalancedChen/P2SeedOmegaUnitChartIdentification.lean:46–52,89–129` uses the affine cyclic rotation for Gamma20 and the unchanged last-coordinate chart for Gamma21. Both use the same real alpha. Consequently the new arithmetic source upper bounds reach the manuscript's two separate unit surfaces, not merely unrelated continuous caps.

## PASS — precise receiver purification and per-tuple Buchstab source

`P2EnhancedReceiverRoughPurification.lean` is a new route while receiver primality is still available; it does not silently replace O's larger masked raw carrier.

- Lines 28–46 define `roughReceiver`, exact `repeatReceiver` (`¬d.Coprime quotient`) and exact `centerReceiver` (`¬quotient.Coprime N`), then prove ordinary roughness from the two coprimality conditions. Lines 48–99 provide a cover and an injective comparison to the actual inclusive `roughNumbers` carrier.
- Lines 103–144 prove `centerReceiver⊆N.primeFactors` and the repeat bound `Σ p∈D.primeFactors, N/(D*p)` at the complete divisor D, with `d∣D` explicit. The wider event `ell∣N` is used only as an upper bound; it is not identified with the exact bad quotient event. Lines 147–160 prove that neither exact exception contains quotient one. The bounds remain inequalities; no disjointness of all three cover sets is invented.
- `receiver_buchstab_upper:173–195` applies native `InclusiveRoughUniform.uniform_upper:53–69` at `x=N/D`, before moving d,D,z. It retains the separate unmultiplied unit indicator and the closed gate `z≤N/D`. `physical_buchstab_argument:199–213` is exactly `(alpha-log(l.prod)/log(Q/d))/(log(z)/log(Q/d))`, not an alpha=2 specialization.
- `quotient_word_upper:229–247` and `original_word_upper:251–260` bind the new comparison to the original labelled occurrences and preserve the additional selected-prime collision. `original_badPair_upper:283–293` binds the excluded Gamma5 part to its original ordered labels, equality-inclusive bad-square gate and inherited a0 cutoff. These are finite original-source comparisons; they are not the Gamma5/Gamma9–21 aggregate mass theorem or a K/4 estimate.

## HOLD — remaining enhanced aggregate source and exceptional payment

The old mask in O is not ordinary roughness: a prime dividing d or N is exempt from `Sifted (d*N)`. Once receiver primality is removed, a quotient sharing such a prime is still counted by `roughCarrier`. A classical rough-number asymptotic cannot be applied to this larger carrier without an exact comparison and payment of the extra pieces. For an actual prime receiver, the divisibility relation `d*prod(l)*m=N-ell` implies that a prime dividing both m and N equals ell; primes dividing both m and d give a repeated-prefix/square event. The selected-prime collision already exposed by `ImbalancedChen/P2EnhancedPrefixMaskDefect.lean:69–106,119–145` is another retained source event, not an automatically negligible term.

The genuine unit upper masses and per-tuple inclusive Buchstab comparison are now supplied above. What remains for the broad enhanced target is the nonunit prime-sum/integral passage over the original words, including the bad Gamma5 piece, and uniform aggregate payment of the **new repeat/center** events relative to the original Theta. One must also bind the primitive cutoff, physical ceiling, alpha gate and old-prefix support conditions to the actual causal marked family. The new unit upper theorem needs no unnecessary bilateral source limit. The aggregate threshold must precede the moving d/actions/Q/positive weights; zero source mass cannot be used as a denominator.

**PASS — prior selected-collision payment is already coded and must be reused:** `ImbalancedChen/P2EnhancedCollisionThetaPayment.lean:50–90` proves `weightedCollisions≤epsilon*Theta` with threshold before Q,D,sigma, under `Q≤N`, positive d, nonnegative sigma, `1<Q/d`, and the explicit old-prefix/new-prime `N^eta` floors. It uses `P2EnhancedCollisionWeightedBudget.lean:163–186` and `P2EnhancedThetaReciprocalMass.lean:48–80`. It would be inaccurate to call this old selected-collision aggregation wholly missing. The remaining new repeat/center payment and actual-support instantiation are distinct obligations; arbitrary positive d alone does not imply its prime factors grow with N.

The classical theorems cannot be renamed into this supply. `ImbalancedChen/P2SeedOmegaSwitchedArithmeticFour.lean:95–103` has coefficient `2/(1-2*delta)`, level `N^(1/2-delta)`, and `wuSourceBox` premises. `ImbalancedChen/P2SeedOmegaActualUnitCountReceiver.lean:53–69` likewise has that classical Q and its original convolution boxes, with separate epsilon/2 unit errors. Neither is the enhanced K/4 licence.

## HOLD — same rho and downstream conclusions

- **P5.6**: `ImbalancedChen/P5OriginalFixedDensitySupplierAssembly.lean:171–202` explicitly requires all eight actual estimates `hstarts`, `h34`, `h5`, `h6`, `h7`, `h8`, `h9`, `h1011`. The exact grouping and constants are fixed at lines 39–60 and 91–116; they are not supplied by the enhanced finite source dictionary. The same source lists the analytic suppliers as still explicit/unproved at lines 169–170. In particular U7's source mass alone does not supply its actual-rho density/PP inputs (`P5U7OriginalSourceSuppliedRoute.lean:26–62,79–125`); U8 and U9 retain analogous policy/integral/PP premises (`P5zUpsilon8OriginalSlot.lean:180–234`, `P5zUpsilon9OriginalSlot.lean:97–152`). Broad P5.6 and its leaf “把八组真实供应闭合到同一原始实例” remain yellow.
- **P4B.4**: `ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean:28–55` explicitly requires `hdensity` and `hUniformPP`. Lines 40–52 use the same `attachedUpperModuli` and `attachedUpperCoefficient` in both hypotheses; the PP source is the actual rank-two smooth physical outer ramp. A Gamma arithmetic mass or a continuous omega cap proves neither hypothesis. The existing proof passes these two inputs at lines 113 and 128–130. The positive smoothing/coprime argument is already a local source chain; it must not be confused with the missing signed PP estimate. Manuscript 557–559 requires the same rho at each precision, while permitting different precision choices to use different rho; no stronger global fixed-rho premise is introduced here. Broad P4B.4 remains yellow.
- **P6.3**: `ImbalancedChen/P6OriginalEndpointAssembly.lean:19–39` retains hLower and hUpper, with hUpper quantified for every real `1/2<b<1`, and concludes the original common all-even threshold only conditionally. Manuscript 1451–1489 needs the actual ordered bad-source mass and PP before `K*log(1/b)`; 1493–1504 then subtracts this upper count from the actual lower count. The scalar margins at 1506–1534 cannot discharge either analytic estimate. Broad P6.3 remains yellow. No new final consumer is needed or added.

## PASS/HOLD — node recommendation

**PASS / local blue only:** exact labelled finite source comparisons and retained exception terms; separate Gamma20/21 unit partition **and their actual enhanced-Q upper masses**; true-alpha, true-li and same-Q positive-weight conversion with exact zero-mass treatment; receiver purification and its inclusive per-tuple Buchstab bound; and the original-word/bad-Gamma5 finite bindings. “Code coverage” includes the genuine native analytic supplier reused for the unit upper masses. It does not mean compiled or kernel checked.

Suggested precise Chinese blue line: **“Gamma20/21 两个独立 unit 的增强同Q上质量、true-alpha/true-li 正权规范化与零质量；prime receiver 净化到普通 rough 的逐词/坏Γ5有限比较，保留 repeat/center/collision 异常项。”**

Suggested remaining yellow line: **“Γ5及Γ9–21非unit聚合积分、repeat/center异常的同Θ支付与实际support/同rho PP许可。”** This does not relabel the already coded old selected-collision payment as missing.

**HOLD / broad yellow:** P2.9 bank analytic endpoint licence, the complete enhanced switched mass, P5.6's eight real suppliers on one original instance, P4B.4 actual-rho density plus uniform PP, and P6.3 removal of hLower/hUpper. Within t30's scope, none of those existing yellow leaves is now fully covered; the new blue entries describe smaller completed code obligations. This is a missing-supplier judgement, not a judgement based merely on `compiled=false`. P2.4 and its four leaves are outside this review and are reviewed by t23.

**HOLD — difficulty classification:** the corrected raw-unit/source mismatch and the masked-to-ordinary rough comparison were fillable omitted deductions (class 2); P supplies their concrete local code. Remaining nonunit aggregation, new exceptional payment, and actual causal/PP instantiation are substantive missing code obligations rather than API spelling alone. This review identifies no proof that the manuscript theorem itself is false (class 3 is not asserted). Static API repairs in the reviewed candidate do not amount to compiler validation.

## PASS — frozen evidence

SHA256 (static filesystem hash only):

| File | SHA256 |
|---|---|
| `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex` | `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` |
| O `P2EnhancedSwitchedUnsiftedSource.lean` | `0996a926dd43a4b017d21393c97ae51f5df47f9ebe8ec14fa7c4d190fc05ac91` |
| O `P2EnhancedSwitchedTrueNormalization.lean` | `1082e7e6ed3b23a9828aeb68cf2a2072a0b13e377799988825fb4fd8ebb1a11d` |
| P `P2EnhancedUnitSourceGeometry.lean` | `d6c31ec99a28e2cd4aa009c7776a1fb02e1f77d64add31da52b26979a8b84973` |
| P `P2EnhancedUnitSourceMass.lean` | `5aa59d6259ff4f3e530aa080223d13a392566704e6e66cc937e3ae2634c955ca` |
| P `P2EnhancedReceiverRoughPurification.lean` | `dfd047a5bc3d57f4ecee4078208f1de9fc777f9b6342a9cd4f72973dc1c075e6` |
| P `REPORT.md` | `7cad12c4b3215a983acda1cc8b304f92e7e1ac9f4c3cefedf3530196862cf59d` |
| P `REGISTRY.json` | `c33aec647ba3907ad99874dc2451d17c262f7ff5ae057eb4e5335f11b054d227` |
| `ImbalancedChen/P2SeedOmegaUnitChartIdentification.lean` | `286948938664d1e42323d7a0a221913656de6033d4b203644e96eee8700a3107` |
| `ImbalancedChen/P2EnhancedCollisionThetaPayment.lean` | `57e32fb7044442b6ebe68cef95a078a58f344b5eaf8bfd48ede34eea60f2049e` |
| `ImbalancedChen/P2EnhancedCollisionWeightedBudget.lean` | `60304cb46666459fca73b38d9090c02738fe5b3afcb6cb2d5c899cc31859a0c8` |
| `ImbalancedChen/P2EnhancedThetaReciprocalMass.lean` | `a1b6b5bc76c7724a5584cf71c18fc154559dffe457532d4481455a286243de1c` |
| `ImbalancedChen/P5OriginalFixedDensitySupplierAssembly.lean` | `716aa10228dfa7fefe8cd30bc0e878882d35bb0b14c355c229ff50d6bd4d5096` |
| `ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean` | `0eddc7dfde67bb42021e9f4176c1827e5a28966a5024f79930f1b59221304d59` |
| `ImbalancedChen/P6OriginalEndpointAssembly.lean` | `7c22fc14a97425b0c5b5a215c9655cc90b9464250f41c300da5845ceea7aebd0` |

Native source root actually read: `//wsl.localhost/Debian/home/slava/codex-lean-ve/native-packages/goldbach/research/wu2008/src/MathlibNt/Wu2008DoubleSieve/`.

| Native source | SHA256 |
|---|---|
| `SecondFunctionalHighUnitLimit.lean` | `acb888fc47cc52367c05da21b0c95e2cdd19b968ff3cc6acb8e458bcecdfbc9c` |
| `SecondFunctionalHighUnitBoxedLimit.lean` | `cf3451b3aa0898bde5f858bb66533468e02dd98887b6a36fffbfcbf470a102a4` |
| `SecondFunctionalHighUnitSourceGeometry.lean` | `d3a5251b8aa46b5506df199e7a1c412ad991fdb557abe8c1c7c16b19090f7bd7` |
| `InclusiveRoughUniform.lean` | `a0cc25326c20fcc9e26c69f57d267c02c55593cc617025ffc92ca8fe2e591896` |

**PASS** for the local static safety scan: no `axiom`, `sorry`, `admit`, `unsafe`, `implemented_by`, `native_decide`, `run_tac` or `#eval` token was found in the O/P enhanced Lean candidates. No new hLower/hUpper/hUniformPP or unconditional terminal theorem was introduced there. No guard or proof body was evaluated.

**PASS** for registry consistency: JSON parsed; all three Lean hashes, line counts (296/183/179), direct-import lists, intended install names and all 39 declaration line bindings matched the source. All 39 pinned entries across 31 unique paths matched their actual SHA256 values. All three new files explicitly retain `compiled=false`, `kernel_verified=false`, formal credit 0. The author's REPORT correctly distinguishes true unit upper supply, prior selected-collision payment, and the remaining nonunit/new-exception/same-rho obligations.

**HOLD** for installation/elaboration only: the O enhanced modules and the staged `P2OriginalChildPhysicalNormalization` are not installed at their `ImbalancedChen/...` paths in this checkout. Their staged source presence is sufficient for the code-coverage discussion above, but does not establish an installed/compiled import closure. This installation status is not the reason for the mathematical supplier HOLDs.
