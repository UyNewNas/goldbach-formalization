# T06 v3 inherited-module repairs

Status: SOURCE_REPAIRED / UNCOMPILED / remote verification pending. Author: gpt-6.1-sol, xhigh. Only this new `v3repairs/` directory was written. Production, all previous T06 frozen files, T01 installation/workflow/resources, and Git/CI state were left untouched.

The authoritative inputs are the six entries of T01 `EXACT_INSTALL_MANIFEST-v2.json`. Their on-disk bytes matched each entry's SHA256 before copying. The real v2 job log is `output/t-batch-20261110/T01_V2_FAILED_JOB.log`, SHA256 `5d4f853ff17bdd28d15f45d56ddb039ce57fa3fe39a82df02236f4a839ea97eb`; the exact relevant errors and input/output provenance are retained in `REGISTRY.json`. The installation paths stay `ImbalancedChen/<module>.lean`.

All original declarations, complete statements, imports, definitions, endpoint conventions, constants and hypotheses are retained. There are no statement differences, new target assumptions, deleted failed dependencies, or proof placeholders. Each edit is inside an existing proof body. No mathematical theorem is weakened to obtain compilation.

| Module | Original SHA256 | Candidate SHA256 |
|---|---|---|
| P1FourthNearOneKernel | `83fc7aa451aa3a40d9112f511b3d869045117a79eb7d4ba3f6c6626d96c1f19d` | `046fbb5257e9a4bbe0d7bd075da054b6dfe2a2e572fa777b13684a29d61a1f83` |
| P2DirectedLogRounding | `de7d70cfbabaa5c0abde8eea3514d0ad1df16d2c4deaa5961b6449bc9c3b666f` | `11d018492ac313d814c9a18df0624e65275571b4c7725d9486ca57c00f3fbcd3` |
| P1OriginalThirdGammaFirstCoordinateRise | `5a2b06092371fb49adcc5742ac538fbb32d6f0c2f340f166a157cda27649ac6e` | `ce79a843c6ac5b6ba7977e40a369cfa7226047d3785f2be466357a29e8536ed2` |
| P1ActualUpperNearOneBound | `3fac5d307e02e636df9e223f102613f6bc12f017bce5411e1121d0b8bef67600` | `e2cd0184207d94fe509ba7b9e2295c07ba0aa505f12dffcefd5a5182806903e4` |
| P5HistoricalRectangularGammaTransport | `6917658f287ac043bfebca18c7775efc145db71796a2ee71ae03e0e16c2e625a` | `fb0e5a57a1123f2ef778c36f1ee29820a0db138d8cc0d862e244eec5d2b33130` |
| P5OriginalSignedMidpoint | `507dee4fe27c1fb4b6bdc4ba095a1fde3651a4ca215fa4381fbc4bafe89b0e69` | `9fdda945eebd1a69a285ba9f5cfb7654a5e5caca72b500c12376db0614709442` |

## Error attribution and repairs

1. **P1FourthNearOneKernel, original lines 58, 60, 76, 106, 118, 148, 247.** Expose `Ici`/`Ioi` membership with `change` before arithmetic or underconstrained order constructors. Correct the `SourceTPlus` qualification to `MathlibNt.SieveTheory.suzukiProposition118SourceTPlus`. Remove the `dsimp` that the actual log reports already made no progress after division elaboration. The closed extension remains `A/s` through two and the actual factor strictly above two. Its value at one remains the extension value; no equality with the raw totalized source factor at one is introduced.

   The Suzuki API was checked at the pinned native revision `09b97db5764ade1246bfb77206baa1b124760958`: `MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiProposition118SourceSeriesPairing.lean`, blob `eee5859f2f858c3c82fb37e65f2cbe172096c74a`, declares the parent namespace at line 22 and `SourceTPlus` at line 31. The imported `ActualThirdOriginalLocalCurvature.upper_eq_inv` (line 19) supplies the genuine initial interval, `RosserContinuousSourceUniformity.continuousOn_suzukiContinuousUpperFactor` (line 109) supplies continuity on `Ioi 1`, and `ActualThirdOriginalCoupledRecurrence.upper_antitone` (line 77) supplies the global upper bound. The original closed-set union argument is retained. These are existing mathematical inputs, not fabricated continuity or endpoint premises.

2. **P2DirectedLogRounding, original lines 142–156.** Reuse the exact existing repair from immutable mirror commit `085ef205771858c7115d092766b3ffcf7ab86d55`: replace the two `mul_lt_mul_right` calls with `mul_lt_mul_iff_left₀`. The candidate's Git blob is exactly that prior module's blob `8eb19a7681fddfb67c2c58857cfa2eb9f7cce80e`. The original call requested unconditional strict monotonicity of multiplication on all rationals, while the replacement uses the supplied positive dyadic scale. Both error bounds retain their strict one-ulp statement, including negative inputs.

3. **P1OriginalThirdGammaFirstCoordinateRise, original lines 41, 57 and downstream 121.** Before `linarith`, identify the two additive spellings of the argument of `v`; arithmetic tactics cannot identify nonlinear function atoms from algebraically equal arguments on their own. Replace three broad `convert ... <;> ring` steps with `simpa only [add_assoc, add_left_comm, add_comm]` and explicit shift `d/2`. This preserves every selected pair gate and the true `fullGamma` maximum. The last unknown-constant error is downstream from the failed `fullGamma_shift_le` declaration. The timeout remediation requires remote confirmation; no heartbeat limit was increased locally or in source.

4. **P1ActualUpperNearOneBound, original line 245.** The actual Euler supplier gives `V ≤ B*S/log(y)`. Deriving `V*log(y) ≤ B*S` uses `(le_div_iff₀ hlogy).mp`, replacing the reversed division API. All threshold quantifiers and the original uniform near-one bound remain unchanged. Supplier: `ActualSmallEulerNormalization.exists_actualSmallEulerProduct_le_singularSeries_log`, line 137, v2 blob `e381b857ad6f3e1810826a5e62eb3c54547c9527`.

5. **P5HistoricalRectangularGammaTransport, original lines 95 and 121.** Qualify the intended real affine branch `VariableEnvelope.B` in the local rescue comparison and its unfolding. The unqualified name resolved to a natural-number combinatorial function. The later failure to bound the genuine `VariableEnvelope.B z` is a consequence of that wrong local expression. The actual `9/2` rectangle error, `e+7chi≤3/256`, max rescue and both pair gates are untouched.

6. **P5OriginalSignedMidpoint, original lines 40, 81 and 110.** Specify `volume` in the two local integrability facts and the two `integral_mono_on` calls; simplify `id` before polynomial normalization of the cubic primitive. The exact signed identity and original `1/24` constant are retained. Pinned mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`: IntervalIntegral/Basic blob `89cf34cb5387b20f311300f6e708aa752ebf3a23` has the generic-measure `ContinuousOn.intervalIntegrable_of_Icc` and `integral_mono_on`; FundThmCalculus blob `82d269a5e9269d791f5581f5f0da29cfc125541a` has the specifically-volume FTC used here.

## Source mathematics and scope

The actual manuscript `proof-library/source/upper-finite-compact-margin-audit-20261010.txt` at paper commit `9731290e8f53cffda44129906cde6a965eaa869b`, blob `0bf009e7a3de5524dc728029af65e9b29fed1fa1`, SHA256 `4aef07338b8d0363c39b39c10307e2c1ff1a3c90aaa7b74f4fc30d91e40a5172`, was reread at the literal Gamma rule and (C3), lines 62–78. The real selected-gate and `max(A,W)` geometry is already present in the imported `HistoricalThirdCoarsePolicy`; the repair neither changes it nor substitutes an ungated rescue. The first-coordinate rise proof uses the already explicit affine slopes and genuine gate monotonicity.

The signed midpoint source `proof-library/source/sharp-switch-midpoint-proof.tex` at paper commit `ba6ec11d800eccc54406490631895e174de85766`, blob `3901c202686777a252f6a1104b4f3dd7577f7b0f`, SHA256 `3b89076e90113e4b8d0a85feb02196c19b7090e546911d0a1f874dffa0dacbaa`, explicitly specifies the signed `delta^3[inf g'',sup g'']/24` remainder. The repaired module still derives it through the same exact two FTC primitives and nonnegative half-cell weights.

These six logged failures are classified as expression/API/elaboration errors. No new omitted analytic theorem or mathematical gap was needed for these corrections. This classification concerns these six repair scopes only; it does not close any previously recorded whole-manuscript gap or the full original P3/Fourier licence.

Read-only local source variants and immutable mirror history were searched before writing. The P2 predecessor is directly reusable; the other inspected copies had the original failing bodies. The old base-topic remote refs were read (p1 `f5a62f9bc862b89d03d5d211379664d8866d689f`, p2 `192228c26a6e5d72e73a87444bd727fa74a336f6`, p5 `745469bce852f868a9f788f72fd9d6c320242dec`); the p1/p2 files are absent on those old topic trees, so they are not used as replacement inputs. The v2 manifest remains the only installation authority.

## Pending verification and handoff

T10 reviews these exact candidates independently. T01 alone integrates v3 installation/workflow/resources, and root alone runs remote compilation and kernel/type/axiom checks. In particular the source rewrite of the Gamma timeout must be judged by the real remote result. No local Lean/Lake/LSP, guard, numerical/finite replay, quota check, Git mutation, CI action, or subagent spawn was performed. No green or successful compilation is claimed.
