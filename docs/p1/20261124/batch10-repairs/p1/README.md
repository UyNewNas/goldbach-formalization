# Batch10: six proof-body candidates

Status: **source candidates, statically checked; no Lean normal/kernel acceptance claimed**.

All six source preimages equal the complete Batch9 log bindings and commit `e44e941df0a4cdf126fc0a0c41df3abd7637d1e8`. The canonical checkout had advanced to `184ae92e36c9172f35297e66d56db8a5a8180da9` at the initial read, but none of these six bytes had changed. This work edits only this isolated directory.

The six full failure blocks contain 25 actual diagnostic errors. Static verification confirms all **79 theorem headers**, **17 definition/abbreviation blocks**, imports, namespace owners and text outside theorem proof bodies are byte-identical. The original mixed LF/CRLF conventions were retained. No constants, domains, assumptions, meanings, imports or public names changed. PositiveStratumMass and the completed audits were not touched.

## Candidate SHA-256 bindings

| Module | Before | After |
|---|---|---|
| P1OriginalFourthZeroCutoffLimit | ed599e4f56d9f10c17c5c6d8d5f2c6a24a0e11d590d3c2d10e292c7bcdfd58ff | f560c82359b29029fa11132b768e7e901a2ae60e88eaaa21c67d17131db63bf0 |
| P1ActualVariableFifthProfiles | 0197fa551554e8913ed8610417983cb39aee0e9b0ca1d84700fd40a4282772d8 | 17678141c2d008fe496ecb0b0ed05888a94d7599402b70780185e7c8dca2e921 |
| P1HistoricalFifthSigned64PayloadCompleteness | 093366657a682b5136f068ea9c714a00b55528650fb211cec6f8ca0902fab638 | 1ced13e8ffbb3eb31b1952ecefb78421918942bb2cd984ee4497af76649b9673 |
| P1OriginalVariableFourthFullSourceActivation | 11a792d96c7c2b8acdfc85d9460d7ec3035e835c4348c2261a7def23c07d8523 | 05697566d8e68d1acd9feae8cedb2dfd5526513e46d27837b904dd17e26e8acb |
| P1OriginalVariableFourthSmallRemainder | 0da036140cbb8adb4b5b1da63c098030f974eafd7c817380628198bca7c6a3f2 | ab7feb610b9ecc8b879bcc38416934424bdf31fc5ac6d4b85cb8bd6666f76a98 |
| P5OriginalCommonRefinedPreservation | d503a96cda2a061b9b1e3b584ea9d52019166031e790c111db8d71845092b3eb | 2692c94da8ad4b2c0bc53b74d3212d07ac161828147254dc67fdfcca0d95e121 |

## Repairs and mathematical scope

### P1OriginalFourthZeroCutoffLimit

Actual old-source error lines: 213. Classification: API orientation / additive normalization.

Keep the existing three-term triangle chain. Close its final shifted inequality with linarith only [abs_add_le (S - R - I) R], avoiding the add_le_add_right name resolving to left addition.

Reuse: Prior isolated batch8-zerocutoff-followup candidate ed599 is the exact failed preimage; all earlier triangle endpoints are retained.

Manuscript basis: sieve-appendix.tex:273-302 (sv:finite-realization, sv:activation-tail); argument.tex:293-299.

### P1ActualVariableFifthProfiles

Actual old-source error lines: 141, 155. Classification: Namespace resolution.

Qualify both existing upper-bound invocations as VariableEnvelope.v_le_cap; no open/import/definition change.

Reuse: ImbalancedChen/VariableEnvelope.lean:82 owns v_le_cap. ImbalancedChen/P1LiteralVariableFifthPositiveCellTestLimit.lean:51,64 already uses the qualified bound.

Manuscript basis: sieve-appendix.tex:130-150 (sv:odd-gain, sv:fifth-envelope).

### P1HistoricalFifthSigned64PayloadCompleteness

Actual old-source error lines: 91, 117, 151, 186, 209, 236, 281. Classification: Boolean reduction / List API / Option injectivity / already-closed branches.

Use if_true in both zero-fuel cases; derive empty list by cases from the zero length equation; use Option.some.injEq for two row equations; delete two impossible branches already closed by split_ifs.

Reuse: The exact existing P1HistoricalFifthSigned64Payload decodeChunks/decodeRow80/decodeRows contracts and existing Option.some.injEq uses in the same module.

Manuscript basis: Engineering completeness of the existing signed64 8-byte-word / 10-column / 80-byte-row wire contract; it asserts no numerical manuscript bound, no historical 292633-row decoding or acceptance..

### P1OriginalVariableFourthFullSourceActivation

Actual old-source error lines: 63, 154, 294, 295, 329. Classification: Fin cast normalization / Bool case reasoning / namespace resolution / zero normalization.

Prove the concrete Fin.castLE index equality; close the two conflicting active/inactive Bool cases by the literal < versus ≤ contradiction; qualify the original variable-fourth level4 owner; reduce weight*0 before Finset.sum_eq_zero.

Reuse: Existing Fin.ext and active_iff_log; no alternate mathematical definition. Existing source-branch uniqueness, literal profile and Finset.sum_eq_zero proof structure are retained.

Manuscript basis: sieve-appendix.tex:273-302 (sv:finite-realization; increasing prefix order and no later-prime ancestor dependence); argument.tex:293-299.

### P1OriginalVariableFourthSmallRemainder

Actual old-source error lines: 155, 159, 243. Classification: Same-coordinate normalization / omitted elementary algebra.

Replace broad dsimp plus nonlinear search by the explicit chain E=E*1≤E*(logN/log3*t)=(E*logN/log3)*t≤1*t=t, with the original Fin.last 3 in every term. Apply the existing pointwise bound, hpay and A identity. Normalize division to multiplication by inverses in the final hterm inequality.

Reuse: Existing last_coordinate_pays_unit, hExp, hpoint, hE and ht0; the same budgets, cutoff, cap, producer licences and constants C,K,A,B,T,q remain. Existing ordinary-frontier evidence already binds SmallCellPointwise normal and UniformSmallRemainder audit24 ancestors.

Manuscript basis: sieve-appendix.tex:273-302 (small-last-prime truncation; sv:finite-realization, sv:activation-tail); argument.tex:293-299.

### P5OriginalCommonRefinedPreservation

Actual old-source error lines: 90, 175, 180, 202, 217, 223, 239. Classification: Conditional ancestry normalization / Bool decide ↔ Prop.

After the same nested-ancestor equalities, split the remaining conditionals explicitly. Add decide_eq_true_eq to the six failing policy-admissibility simplifications; every unchanged monotonicity, original policy and ancestor formula remains.

Reuse: ImbalancedChen/P5OriginalCommonFourthActualAdmission.lean:43-46 provides the exact ordinaryParityRosserPolicy / oddFirstExitPolicy / decide_eq_true_eq bridge pattern.

Manuscript basis: sieve-appendix.tex:130-155 (earlier decisions fixed; third/fifth admission tests retained); sieve-appendix.tex:273-302 (finite causal refinement; no appended-prime dependence).

The manuscript checkout is pinned at `a988cba584d803ae2856a0de50efb582f4f3dd6a`. These actual goals exposed formal API/normalization issues and elementary algebra; no need to alter the original mathematical contracts was found. This is a classification of the inspected failures, not a claim that the complete P1 project is accepted.

## Review and handoff

- `ImbalancedChen/`: complete source candidates, ready for root's exact-source installation.
- `all-six.patch` and `patches/`: unified full/single-module patches.
- `MANIFEST.json`: exact pre/post source SHA-256, Git blob SHA-1, original error/log hashes, manuscript source hashes and repair basis.
- `CONTRACT_CHECK.json`: completed static contract/source checks.
- `verify_static.py`: bounded read-only verification of the recorded source preimages and candidate contracts; it runs no Lean, Lake or cloud tool. It deliberately fails once canonical preimages are replaced.
- `EDIT_OPERATIONS.json`: exact proofbody replacements, including unchanged context.

Root should publish and validate these six normal targets. No local or cloud Lean run, data evaluation, new source import, compilation-budget increase or acceptance receipt was produced here.
