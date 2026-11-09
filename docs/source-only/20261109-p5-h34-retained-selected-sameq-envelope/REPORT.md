# P5.6 / h34 — actual retention + selected same-Q feedback envelope

Date: 2026-11-09.
Repository: UyNewNas/goldbach-formalization.
Branch: `chatgpt/p5-h34-retained-selected-sameq-envelope-20261109`.
Verified incoming remote HEAD: `110d0d0f515b91f35fc0d534889198b3e91e77fb`.
Actual mathematics commit: `344c843fc72c586b3918dc9817a099a29fcbded2`.
Source: `Part5OriginalH430ActualRetainedSelectedSameQEnvelope.lean`.
Source Git blob (read back): `4a5a743d11d54a854e19a8f8a2cb9709a921ce78`.
Two definitions, five theorem CANDIDATES, 211 non-empty/empty lines in GitHub diff.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Verified predecessor and scope

The previously confirmed branch at `110d0d0` supplied the literal actual-selected same-root-Q ideal coefficient read and its selected-error bound, but did not put the selected ideal inside the true *retention* accounting or give an absolute bound on the ideal row.

This increment is based on that exact previous HEAD, not the historical entry `0a3fa5a`. The earlier source remains unchanged. There were no in-progress GitHub Actions runs when this packet was prepared. Repository push permission was confirmed; only the independent h34 branch/directory was written.

## New manuscript-local candidate statements

1. `actualRetainedSelectedPhysicalRead`: the original literal `actualRetainedRead` from the generation-(g+1) request table PLUS the actual selected bank/Buchstab physical coefficient row evaluated on the generation-g predecessor atom array.
2. `actualRetainedSelectedIdealRead`: identical retained read PLUS the previous packet's true winning-cell/Buchstab same-Q ideal coefficient read, on the SAME predecessor array.
3. `actual_retained_selected_same_q_gap_le_error`: their difference is controlled by the EXISTING actualSelectedError. Retention cancels exactly and is never charged a bank/Buchstab error.
4. `actual_selected_same_q_ideal_abs_envelope`: the actual selected ideal absolute value is at most
   `(12*actualBankTheta + 5*actualBuchstabTheta)*predecessorAbsMass + actualSelectedError`.
   The original preceding finite RowAtom L1 mass replaces any freely chosen vector or parameter M; no sign condition is imposed on old feedback atoms.
5. `actual_retained_selected_ideal_abs_envelope`: the same estimate with an ADDITIONAL `|actualRetainedRead|` term outside the selected 12/5 budget. No subtraction of retention or unproved retention norm is performed.
6. `actual_selected_same_q_ideal_zero_of_zero_thetas`: under the already supplied selected-error/row bounds, when both genuine bank and Buchstab Theta vanish, both selected physical and ideal coefficient reads vanish; the retained read is **not** assumed zero.
7. `uniform_actual_retained_selected_same_q_envelope`: one threshold before N, n, root, tau, p and g simultaneously pays the original selected error and bounds the ideal retention-plus-selected expression.

### Crucial exact boundary

These new totals are **mixed-generation feedback accounting expressions**, NOT definitionally the original full new-table selected-count sum. The bank candidate and Buchstab next-table values still need to be matched with their corresponding old-array coefficient reads. In particular `markedBankCandidate`, `markedBankRead`, `actualBankRead` and the original U3/U4 arithmetic q/tag source are NOT identified by assumption. The previous ideal `cellReadIdeal`/`integralRow` is still NOT the fully matched manuscript PP/same-rho/floor/seed integral.

No new h34/hLower axiom, target-equivalent assumption, sorry/admit, unsafe/native proof bypass, or external analytic theorem. Same physical Q within each root, genuine original scalar/specified-cell selector, actual marks and list-position multiplicity, original c/K, root norm 7/2, bank norm 12 and Buchstab norm 5 are preserved. The epsilon selected error is paid once, not added again to any previously paid term.

## True remaining manuscript-internal obligations

- Identify original actual bank/Buchstab new-table contributions with physical old-array coefficient consumers or retain their exact signed residuals, including fixed/switched/floor/base/seed.
- Prove the original `predecessorAbsMass` base and induction growth needed for CLOSED-CELL; this packet does **not** assert a uniform upper bound for that mass.
- Complete original U3/U4 selected-count source, root weights, full/selected/inherited owner filters, six rejection lanes, physical-event collision capacity and signed H430 unpaid debt.
- Match the actual same-Q target to the fixed manuscript PP/same-rho integral, and the native history, outer Theta/count and one causal 430+11 common refinement.

## Validation, installation, and next exact action

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` (`paper/source/manuscript-body.tex`).
Toolchain: Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; neither is changed.

The remote new source, blob hash, and commit diff were read back. A static source scan confirmed the named declarations and absence of forbidden proof escapes. This runtime has no `lean` / `lake` / `elan` (also checked common installation directories); the pinned source-only dependency closure is not staged. Native shell DNS to github.com is unavailable. No local Lean/Lake build, kernel replay, transitive axiom audit, numerical430 table replay, or new CI execution occurred. GitHub code upload + static scan is NOT compilation. Five candidate theorems and inherited finite guards remain UNEVALUATED; no new green node.

Once an authorized pinned build environment is available, stage the original source-only import closure and compile only `ImbalancedChen.Part5OriginalH430ActualRetainedSelectedSameQEnvelope` with immediate dependencies. Fix genuine Lean errors in this task's own files and re-run. Then derive the missing original new-table bank/Buchstab-to-old-row residual and base/seed/floor growth rather than inventing a free count-owner licence.

**完整h34稿内证明仍未闭合。**
