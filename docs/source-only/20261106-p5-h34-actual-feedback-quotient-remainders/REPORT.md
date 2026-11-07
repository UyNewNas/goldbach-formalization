# P5.6 → h34 — real original 106-bank integer feedback remainder ledger

Date: 2026-11-06. Repository: UyNewNas/goldbach-formalization.
Branch: chatgpt/p5-h34-request-admission-20261105.
Verified baseline: cdb3d41462508ced5e88d40d26c6a1effe7c630d.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766 (unchanged).

## Increment

New candidate module Part5OriginalH430ActualFeedbackQuotientRemainders.lean.
It reads exactly the original lowerWeights and upperWeights of each literal action row; each original product is divided by P2Selected430LiteralActionData.q before being summed. No deduplication and no real division substituted inside the original integer numerator.

exact_feedback_integer_ledger proves the integer identity:

unroundedNumerator = q80 * feedbackNumerator + remainderNumerator.

remainderNumerator_nonneg and remainderNumerator_le_length prove 0 <= remainderNumerator <= (#original listed weighted products)*q80, EVEN FOR SIGNED OLD TABLES. The latter is intentionally weak but guaranteed: one q80 unit per actual product, not one per bank. It does not assert that an unexecuted finite table has any specific length or content.

ideal_feedback_exact moves the source identity to REAL feedback, preserving both original divisions (per-product q80 and outer row.divisor) and the final 2^80 decoder. feedbackRoundingLoss_nonneg and feedbackRoundingLoss_le_length give its actual sign and finite payment envelope. bank_ideal_feedback_exact identifies the signed correction at the actual selected historical LevelIndex, with the exact old array, original theta, and positive mark. actual_bank_corrected_feedback_upper plugs the exact subtraction back into the prior fixed-cell conditional bank bound. No scalar-to-specified-cell exchange, no altered 106 choice or new closed-cell count premise.

This is a genuine arithmetic integer-floor payment ledger, distinct from the earlier conditional fixed-read interface, but does NOT pay the original bank base/switch/seed, prove original selected-count ownership, or close one-generation arithmetic count induction.

## Verification and remaining tasks

SOURCE_ONLY / UNCOMPILED / UNEVALUATED. No Lean/Lake installed, no CI or heavy compilation launched, no kernel replay, no transitive-axiom audit and no finite table replay. Text inspection and structural checks do not confer proof credit; all theorems are candidate proof bodies.

Remaining manuscript-internal obligations: complete original U3/U4 selected-count and owner/root-weight/filter/exception multiplicities; establish arithmetic predecessor CLOSED-CELL lower/upper induction and original base/switched/seed application; use per-action literal floor charge in the correct finite integral/Theta payment without counting it twice; PP/same-rho, native-history masses, and common 430+11 causal refinement. Original c/K, root norm 7/2, row norm 12, alpha, same-Q and all thresholds unchanged.

Next: combine the explicit per-product signed rounding ledger with the original literal base and selected arithmetic count source, checking the correct direction and actual row divisor. Do not invent count source equality or redo P1.4/P3.6.
