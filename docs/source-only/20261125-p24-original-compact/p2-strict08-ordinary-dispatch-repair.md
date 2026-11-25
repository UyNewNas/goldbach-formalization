# P2 strict08: ordinary finite-dispatch proof transport

## Actual input and observed errors

The original checker compiled source `4ac06da3308aa24e5c90ef07cd83c69515251ef4`; local metadata HEAD at repair was `5de231954e8b1def21646c896e29ca8f02556a89`. The assigned file initially matched that actual input byte-for-byte.

Complete log: `docs/source-only/20261125-p24-original-compact/p2-strict-symbolic-08.log`, 7,480 bytes, SHA-256 `580e1ad83e9bd1b7fdd9694f40b881eb4e3801eb772ad8e3041742f7fa700e0a`. It records the selector supplier's actual PASS in 7.454 seconds, followed by three errors in `ActualThirdOriginalP4AOrdinaryFiniteDispatch.lean`:

- Line 113: `husable.1` has a `match k` proposition, whereas the supplier expects an elaborated `match k, hD, hselected` proposition.
- Lines 127/128: after `cases hs : originalMinorant ...`, the successful-constructor goals already contain `some ... = some ...`; the original equation `hs` still has `originalMinorant ...` on its left side.

The completed batch has 293/321 successful modules (289 reused, 4 fresh) and three directly failed modules. This candidate was prepared during that run and was not part of its compiled input.

## Preserved dispatch and minimal candidate

Rechecked the frozen 1106 producer's affine-minorant selection followed by residual/domain tests in `certify_extended_prefix.py` (lines 189–274), and the existing finite-selector and B/tent supplier interfaces. The cached producer SHA-256 is `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`, from frozen publication commit `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. The Q80 producer's distinct candidate order/score is not substituted into the existing auxiliary P160 selector.

The same already-selected B-or-tent winner is dispatched. `usableCandidate` remains a post-selection premise; neither an unusable winner's replacement nor a successful mean calculation is inferred. The fixed constants, residual/low guards, exact OLD/NEW query operands, ratios, positive logarithm bounds and rounded upper formulas are unchanged.

Only three proof-expression replacements are made:

1. Supply the residual argument as `(by cases k <;> exact husable.1)`, reusing the case-normalization pattern in the now-passed selector. The extra dependency proofs disappear under each concrete side; `husable.2` and all remaining arguments stay unchanged.
2. Use `Or.inl rfl` for the already reduced B-constructor goal.
3. Use `Or.inr ⟨s,k,rfl⟩` for the already reduced tent-constructor goal. The `none` case still uses the original `hn hs` contradiction.

These are dependent-expression/case-reduction issues. No omitted mathematical estimate, new hypothesis or substantive manuscript gap is needed.

## Frozen source and verification boundary

- Before SHA-256: `15cb009fd09b6060f281896e71f1207860f85a7c1c68c9829b9b21ec708b6428`.
- Candidate SHA-256: `3806bc6a3d7c4abfc670fefe9fc2dc4b78b08989f2cc8861d26d2b1a00e54a0d`.
- Mechanical comparison against the actual input preserves all 3 theorem headers, 5 complete computational declaration blocks and both imports. `git diff --check` passes; no options or proof escapes were added.
- Independent read-only review by `p24_project_cache_reuse` of the actual error targets and subsequently the frozen source diff/SHA found no static blocker. The frozen diff contains exactly the three reviewed edits; no compilation was performed.
- A bounded exact-symbol search for `original_finite_selected_tent_integer_upper` found only its definition and this call in `ImbalancedChen`; no additional identical downstream call was identified or changed.

Only the assigned dispatch file and this note were edited. The passed Selector file remains frozen. No index, commit, ref, remote input or compiler task was touched. Actual acceptance awaits the parent's original checker.
