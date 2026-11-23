Three-module read-only candidate handoff

Status: uncompiled candidates; no Lean/Lake/compiler invocation and no changes to Member, main, P6 or frozen sources. `candidate.patch` passed `git apply --check` against main at the recorded snapshot. This is patch applicability, not Lean acceptance.

All three Member baselines equal main; P6 has none of the three selected source files. Exact baseline/postimage SHA256, 84 public and 3 private theorem headers, and per-module source relationships are recorded in `CANDIDATES.json` and `STATIC_VERIFICATION.json`. Independent declaration scanning confirms every byte outside theorem implementations remains the same; imports, definitions, constants, banks, quantifiers and hypotheses remain unchanged.

P2HistoricQ80DefectLookup reuses 10 existing proof bodies from published commit ab19e4c4f508a2ab624b5bab71af4482e4d46b80, blob 3c422002845ffcd4034a4f28bb3c0538030c809e (source SHA256 2315adab3278273913f68b9130b07b5a9903eedc49502f6870eb53a5be2819d8). The old complete file has different imports/core ownership, so only its proofs were reused. Repairs replace unavailable ext registration with constructor congruence, normalize dyadic casts, unfold rectangle definitions and explain the Int-list flatMap coercion. The fixed closed-cell bank equality uses the existing kernel decision proof and retains all numeric data.

P2TableActionSoundness has no other variant on available refs. Its candidates make Real casts explicit around floor monotonicity, normalize the logarithmic integral expression, specialize Bool cell bounds, handle tableGrid50 exactly, and repair typed tactic-term pair syntax. These are local elaboration and elementary-simplification issues. The source remains an ordinary Wu small-delta result; this does not supply an enhanced-family equivalence or complete the106-action/430-round analytic license.

Part5OriginalUpsilon5CausalSplit also has no alternative published variant. The candidate introduces the missing implication hypothesis, types the two region inequalities explicitly, and beta-reduces integrands before three rewrites. The enhanced max, equality wall at s=4, s>4 second region and explicit ContinuousOn corr [2,5] premise remain intact. No step-table continuity claim is added.

The1106 manuscript anchors are numerical-appendix.tex303-374 (Q80 closed-cell recurrence), argument.tex635-638 and670-678 (normalization and Buchstab transitions), numerical-appendix.tex378-412 (actual two-prefix max/residual and admitted248 correction), and sieve-appendix.tex200 (ordinary lower factor on[2,4]). No substantive local proof gap was identified by this static review; successful normal/kernel/all-public verification is still required.

The sole source/build owner /root/manuscript_inventory can review `candidate.patch`, recheck the baseline hashes, apply the proof overlays and perform guarded validation. DIAGNOSIS.json contains exact failure-log locations and the scope limitations.
