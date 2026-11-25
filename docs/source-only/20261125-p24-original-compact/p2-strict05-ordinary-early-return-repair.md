# Strict 05: ordinary early-return query normalization

## Observed failure and scope

The original P2 strict-symbolic-05 checker, compiling proof source
`ed3b1667`, reported three type mismatches in
`ImbalancedChen/ActualThirdOriginalP4AOrdinaryEarlyReturnLeaf.lean`:

- At lines 166 and 235, the reader enclosure used the real power
  `(2 : ℝ)^160`, while the rational NEW query retained its outer real cast
  of `(2 : ℚ)^160`.
- At line 187, `hmu` retained `realBox b 0`, while the log guard expected
  the real cast of `b 0`.

The completed batch log is `p2-strict-symbolic-05.log` in this directory,
17,467 bytes, SHA-256
`d16e52df7542486074b3ccadc65abca416f372283e7f7c34cfe7e20271d841e4`.
The batch finished with 283 of 321 modules successful, including 276 reused
records and 7 fresh passes; four modules failed directly and none remained
pending. It records `ActualThirdOriginalP4AOrdinaryBCandidateLeaf` passing in
5.192 seconds and the already repaired rounded stored consumer passing in
5.812 seconds. Neither of those files is changed here.

## Manuscript correspondence and classification

The frozen 1106 `numerical-appendix.tex` specifies directed interval
arithmetic, returned denominator `2^160`, and the lower delayed function's
zero branch at arguments at most 2. Its SHA-256 is
`bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.

The corresponding frozen `certify_extended_prefix.py`, SHA-256
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`,
uses `jensen_difference_upper`: after rejecting a crossing of 2, it forms
the NEW mean, reads its upper endpoint, and returns that endpoint directly
when `old_hi <= 2`. OLD endpoint reads and chord arithmetic occur later.
This confirms the existing early-return semantics; no historical producer
or numerical data is reconstructed.

All three failures concern expression normalization. They do not expose a
missing inequality, omitted mathematical argument, or changed branch bound.
The original 32/256 logarithm parameters, integer data, query denominator,
branch ordering, and all hypotheses remain unchanged.

## Minimal candidate

Both query proofs add `Rat.cast_pow` and `Rat.cast_ofNat` to their existing
`simpa only` lists. The log-guard application adds `realBox` to its existing
simplification list. These are the same normalization patterns already
present in this batch's successful ordinary B-candidate leaf.

Static comparison against `ed3b1667` confirms that the entire candidate is
exactly these three proof-site replacements. All 19 public theorem headers,
the one private theorem header, both complete computational definitions, and
both imports are byte-identical. `git diff --check` passes. No new assumptions,
axioms, admitted proofs, evaluation mechanisms, or linter settings are added.

Original source SHA-256:
`072e4888f2b6afe5c5955645fa39963dce26954bca92c6f0a4b5c540323fd34c`.

Frozen candidate SHA-256:
`b4175a40bbe2c155bbec2c308b81473f8f31f3734eed85fc5d512b1f1dc21269`.

The candidate has not been compiled. Root will publish and verify it with
the original checker; this repair grants no compilation or kernel credit.
No index, remote task, or running P2 input was changed by this repair.
