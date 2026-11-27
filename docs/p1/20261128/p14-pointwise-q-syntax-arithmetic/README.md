# PointwiseQ syntax and arithmetic retry

Source-only candidate for the existing P1.4 PointwiseQ owner. The original source at9aa63b9a82b25f03ea12f622a718aafb65d551cb failed normal with nine concrete parser/arithmetic/name-resolution diagnostics. No normal, kernel or owned acceptance is claimed here.

## Exact source change

- Preimage:7982 B, SHA-256 `990c9e369323a762eb11b9f2f27cd422d3b3f96ed02b81db1febc54f7132e682`.
- Candidate:8212 B, SHA-256 `4bc28079be6d5113f34fa07f352b095213cfa94df1f4128453227877d085f968`.
- Original imports and all nine declaration headers are preserved, with only the reserved scalar binder spelling λ changed to lambda. No hypothesis, conclusion, strict own-cube gate, positive-part clamp or resource setting is changed.

The five edits are: open the existing rawCandidate namespace; rename both λ binders and all16 occurrences of that token; use norm_num for firstF_two; explicitly derive nonnegative denominator plus nonzero implies positive; remove the already-unreachable ring after hsum's field_simp.

The positivity step follows only from existing hsb:s≤b, hu:0≤u, and hzero:b-s+u≠0. The same concavity argument, weights and combination identities are retained. The hconc premise remains at this original interface, with its existing companion FirstFConcavity work unchanged.

## Original evidence

`ACTUAL_FAILURES.json` preserves all nine complete PROJECT_ERROR sections and their binding to the original source and normal command. The entire existing task transport was reconstructed toEOF locally; the complete checkpoint14 normal.log was then read at198088 B and SHA-256 `036c6d57c6123c3c12518a0466aead1dda4f32a88b0de52673f392dd7e9ef325`. Every saved error section and line number matches that complete log. The raw log remains in the existing checkpoint14 export; no extra remote read or duplicate export was performed.

## Static checks and scope

`STATIC_SOURCE_CHECK.json` records the exact replacement pairs and inverse reconstruction. `baseline.lean.txt`, `candidate.lean.txt` and `candidate.patch` allow byte-level review. The entire frozenUpperPositiveKernel_ge_Q theorem, including both hlink branches, remains byte-identical. Its dsimp-before-rw[hmax] shape is a documented watchpoint for actual compilation; this retry does not speculate on a larger unobserved downstream failure.

Frozen1106 numerical-appendix SHA-256 `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232` and existing first-interval/profile suppliers are pinned in `REVIEW.json`. The errors expose parser and elementary proof-expression issues, not a newly identified substantive manuscript gap. Static inspection does not establish that the newly reachable bodies compile.

The new stage is `pointwise-q-syntax-arithmetic-retry`; it uses the unchanged original run_stage/materialize/guard/serializer acceptance route. Only the source candidate and its fixed before/after manifest are prepared. Root performs publication and scheduling. No compiler, remote task or Git operation occurred in this repair; whole_P1_4_complete=false.
