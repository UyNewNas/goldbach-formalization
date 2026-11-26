# P2.5 continuation — 2026-11-26

User scope: complete Saving16 inside the November 6 manuscript, reuse existing work,
write source locally, use the supplied compiler environments, and submit to GitHub.
No new axiom, sorry, admit, native_decide or unsafe proof shortcut is permitted.

Baseline: remote `work/p2-5-saving16-20261125` at
`4e69759e3d27495c0e7bccfee23b7a0b42c48ea6`; its tree equals the previous
local `aeebee513ed88332ba4ef1c8f4b4222252898dcc` tree. The older dirty checkout
is preserved. This continuation uses `/workspace/library-files/p25-proof-work`.

## Execution ledger

- Recovery complete: original round3 task `ba9a22be4e61459497878039580c02c9`
  finished with 325/377 normal compilation records, 38/69 accepted owned audits,
  eight direct normal failures and 44 dependency-blocked modules. The complete
  task stdout is retained here. This is not a successful P2.5 acceptance.
- The published final cell00 decoder candidate was tested by task
  `1847725e973d4e2f866720eac3f6f4d9`, reusing 21 accepted dependency objects.
  It failed normal checking: the two mapM goals were resolved, but three existing
  array aliases remained, followed by a kernel memory limit. The exact failed
  receipt and logs are preserved under `field-final-attempt004`; no new formal
  credit follows from that attempt. A targeted proof-expression repair is pending.
- All eight complete original per-module logs have been recovered and checked
  against their recorded source hashes. Independent review approved four exact
  historically compiled source repairs and four existing draft repairs, with only
  the additional unused-simp removals established by the complete H5/H7 log.
  The unchanged 377-module closure and 69-target audit will decide current reuse.
- Published the reviewed analytic repairs and strict continuation at
  `168973571f795dbe8fb1c1bccfd7f7c54899b36a`. P2 task
  `381b23081efa4391a45337f2a1eb0ab8` reached 330/377 normal successes, reusing
  all 325 prior successes and adding five. Its completed owned audit accepted
  41/69 targets, reusing all 38 earlier successes and accepting three new owners
  containing 245 declarations. Six direct failures and 41 blocked modules remain.
  The complete original receipt and six failure logs were recovered byte exactly;
  all source, gate, runner, HEAD, history, baseline and external postflight checks
  matched. The aggregate remains failed.
- Published the explicit cell00 field composition at
  `b667409e7e7f23094637dfccfdceec6e6d34ee68`. P3 task
  `202af6f52a5c405eaa74fe1f00906a75` failed only on kernel memory at the final
  theorem. The exact failed receipt is retained under `field-explicit-attempt005`.
  The next candidate uses a private symbolic composition lemma, while preserving
  all public statements and discharging all helper premises in the closed theorem.
- Published that symbolic repair at `99ec807044cd865b9713e769c6a967094c4b3e34`.
  P3 task `271829aa21dd4513b8e2754b759fb241` accepted the final field decoder:
  normal compilation, independent replay and complete owned audit all exited zero.
  The audit covers seven declarations including the actual private composition
  helper. All 21 accepted dependency objects were reused without repeating their
  gates. The exact receipt, logs and accepted object are retained in
  `field-symbolic-attempt006/ACTUAL_EVIDENCE.json.xz`.
- Published the independently reviewed five-consumer continuation at
  `8fb0faace8f95a4ad4be26f32350575491445ac4`. P3 task
  `c9cc66562e934713bcf75ab704f8562d` failed on disk exhaustion while creating
  the first target directory, before any normal, replay or audit stage started.
  All five owners remain unaccepted; the exact receipt is preserved under
  `consumer-attempt004`. Existing proof sources remain unchanged. Resource
  recovery and a fresh continuation must preserve this failed attempt.
- Resource-guarded consumer v5 was published at
  `be20f0b050bb787ecb98f9afdd9b6a386706f45a`. Its actual attempt005 accepted
  `P2Saving16Cell00Decoded` with four owned declarations and then encountered
  kernel memory errors in `P2Saving16Cell00OriginalParse`. The aggregate remains
  failed and the three later owners remain pending. Complete actual evidence
  and the accepted Decoded object are preserved under `consumer-attempt005`.
  Continuation must reuse that owner and repair only the observed transport
  expression, with the public statements and original source data unchanged.
- The independently reviewed four-consumer v6 continuation keeps accepted Decoded
  as dependency 41 and changes only OriginalParse proof expressions. Three private
  symbolic-index wrappers preserve the same three public statements. All 46 offline
  guard tests passed; actual compiler gates remain pending. Earlier consumer004/005
  aggregates retain their failed status.
- P2 storage v2 task `f1014302ea974fc9a9a13ebb97cee682` stopped at its
  capacity guard before mutation. Its exact 1,406-byte receipt is retained under
  `p2-storage-round4-v2/apply002`; no storage recovery or proof credit is claimed.
- Four-consumer v6 is published at `4653b261828f127ba0b5082eaf1106a3fea09d46`
  and submitted as P3 task `c797343dbed9482482010ecb52e4b22e`. It was still
  queued at this checkpoint; source review supplies no compiler acceptance.
- Storage v3 adds only unreferenced `docs/evidence/owned-frontiers/` Git working
  copies. An exact read-only inventory found 1,278 ordinary blob-equal files and
  193,220,608 conservative allocated bytes; eight attribute files stay protected.
  All 15 policy/capacity tests passed independently. Every live protection, source,
  cache, history, and 1 GiB plus reserve check remains unchanged. Recovery itself
  is still pending and must pass before analytic round5 runs.
- Whole P2.5 remains open: all fourteen original archives and 39,741 simplex
  operations, their exact individual Q96 floor sum, analytic ownership/integral
  closure, and the same-Q/rho signed distribution supplier.

## Decisions

- Reuse the existing plan in `docs/superpowers/plans/2026-11-25-p2-5-saving16.md`.
  This is continuation of the user's authorized design, not a new proof route.
- Preserve all selected source statements, data and complete modulus terms.
  Reuse historically compiled repairs only after current preimage comparison;
  old objects require current source/dependency/context identity before reuse.
- Lean theorem checking, independent kernel replay and full owned-declaration
  audit are the proof validation gates. Finite consumers transport proved
  equalities instead of repeating parser, determinant or floor evaluation.
- The manuscript and existing OwnedIntegral chain need a disjoint positive
  inner union, not an exhaustive triangulation. No extra coverage theorem is added.
- The manuscript freezes `3ffa2d1` and `a988cba` have identical release TeX;
  the intervening change only updated README. Existing manuscript pins are valid.

Formal credit in this ledger is limited to the explicitly identified accepted
owners and their exact receipts. It does not establish completion of P2.5.
