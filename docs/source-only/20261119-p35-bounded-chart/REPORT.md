# P3.5: bounded physical chart pair, source-only handoff

Base: `c5f3d76641429830e38093c384e90636fa1a3d18` on
`codex/yellow-closure-20261110` as read on 2026-11-19. The commit
containing this packet is the new SHA (obtain it from the enclosing Git
commit; a commit cannot contain its own hash). This packet makes no
modification to that shared branch.

## Candidate and mathematical range

`Part3OriginalBoundedChartPair.lean`, SHA-256
`2c3408267f14ffe434cdf7ff6b4f9b03feec52f00c5a4bff64cc917e976e49a2`,
contains two proposed proof bodies. `threshold_initial_range` takes fixed
`B >= 0`, `Z > 0`, `M = 2^j - 1/2`, and `Z <= B*M`, and aims to show
that the literal `W=max(2^j,Z^2/2^j)` is at most
`(2+2B)*(Z/2+M)` and `(2+2B)*(Z+M)`. Indeed `M <= V <= 2M` and
`Z <= BM <= BV`, hence `Z^2/V <= BZ`; both estimates follow.

`bounded_chart_pair` proposes to use that bound twice in the existing
full-positive initial-region theorem, with `Q=Z/2,Z`, the actual `W`,
and the one phase chosen by `original_pair_to_pascadi`. The two upper
prices remain separate and the original endpoint-corrected level union,
strict exceptional slots, weights, and dependent n-side row mass are
unchanged. The estimate is a reduced-n-side pair bound, **not** the raw
trace or the full (24) estimate. The constant is chosen after epsilon and
fixed B and before all physical chart and packet data. No full-J, 7/32,
half-support, or n-side common-sequence premise is added.

This candidate removes the two full-J energy terms only within the stated
bounded-ratio range, subject to successful checking of the candidate and
its already source-only dependencies. It does not remove oldform cost,
the archimedean gap, or the need to pay regular/continuous/zero/tail
terms and the downstream original scalar and reserve costs. It does not
claim that `Z <= B*M` covers the original full physical parameter range.

## Exact source selections and input boundary

* `original_pair_to_pascadi`: `docs/source-only/20261113-resume/resume-balance-policy/r14_09/avgj-next/Part3OriginalExceptionalPostRemovalPair.lean`, Git blob `a038900816ae4e167afb9f46ace2e142440d386c`.
* `initial_region`: `docs/source-only/20261115-resume/s09/actualpositive6/Part3OriginalNativeJInitialRegion.lean`, Git blob `45ae9c7ea1bb2ec98f6efe9c2205777b0c15ae1c`, selected according to its adjacent `FREEZE.json` (Git blob `ff5cb8cf7a7d1106348101affebbd87ce3f644da`).
* `threshold` and `threshold_pos`: `ImbalancedChen/Part3ZExceptionalThresholdGeometry.lean`, blob `dc31cc0fac0fe6d9fa049f66dc48ffcb9ae55d41`.
* Paper pin `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; distribution module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §§7 and 10(v)–(vii). Same pin as the positive6 manuscript audit.
* External boundary unchanged: Pascadi v3 Theorem J and its normalization/range as documented in `AVGJ_APPLICABILITY.md`; ABL v1 Lemmas 3.1–3.2 for discrete and continuous removal; a uniform archimedean gap for the spectral denominator and theta=7/32. These are not new axioms or proved here. The present bounded-ratio source uses the earlier candidate initial-region supplier, not a new assumption of full J.

## Validation, limits, and next action

* `SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no.
  Transitive axiom check: not run. Independent review of this packet: not
  run. `UNEVALUATED`: yes, all candidate proof bodies and inherited source
  dependencies.
* On the task execution environment, `type -a lean lake git` reported Lean
  and Lake not found; the workspace is not a git checkout. No proof
  command was run and there is no Lean exit code or compilation log.
  `ulimit -a` reported an 8192 KiB stack, 16384 open-file limit and no
  shell virtual-memory/CPU limit; no resource limits were expanded.
* The baseline `lean-toolchain` records `leanprover/lean4:v4.33.0-rc1`;
  `lake-manifest.json` records mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`
  and native `09b97db5764ade1246bfb77206baa1b124760958`. This verifies
  configuration only, not runtime availability.
* `sha256sum` on the candidate produced the hash above. `rg -n
  '\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1 (no
  matches). This is text inspection, not elaboration or proof checking.
  No CI, user machine, or Codex invocation was used.
* Stage the exact two selected source modules and their frozen transitive
  imports in a matching existing pinned environment; first type-check the
  new module and resolve any elaboration errors without changing its
  statement. Then run kernel replay and transitive axiom inspection and
  independently review the actual pair consumer. Separately establish
  the unbounded `Z/M` branch and raw discrete/continuous return, retaining
  both zero lanes, actual tail, 14eta/28eta distinction, 128C enlargement,
  and threshold order. Do not promote this packet on static evidence.
