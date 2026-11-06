# P1.4: actual post-eight ordinary upper guard extraction — checkpoint

- Base branch: \`chatgpt/p1-full87-post8-suffix-20261105\`; verified predecessor HEAD \`438197bc324e9aecb7d4e837557ad086974e72fe\`.
- Proof-source commit: \`7bc96be04650c926ecd05e3106b5f2c500b96651\` (parent \`438197bc324e9aecb7d4e837557ad086974e72fe\`). No master mutation or merge.
- Source: \`P4AOriginalFull87Post8GuardExtraction.lean\`, install target \`ImbalancedChen/P4AOriginalFull87Post8GuardExtraction.lean\`.
- Source Git blob: \`ab3da5050d3b9f44d465bdadc7166f10c5f3e04e\`; 166 lines; five named theorem candidates and two definitions.
- Verification: **SOURCE_ONLY / UNCOMPILED / UNEVALUATED**, no kernel replay, transitive axiom audit, archive readback, independent review or CI.
- The latest checkpoint after publication is the HEAD of this same branch; REGISTRY.json gives the proof commit and source hash, so no temporary workspace is required for recovery.

## Mathematical finding and exact candidate progress

We read the actual \`ordinaryParityRosserPolicy false R\` definition in \`ImbalancedChen/FinitePrimeGeometryCore.lean\`, actual \`FirstExitValidSelection\` in \`ImbalancedChen/FirstExitValidSelection.lean\`, and the pinned upstream native \`UpperAdmissibleSet\` from \`MathlibNt/SieveTheory/LiLiuPrereqWFSmallRosser.lean\`.

At a selected odd prefix \`pre\` the *literal* policy is true iff both
\`(pre.prod : ℝ) < R\` and the entire upper Rosser odd-square predicate holds. It is false iff the total-product cutoff fails **or** at least one odd-square of the entire prefix fails. The latter witness is an arbitrary odd-rank ancestor, NOT necessarily the newly selected last prime.

The new \`post8OddTrace\` is the exact selected-list traversal after the actual eighth state, starting at even sign. The recursive \`valid_upper_odd_trace\` uses the real \`FirstExitValidSelection\` definition: each *successful* odd post-eight selection has passed the whole frozen-level guard. \`owned87_terminal_post8_success_guards\` extracts a real chosen sublist and those exact guards from an actual retained terminal leaf on the existing \`states\` occurrence list for either of the two actual levels \`N^actualParent\` or \`N^finiteCap\`. It invokes the existing real \`frontier_sign_mass\`, does not require historical first-eight tests at the frozen level, and does not replace sign-sensitive beta/physical modulus accounting.

This is genuine **successful selected-guard extraction**, NOT the complete \`hprior\` or \`hexit\` used by \`post8_first_odd_exit_log_lower\`: the outstanding log/rank adapter is manuscript-internal. A failed selection cannot yet be converted to \`hexit\` merely by noting policy rejection.

## Concrete falsification of a tempting but invalid bridge

For ascending prime prefix
\`[3,5,1009,1013,1019,1021,1031,1033,1039]\` set
\`R=158857908555780469977886\`. Then:

- Full product \`17650878728420052219765 < R\`;
- New least prime square \`3^2*product=158857908555780469977885 < R\`;
- Inherited odd-square at 1009: \`1009^2*product([1009,1013,1019,1021,1031,1033,1039])=1198001617780574345596704731 ≥ R\`.

So the true upper policy rejects this odd prefix **despite the new last-prime square passing** and its total-product cutoff passing. This is a synthetic mathematical counterexample to an unjustified inference, not a statement that the original87 domain contains that prefix. Nothing implies a historical rank-eight policy satisfies old odd-square guards at either new frozen level.

## Checks, compatibility and remaining obligations

Finite Python exact-integer traversal inspected 2,444 actual upper-policy retained terminal paths over a nine-prime synthetic carrier and multiple levels; each retained odd trace passed the literal full-prefix test. The explicit counterexample was evaluated with exact integers. The new Lean source has only static/escape/delimiter inspection; no Lean compiler or effective dependency build was invoked. All candidate proof terms are UNEVALUATED.

Next: map every successful odd selected prefix of the real ordinary continuation to precisely the \`hprior\` indices and strict log tests at the same frozen beta using the existing sorted rough carrier, actual \`primeHistoryLogCoordinates\`, the original eighth history and exact prime-log reconstruction. Separately split the **first rejected odd selection** into total-product failure, last-prime-square failure, and inherited-square failure; prove an exclusion/charge for the inherited case before claiming \`hexit\` or a uniform deletion factor. Preserve selected-complement tests and strict endpoints. Then advance actual exit-series/residual-integral identification and error/reserve payments.

Remaining internal obligations: actual post-eight log guard/rank matching and first rejection ownership; full-source ordinary-density/residual-integral uniform asymptotic; primitive/modulus/centre corrections; sixth filtering; saved original87 numerical binding, changed/tagged coverage, separate compiler and density reserves, same-rho total assembly, original data replay, Lean/kernel/independent verification. No old files, pins, c or K were modified.
