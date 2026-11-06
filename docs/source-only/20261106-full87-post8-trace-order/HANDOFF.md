# P1.4 — actual original87 post-eight odd-trace order / parity continuation

## Resume (do NOT restart at older navigation commits)

- Last previous branch HEAD actually compared (identical):
  `1b6d25c56d4d0b347af171a6c12c539739faf5c0`,
  `chatgpt/p1-full87-post8-inherited-squares-20261105`.
- This run's isolated branch:
  `chatgpt/p1-full87-post8-trace-order-20261106`.
  **Re-read its latest HEAD before any future write.** It may advance
  beyond the hashes quoted here.
- New candidate source:
  `docs/source-only/20261106-full87-post8-trace-order/P4AOriginalFull87Post8TraceOrder.lean`;
  source readback blob `ac0a4b5918570020c1ef9fc457d3fb05d49f23f2`;
  initial source commit `8ef63fb015830071df5fa082eeddbc29ebf57109`;
  same-witness cleanup commit `de584a8c00bfc9566c8f68398075e771a555b09e`.
- Corrected predecessor:
  `docs/source-only/20261105-full87-inherited-odd-squares/P4AOriginalFull87InheritedOddSquares.lean`;
  q-suffix parity application fixed in commit
  `f2c92e73e488c78cc8daeb2832a3430106bc97a3`;
  new blob `f4e61a586ff6699240591f8cbf488c18f22fa364`.
- Report committed at `c0385747b18d56e9bc36fae4e105cf3ba673de40`;
  input boundary at `5425ba37bf09b080a02153c1ab27254192fc50cd`.
  See REGISTRY for the complete hashes and final checkpoint.

## What actually changed mathematically

The source-level fact of interest is that, after EXACTLY eight
historical selections, the actual `post8OddTrace` records successful
odd-cardinality prefixes at the frozen ordinary level. Given the
literal descending rough carrier, increasing reverse-stored prior
history, and the strict remaining/ancestor boundary, the new proofs
show each recorded prefix is strictly increasing and Nodup. The trace
parity induction gives `Odd older.length`; `Nodup` then gives
`Odd older.toFinset.card`, exactly what the earlier
`owned87_post8_later_odd_reject_last_square` needs.

Unlike a fixed `rank=8` shortcut, the trace induction handles
arbitrary later selected depth while keeping the original occurrence
list, actual parent/cap Boolean and complete full-prefix policy.

One actual previous source proof error was corrected:
`(hqeven hcard).elim` (non-function even proof applied to its negation)
became `(hcard hqeven).elim`. This is a type-direction fix, not new
mathematical content or a compilation certificate.

## Still conditional, NOT proved from the state producer

Four carrier facts are explicit at the real original87 state:
`s.selectedPrefix.length=8`, `s.selectedPrefix.Pairwise (<)`,
`s.remaining.Pairwise (>)`, and
`∀ p ∈ s.remaining, ∀ r ∈ s.selectedPrefix, p<r`.
Their direct derivation from the predecessor's actual eighth frontier
is NEXT, not an external hypothesis, and is not to be assumed
unconditionally.

For true later first exits still missing:
- a literal first-rejected pair whose two members appear after the
  successful odd trace, with p<q<all older and the actual rank;
- the rank-nine special case where inherited historical square
  failures may occur;
- normalized log hprior/hpair/hexit and last-prime reconstruction;
- same-source ordinary Rosser exit-series to residual integral,
  primitive/modulus/centre errors, sixth filtering, saved87 original
  numeric archive, changed/tagged coverage, two reserve books,
  final same-rho assembly and all formal replay.

Do NOT attach another mask, infer signed saving from cap monotonicity,
or substitute a different source. Preserve strict endpoints, signs,
occurrence multiplicities, full-q beta, and parameter-before-N
quantifiers.

## Evidence and constraints

11,520 synthetic finite history/selected-list combinations were
checked in Python with odd trace rank, no repeats and strict
increasing order; this is NOT actual87 evaluation. The first attempted
larger exhaustive enumeration was interrupted before completion and
must NOT be counted as an additional successful check. Both source
files were fetched from GitHub and their blob SHA-1s matched the
values above; forbidden escape-token scan was clean.

NO Lean/Lake compilation, kernel replay, transitive axiom audit,
original numerical archive replay, independent review, CI dispatch,
Codex, toolchain upgrade or user workstation access. Everything
SOURCE_ONLY / UNCOMPILED / UNEVALUATED; formal credit zero.
No analytical external input was proved or newly invoked.

## Concrete next action

Read the genuine firstExit depth-frontier producer used by
`P4AOriginalFull87OwnedEighthSource.frontier`. Find the existing
pairwise/sublist and selected-prefix-versus-remaining boundary
invariants. Use them to eliminate ALL four extra carrier hypotheses
from `owned87_post8_ordered_reject_last_square`, or document exactly
which one the true producer does not imply. Only then bind the actual
first rejected branch. Do not jump from a retained LEAF to an
arbitrary hypothetical rejection.
