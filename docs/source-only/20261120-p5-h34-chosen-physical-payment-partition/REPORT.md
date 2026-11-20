# P5.6 → h34 — original chosen Q80 physical payment partition

Date: 2026-11-20.
Repository: UyNewNas/goldbach-formalization.
Independent h34 branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Verified incoming HEAD: `deaa68e37afea2ad1fdcaa80f11b0a4bb788ca77`.
Lean candidate source commit: `d16db2321b64c554169a319ab32986efb7997be9`.
Lean candidate source blob: `cb0bd2eead874dde01c040e5dec4982977f18f1f`.
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@`ba6ec11d800eccc54406490631895e174de85766`.
Frozen Lean: `leanprover/lean4:v4.33.0-rc1`; mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Increment: one real physical winning action, no candidate summation

Added `Part5OriginalH430ChosenPhysicalPaymentPartition.lean` (188 physical
lines, 12 theorem declarations including one private helper, two definitions).
It imports the previous `LiteralUniqueStrictWinner` candidate source and
preserves the unchanged literal `roundDecision`, `iterate`, exact
`literalIncrement`, and original 106 `Fin 106` bank-row indices.

* `buchstabPaid`: actual integer numerator increment if and only if
  the FINAL chosen physical action is Buchstab; otherwise zero.
* `bankPaid`: actual upper-table numerator increment if and only if
  the FINAL chosen action is the PARTICULAR original row `k : Fin 106`;
  every losing or tied offer receives zero.
* `retained_increment_zero`, `upper_cell_chosen_partition` and
  `lower_cell_chosen_partition`: precisely split every genuine Q80
  increment among the two exclusive action classes. Lower cells have
  no bank payment lane.
* `bank_paid_authentic_target`: any nonzero original indexed bank
  payment has the actual row target and the exact candidate-minus-old
  integer numerator, derived from previous winner provenance.
* `bank_paid_unique_index`, `buchstab_bank_payment_disjoint`:
  per generation and upper physical cell, at most one original bank
  row can receive a nonzero payment; it cannot coincide with a
  Buchstab payment. This is PHYSICAL winning-row uniqueness, not
  arithmetic selected-count root ownership.
* `bank_paid_nonneg`, `buchstab_paid_nonneg`: nonnegative
  payments derived from genuine monotone retention.
* `upper_430_chosen_account`, `lower_430_chosen_account`,
  `full_430_chosen_physical_account`: complete literal 430-round
  two-table physical numerator gain is partitioned among actual
  selected winners, no 106-fold overcount and no repeated retained
  mass.
* `chosen_physical_430_necessary_floor`: transfers the previously
  recorded raw physical net-growth necessity
  `1731100593645017731014086` into these disjoint actual-winner
  numerator accounts. It is NOT a new count lower bound.

These are proposed proof bodies, not executed Lean theorems. No new
numeric simulations, new heuristic physical support statements, or
alternative generator definitions were substituted.

## Explicit internal boundary

The physical `Choice` only labels the winning table action at one
iteration and physical site. It does NOT map that action injectively
or otherwise to the authentic original U3/U4 arithmetic `q/tag`
selected-count source, root weights, owner, allowed appearance/payment
multiplicity, first exit, full/selected/inherited gates, or rejection
filters. Those are still manuscript-INTERNAL and unproved.

The real frozen F endpoint envelopes, original seed/base payments,
all-action 430-step CLOSED-CELL induction, the seven-integral strictly
>=0.650 certificate (prior candidate only 0.590), manuscript PP/same-rho,
native history, Theta/count connection and shared 430+11 nested causal
refinement are also OPEN. This source is NOT an h34 closure.

## Toolchain, provenance and safe ownership

Checked active repository push permission, parent branch HEAD, prior
REPORT/REGISTRY/EXTERNAL_INPUTS and actual literal winner/increment source
before constructing this isolated packet. No P1.4/P3.6 or production
file was edited. No manuscript parameter, c/K, root norm 7/2,
row norm 12, true alpha, same-Q, CI workflow, toolchain or mathlib
version was changed; no forced push or main merge was requested.
No genuinely external analytic result was added.

Execution container check: git available; `lean`, `lake`, `elan`
absent and `git ls-remote` DNS resolution failed. The fixed import
closure is not staged here. Therefore actual Lean/Lake compilation,
kernel replay, transitive-axiom audit and finite Lean certification
were NOT performed. All new declarations remain candidate-source
UNCOMPILED; earlier source-only ancestors are also unverified here.
Static inspection or content hashes are not compilation.

Next: stage and compile pinned import chain and this module with the
existing toolchain, fix actual Lean errors if found, then derive a
real U3/U4 `q/tag` root/owner/first-exit and selected-count
multiplicity correspondence from these disjoint physical payments.
Do not relabel that consumer as external and do not substitute raw
physical numerator bounds for the original counting inequalities.

**完整h34稿内证明仍未闭合。**
