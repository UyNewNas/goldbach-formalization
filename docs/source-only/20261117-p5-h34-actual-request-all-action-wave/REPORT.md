# P5.6 → h34 — actual generated-request all-action wave and selected retention/Buchstab steps

Date: 2026-11-17.
Latest verified previous baseline: `2a922a7794d74a6c8ad235ee4c09cd48d720fce5`.
Mathematical source commit: `2e2e4a8a6119d5f97673b793eeff6667ba4d653a`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.

Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Non-duplicate manuscript-internal increment

Previous packets reconciled original U3/U4 tagged counts at true Fin positions, including
U4 double-tags, further q/tag receipts, other true-Fin receipts, and four outside-source
rejections. They did not close the causal owner or the requested ALL-action program.
This packet deliberately does **not** add another arbitrary original-source filter,
tagged-receipt identity or external analytic lemma. It works with the pre-existing
actual `children`, `history`, `mark`, `Selected`, `edgeRow` and `edgeValue`
source, and makes the all-action recursion explicit.

File: `Part5OriginalH430ActualRequestAllActionWave.lean` (source-only, 172 lines).

* `waveAccount`: entire actual generated request history, with each original
  occurrence's literal positive edge-product mark and correct remaining generation;
  test accepts current Request, preserving specified-cell versus scalar read.
* `wave_zero`: exact generation-zero seed; not mapped to predecessor 429.
* `wave_successor`: exact all-action recurrence for every generated request:
  W(g+1,r) = V(g+1,r) + sum_{e in children(N,Q,g,r)}
  edgeWeight(e) W(g,nextRequest(r,e)). The current node is counted once,
  the only expanded edges are the actually selected ones, and list-path
  multiplicities survive all flatten/map/sum reindexings.
* `actualStep` and `step_exterior_zero`: exact literal chosen next-step
  value and zero next-step term if the requested resolver returns none.
* `step_retained`: selected retention consumes the **specified** retained
  floor cell, not a scalar-owner substitute.
* `step_buchstab`: the selected Buchstab branch is the **actual strict
  prime-child carrier** from `singleChildren`, each with weight one and
  its concrete scalar successor request; no Buchstab integral is substituted.
* `step_bank`: only the actual selected one of the 106 banks is read,
  preserving all W1/W2 fixed/single/pair coefficients.
* `step_row_value`: the chosen child row evaluates to the literal next-step
  request value; it is not an error bound.

All assertions are Lean **candidate proof bodies** rather than compiled theorems.

## Mathematical boundary

This proves no fresh numerical bound and cannot upgrade the prior
`uniform_level_bank_supply` to an all-action quantitative count inequality.
The already existing source has scalar Buchstab estimates on separate
catalogue families; those have NOT yet been transferred to this concrete
request/occurrence history under both cell and scalar read semantics.
The actual retained/Buchstab payment, CLOSED-CELL count induction,
generation-wise Theta charges and zero-mass cases remain unproved.

In particular, exact recurrence W=V+children(W) is a finite structural
identity, not a target-equivalent induction hypothesis or a licence to
identify W with the original full/selected/inherited U3/U4 count source.
Owner cardinality, original roots' 7/2 weights, signed Euler and U4 duplicate
receipts, source rejection lanes, PP/same-rho, floors/seeds, native history
and the common 430+11 nested causal refinement all remain manuscript-internal.

## Verification

GitHub API write succeeded for mathematical source commit. It must be read
back and its Git blob and compare checked after the metadata commits.
Local `lean`, `lake`, `elan` are absent; native `git ls-remote`
failed to resolve github.com; previous source-only modules are not installed
under the `ImbalancedChen/` import path. **No Lean compilation was run**,
no kernel replay or transitive axiom audit ran, and inherited finite tables
are `UNEVALUATED`. Text checks never imply type-checking or proof validity.
No green node is claimed.

Pinned manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
Pinned toolchain: `leanprover/lean4:v4.33.0-rc1`.
Pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
Original c/K, norm7/2, row norm12, actual alpha, physical Q, and
430+11 budget unchanged. P1.4/P3.6 and CI/workflows/dependencies untouched.

## Next concrete action

Stage the pinned transitive import closure and compile the new file plus
`RequestedBranches` and `RequestedHistory` incrementally. Fix any actual
Lean errors in THIS task's source only. Then instantiate the existing
Buchstab absolute/row-mass supplier at `Selected` on the literal
request generation; combine with retained cell equality, bank local
supply and zero-mass cases into a genuinely quantitative CLOSED-CELL
all-action induction before touching any further source-count identities.
