# P3.5: fixed C4 test family and regular-envelope adapter

The user requests completion of P3.5 for the frozen 20261106 manuscript.
Continue the accepted branch `codex/p3-5-full-kernel-20261125` at
`ce38b7e8a5a2e7d501afe3a0213e08641dfbc777`; do not repeat accepted Fourier,
Cauchy, cumulative-shell or exhaustion proofs. Preserve the original physical
range, both signs and the printed normalization.

## Findings and approach

The previous accepted test-seminorm component leaves the derivative order of
the external test estimate open. The manuscript-cited Drappeau Lemma 4.4,
equation (4.12), specialized to weight zero `kappa=0`, explicitly requires
derivatives only through order four and
uses transforms (4.9)--(4.11) with the existing native normalization. For the
fixed support ratio `[Y/16,16Y]`, unit normalized derivatives give a uniform
regular envelope proportional to

`L(Y) * min 1 ((1 + Y*sqrt Y)/(1 + |t|^3))`,
where `L(Y)=(1+|log Y|)/(1+Y)` and `Y>0` is arbitrary.

1. Prove the actual period-64 tests belong to that unit C4 family after
   division by their positive, mode-dependent normalization. Pay that
   normalization with the existing degree-four actual Fourier theorem.
2. Translate the cubic envelope into the already proved shell consumer with
   independent low and high constants. Use `K=max 1 (2*Y)` and specialize the
   consumer's auxiliary mixed-tail parameter to zero. Bound the total tail
   by `64*E` and the whole cut by `65*E*pairBudget`; then use the existing
   geometric-window comparison for the factor `260`.
3. Reuse the same positive-measure cutoff and exhaustion theorems for global
   integrability. No convergence assumption replaces a proof of integrability.

The alternative of importing fixed-mode Schwartz decay fails the uniform
quantifier order. Proving an outside Bessel theorem is excluded by the user's
scope. The chosen route formalizes only the manuscript's normalization and
envelope conversion; the external theorem remains explicitly registered.

## Boundaries

The external C4 estimate is not a new Lean axiom and is not asserted proved.
The six native Y04 source dependencies currently absent from the checked
local files, archive members and GitHub scope remain a separate source
blocker. These adapters alone cannot turn the full P3.5 node green. Any result
still requiring actual automorphic rows, their identification, or the
external estimate must state that boundary exactly.

No `sorry`, `admit`, new `axiom`, `native_decide` or `unsafe` is allowed.
No modification of pinned dependencies or previously accepted theorem types.
New source is authored locally. The P3 and fallback MCP sessions are currently
terminated. P1 subsequently provided the exact pinned Lean, Mathlib and
Goldbach cache; compile in a separate P1 checkout, binding actual imported
object paths and hashes. The local isolated bootstrap remains a recorded
fallback, not another full acceptance pass. Push verified work to the existing P3.5 branch;
P3 Draft #12 only receives a whole secondary node after genuine closure.
