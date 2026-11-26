# P2.4 finite A: equivalent kernel table representation

## Intent and existing authorization

Continue the already authorized P2.4 completion, retaining the frozen manuscript
and all original mathematical interfaces. The accepted symbolic prerequisite
is 321 modules. At source f5f4dc1a6934f9412cc8f4918ed2c0e1ff05d3a4,
finite A attempt 02 is running through the unchanged original checker.
The proposed fallback is an implementation choice for the same proof
obligation, not a new endpoint or a request to change the user's scope.

## Observed problem

The original rfl failed because locked Lean's Rat arithmetic is irreducible
to default meta-level unfolding. A runtime-only observation computes exactly
the archived rational, but has no proof credit. Both an all-transparency rfl
and decide +kernel reached their separate 120-second diagnostic limits.
The full original A attempt is still running and must retain its own result.

Locked Lean implements the logical Array through List. The current builder
performs 196608 pushes and reads nodes.size at every update; push, size and
lookup therefore expose growing list spines in the kernel. Runtime extern
array implementations do not establish kernel performance.

## Approaches

1. Keep the one-line decide +kernel repair and use the existing full budget.
   This is the smallest change and is already running. It remains the first
   acceptance opportunity; a short diagnostic timeout is not final failure.
2. Add a private balanced map representation to A's proof, prove that its
   total lookup equals the original sourceState, then transport the same
   closed equality. This adds generic proof obligations but removes growing
   list spines. It is the assistant's selected fallback if the direct route
   fails or demonstrates a concrete impractical resource boundary.
3. Use the existing cbv/decide_cbv evaluator without representation changes.
   Locked cbv has a separate default 100000-step bound and no verified
   constant-time push/size path. No evidence presently makes this a stronger
   candidate for the 196608-step source builder.

No method may use native_decide, unchecked results, new axioms, stored table
or first/tail literals as an evaluator, source substitutions, or relaxed gates.

## Minimal construction

Keep the original A theorem names and complete types, the archived rational,
the original fastFixedUpper, historicalUpper, scale, firstBounds, nodeUpdate,
sourceState, Array implementation, all existing parameters, and all local
resource options unchanged.

Use private helpers in the existing A module; do not add a project module.
The project closure remains exactly 324 with the existing ordered fingerprint.
The carrier is Std.TreeMap.Raw Nat Node compare, with an empty tree and
initialNode as the total lookup default. Carry the next natural index
explicitly, starting at 1; never derive it by traversing a data structure.
Each step inserts nodeUpdate g next (reader old) at next.
The complete builder still performs 12 * 16384 updates.

Prove two generic invariants before any closed specialization:
- the map satisfies Raw.WF;
- its total reader equals sourceState g n after n updates.

The exact locked APIs are Raw.getD_emptyc, Raw.getD_insert, WF.emptyc,
WF.insert and Nat.compare_eq_eq. These support insertion's global reader
equation, including all out-of-range indices. No finite-range hypothesis
may replace the current total-function refinement.

Use those invariants together with the already accepted tableArray_lookup
to identify the dInteger query at 10. A small private function parameterized
by this integer must retain the original tailInterval and fixedUpper formula
in the original operation order. Prove the formula transport generically,
then specialize. The closed proof computes the balanced table and the
original first/tail arithmetic and proves the same archived rational equality.
No observed numerical component is used as a substitute definition.

## Execution and verification

First review the representation/refinement proof design. A generic isolated
Std-only proof prototype may use P3's existing pinned Lean and a new diagnostic
output directory, without cloning, migration, dependency rebuilding or native
qualification. It receives no canonical acceptance credit and must not mutate
P2 source, records or objects. It is a proof of the actual representation
invariant, not a small numeric benchmark.

Production changes, if needed, remain a reversible source-only commit.
Independently compare all original public theorem headers and definitions,
and check that any added import is already covered by the existing locked
runtime snapshot. Preserve the original checker and complete module scope.
Validate the actual new source through zero-budget symbolic prerequisites
followed by the original A gate, including native pre/post checks.

Successful compilation of private helpers does not accept the closed equality.
A requires complete 102/102 with exit 0, no failed/pending modules and the
normal native postcheck. B and W remain separate subsequent original jobs.
The complete owned audit must include all new private/generated declarations,
with only propext, Classical.choice and Quot.sound allowed transitively.

## Remaining risks

A balanced map reduces table access depth but does not promise a particular
kernel runtime. Raw map balance and comparison operations must themselves be
total and available to the kernel. Proof transport must not accidentally force
the original Array before using the generic equality. Deep recursion and the
actual closed arithmetic still require measured production evidence.

This design addresses A only. It supplies no unrun B endpoint or whole
functional credit, and it does not enlarge the manuscript scope to a complete
Python operational refinement or claim crossing the 6.809 stop target.
