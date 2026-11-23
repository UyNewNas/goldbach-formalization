# Sorted dwell merge: independent static candidate

Status: **UNCOMPILED**. No Lean/Lake/compiler/kernel/type or axiom probe was run.
No live Member/main/native/P6/frozen source or build output was changed. The
sole Member source owner must adopt and validate this candidate.

Module: `ImbalancedChen.P2EnhancedSortedDwellMerge`.
Baseline SHA256: `df3f3826eacb18eaafa3bba4560ca343c853a0ebf2e306fdaa6c9366cd545a10`.
Candidate SHA256: `7ae4bcfdb999b7e7c62534f64bb3e25f50f611d59e0eef941afd559a72e41eec`.
The complete candidate and baseline are under their corresponding directories;
`candidate.patch` and `STATIC_RECEIPT.json` bind the comparison.

The main canonical source matches the baseline. Published project commits
`a398a6dc` and `b2c20e78` have exactly that same source hash. P6 has no canonical
file. Exact-path history was inspected for a later constant-family or beta
normalization fix; no already-published fix was identified. This search does
not claim an exhaustive all-branch/all-repository absence proof.

There are nine public theorems and one definition. Eight public theorem headers,
the complete `sortedUnion` definition, imports, numeric token sequence, and all
hypotheses remain byte-exact. No mathematical condition, constant, bound, label,
permutation, order requirement, or residual level was added or removed.

## Explicitly authorized header elaboration annotation

The original `cast_insertNth` header fails before its proof can elaborate.
Pinned mathlib `Data/Fin/Tuple/Basic.lean:780,852` has a dependent implicit
family `α : Fin (n+1) → Sort*`, with
`insertNth i (x : α i) (p : ∀ j, α (i.succAbove j)) j : α j`.
The original outer real annotation leaves the inserted natural family
underdetermined. Root explicitly authorized the following constant-family
syntax clarification:

```lean
(fun j => (p.insertNth (α := fun _ => ℕ) q v j : ℝ)) =
  p.insertNth (α := fun _ => ℝ) (q : ℝ) (fun j => (v j : ℝ))
```

The insertion position `p`, natural label `q`, natural tuple `v`, index `j`,
and cast equality are retained. This is the sole header change. The old header
did not elaborate; this report does **not** claim that an old elaborated type
was compared with the new type or proved kernel-equal. Both literal headers
and their hashes are recorded separately in `STATIC_RECEIPT.json`.

The pinned nondependent permutation bridge is
`GroupTheory/Perm/Fin.lean:288`,
`cons_comp_cycleRange {α : Type*} (a : α) (x : Fin n → α) (p : Fin (n+1))`.
Its existing proof is retained; the fixed Nat/Real families specialize that
API to the intended tuples.

## Remaining proof-body corrections

* Add `Function.comp_apply` to the two existing `simpa only` calls in
  `dwell_ofFn_iff`. The log shows casts composed with `v` surviving on one
  side of the prefix product. The pinned `List.prod_take_ofFn` theorem
  (`Algebra/BigOperators/Fin.lean:728`) returns the same actual indexed
  product, with no change to its range or weights.
* In the empty-residual antitone proof, explicitly change the beta-reduced
  real inequality to the casts of `old[j.val]` and `old[i.val]` before the
  existing `exact_mod_cast`. The local tuple is precisely that old list.
* Replace the length `simp only` before the inserted witness with
  `rw [List.length_append, List.length_singleton, ← Nat.add_assoc]`, then use
  `p.insertNth (α := fun _ => ℕ) q v`. The existing log still expects
  `Fin (old.length + (residual ++ [q]).length)` after the old simplification;
  the explicit rewrite transports the binder to the insertion's
  `Fin ((old.length + residual.length)+1)`. This is a candidate implementation,
  not a compiler-confirmed claim.
* In `sortedUnion_well`, give the antitone consequence the explicit real
  inequality type `(v j : ℝ) ≤ (v i : ℝ)` before `exact_mod_cast`.

These changes only expose beta reductions and existing list-length equalities.
The insertion continues to use the actual natural occurrence and the proven
sorted-insertion position. The original residual atom may still interleave
with arbitrary old slots; no append-order or new ceiling premise is introduced.

## Nov6 manuscript scope

`coefficient-appendix.tex:22–45` specifies the decreasing full and selected
square conditions. Lines 88–98 retain the marked residual level and original
parent ceiling. Lines 150–185 insert whole slots using the existing square
bounds and original capacities. The candidate retains `old.prod * R ≤ Q`,
uses exactly `R=Q/old.prod` in the residual-level theorem, proves a permutation
of `old ++ residual`, and preserves the exact arithmetic product. It remains
a support/geometric theorem and adds no distribution or signed-density claim.

The API source hashes and pinned Lean/mathlib versions are recorded in the
static receipt. `FAILURE_EXCERPTS.txt` preserves all six reported failures.
