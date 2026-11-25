# Saving19 moment symmetry candidate

This directory is an isolated source candidate. Its scripts do not install
production sources or submit P1 jobs. The three pilot owners have a separate
minimal publication manifest; the parent owns their publication and acceptance.
The optional complete guard/facade overlay remains separate from that pilot.

## Scope and status

The candidate replaces repeated index-specific polynomial enumeration by a finite
permutation argument. It preserves the original nine barycentric nodes, the
duplicated marked node, the degree-at-most-six public guard, every original public
statement, and the physical simplex interpretation.

`P2OriginalSaving19MomentFiniteReindex` has one successful local normal compilation
against the exact project Mathlib pin. A second isolated diagnostic verifies the
exact copied `duplicateH` definition and candidate recurrence proof, plus the exact
factored Core right-hand side and its cast/factor transport. These are local
diagnostic results, not P1 kernel or full-owned acceptance. The actual production
Core-importing Symmetry owner, arbitrary-index pilot, complete guard consumer, and
optional facade have not been compiled by this work.

## Files

| Module suffix | Purpose | Direct project imports |
|---|---|---|
| `MomentFiniteReindex` | Reindex the weighted antidiagonal sum without enumeration | None; two Mathlib imports |
| `HigherMomentsSymmetry` | Obtain integratedPower equivariance from Core; prove duplicateH equivariance by induction | Core and MomentFiniteReindex |
| `HigherMomentsSymmetryPilot` | Degree 2 with arbitrary marked index, obtained from the accepted index-zero leaf | Symmetry and LowBoundary |
| `HigherMomentsGuardBySymmetry` | All original degrees 0 through 6, using the seven index-zero leaves | Symmetry, LowBoundary, K3I0, K4I0, K5I0, K6I0 |
| `HigherMoments` | Optional facade overlay; only the integratedPower guard proof and its provider imports change | MomentFloorConsumer, Core, GuardBySymmetry, AuthorK0 through AuthorK6 |

`prepare_overlay.py` constructs the optional facade from the pinned existing
facade and checks all 36 original public declaration headers. All original
definitions and structure fields remain byte-identical. The other 29 existing
facade declarations are byte-identical to the active partition candidate.

It does not generate or overwrite the three pilot sources. It pins Symmetry to
SHA-256 `5425985922dae867d1a1be2903c2def751187894373d700ca3a8a62b3346e16d`,
including the explicit final `rfl` in `duplicateH_perm`, before regenerating the
optional facade metadata. Core and LowBoundary are never written by the script.

## Proof of finite reindexing

For a permutation `σ : Equiv.Perm (Fin 9)`, the forward map on the exponent
antidiagonal is `e ↦ e ∘ σ.symm`; its inverse is `e ↦ e ∘ σ`.

1. `Equiv.sum_comp` preserves the exponent sum `k`. The support condition in
   `mem_piAntidiag` is automatic on `Finset.univ`.
2. Function extensionality and `σ.symm (σ r) = r` give injectivity. The explicit
   inverse gives surjectivity.
3. The marked coefficient satisfies `(e ∘ σ.symm) (σ i) = e i`.
4. `Equiv.prod_comp` preserves the monomial product under the same reindexing.

The resulting theorem works for an arbitrary coefficient function `w : ℕ → A`,
with only `AddCommMonoid A` and `CommMonoid A` needed. The Core wrapper specializes
it to `A = ℝ` and `w n = ((n + 1 : ℕ) : ℝ)`. The already accepted
`integratedPower_eq_factored` supplies the unchanged factor `k! / (k + 9)!`.

For `duplicateH`, strong induction on the degree uses only the original recursive
equation, the smaller degrees `k - j.val < k + 1`, and invariance of each power sum
under `Equiv.sum_comp`. The marked node becomes `y (σ i)` on both sides.

Finally, instantiate `σ = Equiv.swap 0 i`. Its value at zero is exactly `i`, so an
existing index-zero guard applied to `y ∘ σ` gives the original guard at arbitrary
`i`. No guard identity, final saving, or extra estimate is a theorem parameter of
the pilot or complete guard consumer.

## Existing API reuse

The exact local Mathlib checkout is:

```text
/workspace/library-files/p34-proof-work/.lake/packages/mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1
```

The existing project source search found no `integratedPower` or `duplicateH`
permutation supplier. At this Mathlib pin, `Algebra/Order/Antidiag/Pi.lean` has no
general permutation/comp closure lemma for `piAntidiag`; its Bool equivalence,
scalar-map, and symmetric-power APIs do not provide the needed marked reindexing.
The candidate therefore adds only this finite specialization, using:

```lean
Finset.mem_piAntidiag :
  f ∈ piAntidiag s n ↔ s.sum f = n ∧ ∀ i, f i ≠ 0 → i ∈ s

Finset.sum_bij
  (i : ∀ a ∈ s, κ)
  (hi : ∀ a ha, i a ha ∈ t)
  (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
  (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b)
  (h : ∀ a ha, f a = g (i a ha))

Equiv.sum_comp (e : ι ≃ κ) (g : κ → M) :
  (∑ i, g (e i)) = ∑ i, g i

Equiv.prod_comp (e : ι ≃ κ) (g : κ → M) :
  (∏ i, g (e i)) = ∏ i, g i

Equiv.swap_apply_left (a b : α) : Equiv.swap a b a = b
```

The sum APIs are the existing `to_additive` versions of the product declarations
in `Algebra/BigOperators/Group/Finset/Defs.lean`. Calls use the fully qualified
`Equiv.sum_comp` and `Equiv.prod_comp` to distinguish the separate
`Equiv.Perm.*_comp` finite-support variants. Source paths and hashes are recorded
in `SYMMETRY_STATIC_MANIFEST.json`.

## Local diagnostic

The isolated diagnostic directory is `/workspace/p26-local-checks/symmetry/`.
`FINITE_REINDEX_LOCAL_DIAGNOSTIC.json` records the copied source hash, exact command,
working directory, read-only dependency paths, runtime version, output hash and
empty normal log. The first run completed with exit code 0 in 5.472 seconds.

```text
Lean 4.33.0-rc1
commit 62eed1db4d67327ec8120be05f1a1b0847d74561
flags: -j1 -M4096
source SHA-256:
ef69493b03eea3c013fe645f20f5a70b4348e64ec3c59aef1a0e325afa42e902
```

The diagnostic reads existing Mathlib objects and writes only under its own
directory. It imports no Saving19 Core object, does not rebuild any library, and
does not establish the remaining Core wrapper or the P1 acceptance gates.

A separate local `#print axioms` inspection completed with exit code 0 and reports
exactly `[propext, Classical.choice, Quot.sound]` for the finite-reindex theorem.
Its command and log are retained in `FINITE_REINDEX_LOCAL_AXIOMS.json` in the same
diagnostic directory. This inspection is not a replacement for P1 full-owned
verification of the complete proposed source closure.

`CORE_SHAPES_LOCAL_DIAGNOSTIC.json` records the second diagnostic. It copies the
accepted Core's entire `duplicateH` declaration byte-for-byte and the candidate's
entire `duplicateH_perm` declaration byte-for-byte into an isolated namespace.
It also copies the exact right-hand side of `integratedPower_eq_factored` into a
local definition and checks the same wrapper tactics against it. No old project
supplier or Core dependency chain is imported or rebuilt.

That diagnostic completed with exit code 0 in 1.936 seconds, under the same
`-j1 -M4096` flags. Both local theorems report exactly
`[propext, Classical.choice, Quot.sound]`. The initial failed attempt is retained
under `attempts/core-shapes-01/`: it left only the definitional equality between
`(y ∘ σ) i` and `y (σ i)`. The final explicit `rfl` closes that goal; no mathematical
statement, definition, or runtime limit changed.

## Minimal pilot publication scope

`PILOT_SOURCE_MANIFEST.json` lists exactly these three new owners in order:
`MomentFiniteReindex`, `HigherMomentsSymmetry`, `HigherMomentsSymmetryPilot`.
It binds the existing accepted Core and LowBoundary hashes without regenerating
their sources. `PILOT_SOURCE_INPUTS.json` separately records each complete project
source closure against one observed coherent Git commit. The respective source
closure counts are 1, 218, and 220.

The complete `GuardBySymmetry` and facade are explicitly outside this pilot
manifest. The parent should use a new three-owner scope with the unchanged
normal/context/kernel/full-owned machinery; the old 68-owner manifest validator
is not the scope for these new modules.

## Proposed later integration

First compile/audit `MomentFiniteReindex`, then `HigherMomentsSymmetry`, then the
degree-two `SymmetryPilot`, reusing the accepted Core and LowBoundary objects.
Only after that diagnostic route is accepted should the parent consider the
optional facade arrangement.

The complete arrangement needs the same index-zero leaves for degrees 0 through
6. LowBoundary already carries degrees 0, 1, 2 at index zero, together with two
already accepted extra low-degree leaves. Degrees 3 through 6 use their existing
I0 provider files. The seven author/Newton providers stay unchanged.

The resulting moment proof closure contains 17 modules instead of 68, excluding
the standalone diagnostic pilot. This removes 54 unused index-provider modules
from the facade's imports and adds three finite-reindex/transport modules. It
does not lower the cost of the single K6I0 enumeration; that provider still needs
its own successful ordinary/kernel/full-owned verification.

This is an expression and finite-reindexing change. The original manuscript
`num:simplex-moment` formula, its `d = 8` specialization, the real integral
semantics and the downstream 28,918-row archive remain unchanged.
