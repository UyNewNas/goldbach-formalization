# P1.5 actual historical first-disagreement bridge

Status: **STATIC SOURCE REVIEW; NEW BRIDGE NOT ELABORATED**. This review adds
no normal-compiler or kernel acceptance. It does not close the signed medium
estimate, `RestrictedMediumTarget actualF`, or P1.5.

Repository baseline: `UyNewNas/goldbach-formalization`,
`3c9bc8fbb8dcd8adc9e4f69c53aab7f41b8d5508`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes`,
`a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/`.

## 1. Concrete next step

The accepted `P1OriginalHistoricalCoefficientDictionary` identifies the
original physical signed coefficient at its unique small/rough factorization:

```text
trueDDeltaRho(a*b) = roughMaskDelta(b) * attachedMobius(a,b).
```

Here the Rosser member inside `attachedMobius` remains the original member
chosen from the rough Möbius sign. Changing the retained policy changes the
rough support mask; it does not choose a new small coefficient.

The new local candidate `P1OriginalHistoricalFirstDisagreement.lean` connects
that accepted identity to the existing generic common-tree witness. It has
two public conclusions:

1. If the actual complete-modulus coefficient at `d` is nonzero, there are
   `a` in the original small support and `b` in the union of the two actual
   rough supports, with `a*b=d` and a nonzero rough-mask change at `b`.
2. The same factorization has an actual state in the common tree of the two
   `oddFirstExitPolicy` policies, on the same target-deleted rough carrier.
   The state has `positive=false`, the two original odd policies disagree
   on its literal stored prefix, the reverse prefix is a sublist of the
   actual processing carrier, and every prime in that prefix belongs to
   `d.primeFactors` for the **complete original modulus**.

No new discrepancy estimate, cap equality, atom factorization, collision
budget, or medium-target premise is assumed. The proof reuses the generic
first-disagreement theorem; it does not copy its list induction. The new
content is the passage from the attached actual coefficient through its
rough mask to the real common history, including the lift from factors of
`b` to factors of `d=a*b`.

The bridge source is 5533 bytes, SHA-256
`edb45d7c44440fdb68937fc0931c95c7a7ab0532ec26b1f20002b8669c8700a2`.
It contains 2 public and 2 private source declarations. These are source
counts, not kernel-owned declaration counts.

## 2. Why the four existing modules are needed

The required API is
`p1_coefficientDifference_ne_zero_firstDisagreement`, in
`P1HistoricalBoundaryPolicyDifferenceSupport`. Its conclusion gives an exit
on the actual common tree and a factor history of the same modulus. The
lower modules inspected do not provide this witness. Importing a lower
module and copying the Boundary induction would duplicate existing work.

| Order | Existing module | Source bytes | Source declarations: public / total | Purpose |
| --- | --- | ---: | ---: | --- |
| 1 | `P1SignedExitPartition` | 15982 | 14 / 15 | Enumerates signed exits with their literal residual carriers; groups occurrence-preserving sums by actual rank and history. |
| 2 | `P1SignedExitPolicyComparison` | 17805 | 16 / 17 | Cancels the common retained tree and retains both new-only and old-only signed continuations. |
| 3 | `P1SignedExitCoefficientDifference` | 17943 | 23 / 23 | Uses one fixed Möbius coefficient, cancels its overlap, and relates nonzero difference to the symmetric difference of supports. |
| 4 | `P1HistoricalBoundaryPolicyDifferenceSupport` | 20316 | 15 / 17 | Follows a one-sided valid selection to its actual first disagreement and preserves its prime-factor history. |

All four original files have now been read in full. The finite identities
preserve skip branches, both signs, restored old exits, actual order and
actual tails. No mathematical declaration change was identified by this
static review. Compatibility with the current Lean environment remains an
elaboration question; original bytes should be tried first.

The four files total 72046 bytes. Including the new bridge gives 77579
bytes, 70 public / 76 total source declarations. The source token scan finds
none of `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe`. That scan is
not a substitute for compilation or kernel checking.

The direct external project boundaries of the four-module chain are:

- `FirstExitHistoricalLevels`
- `FirstExitGenericModuli`
- `PhysicalUpperWeightBridge`
- `FirstExitValidSelection`
- `HistoricalPrefixCertificate`

All five occur in the accepted Dictionary context with source, object and
trace hashes. The combined project closure is the accepted 289-source
Dictionary closure plus four existing source-only modules plus the new
bridge, for 294 project sources. The acceptance driver still has to verify
the actual transitive import graph and live dependency pins; this review
does not treat set inclusion as a new acceptance.

## 3. Original source identity and bounded acceptance history

Exact original sources are preserved under `reference/`. Their original
manifest is `docs/source-only/20261024-code-only/source-manifest.json`, Git
blob `a239999f01fa66a7bc9270bf4ba7ad3ea08be411`. Each original entry explicitly
has status `SOURCE_ONLY_UNCOMPILED_ZERO_PROOF_CREDIT`. The four current local
SHA-256 values and byte counts exactly match that manifest.

The exact Git path history of each file has one returned original commit,
`e3383270bcdf1a22ce32ff379c0695f3729978cc`, dated 2026-10-24T09:00:27Z. Its
message explicitly calls the checkpoint source-only and records no Lean,
lake, checker, numerical replay, audit, or CI execution.

No same-source acceptance was found in the following bounded searches:

- `verification/proof-continuation/2026-10-15/manifest.json`: 190 original
  owner entries and 3661 evidence-file entries.
- `docs/verification/20261123-blue-compilation/README.md`.
- `docs/PROOF_STATUS.md`.
- `docs/PROOF_CONTINUATION_2026-10-15.md`.
- `docs/CURRENT_MANUSCRIPT_MAP.md`.
- `docs/verification/20261123-blue-compilation/reuse-observations-iteration2/blue-member-four-commit-reuse-inventory-20261123.json`.

This is a bounded negative result, not an assertion that no acceptance
could exist anywhere. Fresh parent-owned P1 readiness inventories also
record no live source/object/trace/owner for the four modules. The original
manifest status, exact source history and bounded acceptance searches are
preserved in `CHAIN_BINDINGS.json`; live absence alone is not used to infer
historical non-acceptance.

The recommended first new owner is **`ImbalancedChen.P1SignedExitPartition`**.
Its only project import is accepted `FirstExitHistoricalLevels`; its other
direct import is `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`.
The sibling probe should check the actual transitive closure and reuse all
accepted objects. It should neither build dependencies nor recompile the
accepted Dictionary or Variation owners. Original source and every failed
attempt must remain retained if a proof-only repair becomes necessary.

## 4. Manuscript basis

The finite first-exit argument is in frozen `argument.tex`,
`eq:current-upper-exit`. The proof partitions excluded divisors by their
first excluded prefix, preserving the actual remaining smaller-prime
subsets. Comparing two retained trees uses the common prefix before the
first test on which the policies differ; the four existing modules express
that finite signed decomposition.

The attached coefficient basis is in frozen `coefficient-appendix.tex`,
the paragraph after `coef:tensor-identity`: the sign determines the small
beta member, and disjoint small and rough prime universes make their
decomposition unique. The accepted Dictionary supplies that attachment
identity. The new bridge composes it with the finite first-exit witness;
it does not supply another formulation of the analytic proposition.

Frozen manuscript Git blobs are
`90234d94460f1d7d59982635d7bf54c9b19250da` for `argument.tex` and
`10f3e2efb2074a9b97148a5151956e1d450be13f` for
`coefficient-appendix.tex`.

## 5. Exact remaining mathematical boundaries

The current literal historical medium is the existing `historyMedium` in
`P1OriginalHistoricalExactMediumResidual`. It evaluates the same
`trueDDeltaRho` on `historicalModuli`, which filters the union of the two
physical supports using the **complete modulus**:

```text
panModulusCutoff N B < d  and  d < N^(599/1000).
```

The original comparison uses old `S false`, fresh `R false`; the original
saving uses old `eight false`, fresh `six false`. These are not the
finite-fallback policies fixed by `P4BOriginalCollisionWords.Params`.

Three substantial connections remain after the new finite witness:

1. **Whole-atom tensor identification for these actual policies.** Frozen
   `argument.tex` immediately before the HB discussion and
   `coefficient-appendix.tex` before `coef:tensor-identity` require the three
   groups to be fixed on whole atom boxes using endpoint data and the
   medium length. The proof cannot select a different grouping for each
   arithmetic tuple or discrepancy sign. A first-disagreement witness gives
   provenance of a nonzero coefficient; it does not construct that signed
   atom family, its endpoint gates, or the complete-modulus filtering.
2. **The same physical/free collision identity and payment.**
   `coef:tensor-identity` keeps the normalized factorial scalar and original
   beta attachment. `coef:collision` keeps global squarefreeness in the
   physical coefficient and only removes it in analytic comparison, with
   a divisor-factor bound of size `(N+D_*) N^(-eta_0+o(1))` and the exact
   complete-product case included. Existing collision APIs keep their own
   original Params; they do not identify an arbitrary historical
   `old/fresh` coefficient with `products P / free P`.
3. **Uniform signed medium estimate on the full actual family.** Frozen
   `prop:current-medium` fixes the family parameters before the bound, uses
   three separate one-bounded modulus sequences, the original four strict
   geometric inequalities, and auxiliary-coprimality SW uniform in every
   auxiliary `k,q,b_0`. The target is
   `forall A>0, exists C>0, exists x0>1, forall i`, with `C,x0` chosen
   before the actual chart, row, complement, mode and owner choices, and
   `norm(signedError(actualF i)) <= C*scale/(log scale)^A` above threshold.
   Neither coefficient unit bounds nor the first-exit support witness give
   that estimate. The recorded general source-to-spectral route still
   needs the actual completed variable, pointwise kernel identification,
   and a full-phase estimate for the same remaining array.

The existing U06 theorem is a genuine restricted payment for the
short-head, low-first rough-rank-three subcomponent, in its original
`products/free` channel. Its terminal bounds the difference between the
free row and an explicit remaining row. Longer fibres, other words and
the retained tail remain. The stronger shared-boundary inequalities used
for that payment do not follow from the four basic medium gates alone.
Reusing U06 therefore requires the exact original historical component
identification, followed by preservation and payment of its complement.

These are unclosed formal provider obligations, not a claim that the frozen
manuscript theorem is false. No new hypothesis asserting one of these
missing conclusions has been introduced in the bridge.

## 6. Local evidence files

- `CHAIN_BINDINGS.json`: exact source identities, bounded history records,
  import boundaries, accepted Dictionary context pins, and bridge identity.
- `STATIC_REVIEW_DECLARATIONS.json`: lexical declaration inventory, file
  hashes, byte counts, and forbidden-token scan; explicitly static only.
- `P1OriginalHistoricalFirstDisagreement.lean`: new source-only bridge.
- `reference/P1SignedExitPartition.lean`,
  `reference/P1SignedExitPolicyComparison.lean`,
  `reference/P1SignedExitCoefficientDifference.lean`, and
  `reference/P1HistoricalBoundaryPolicyDifferenceSupport.lean`: unchanged
  original source-only bytes.

Accepted Dictionary source/acceptance remains the original
`040d46058821746c69c5183b3f6c22792287c4ba` record. No compiler job, Git push,
or accepted-source edit was performed by this review agent.
