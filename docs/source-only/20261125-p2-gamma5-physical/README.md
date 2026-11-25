# Actual Gamma5 physical extension and mixed Euler budget

## Verification status

The corrected physical extension and reused scalar log-floor core passed
strict compilation, independent `leanchecker` replay, and full owned
declaration audits in job `f1c4e308531844908cd1875e245dcf69`:

| Module | Owned declarations | Accepted source SHA256 |
|---|---:|---|
| `P2FiniteMarkedGamma5PhysicalExtension` | 35 | `f54dfd8c30c3c0bb1982ac09bb91d7c39f7ed01342d32f1e18b63eb15e3395a5` |
| `P2SmoothLogFloorDerivativeCore` | 4 | `bc9fd90fadf2c967df05e4e9a0be2491d642b63369f060cd2aed25bee6c7b472` |

`P2FiniteMarkedGamma5PhysicalEulerBudget` passed strict compilation,
independent stock replay, and a full audit of 20 owned declarations in job
`f0e65e6421f44d6bbfcd8e9132d99fc4`. Its accepted source SHA256 is
`2d5bf41aabe57cf035ad443f9b4ae44608aa3f4d0d9636494413f7f746c426ac`.

The conjugacy core and actual Euler-word bridge are both fully accepted.
Job `24e632b1c7794c4c8fede0d6fa606e78` exited zero and completed independent
replay and full owned-declaration audits for both final source hashes:

| Accepted module | Source declarations | Audited owned declarations | Accepted source SHA256 |
|---|---:|---:|---|
| `P2OriginalEulerWordConjugacyCore` | 17 | 25 | `29b4397331ac573e1da3c5d3eb972790f58bc9f12f21834dfe4e1398d0f73d8f` |
| `P2FiniteMarkedGamma5EulerWordBudget` | 17 | 19 | `761063d2147c7de6dc02bf6f616d1c4cb7be6d6f8da26f86c5e41c74755782a5` |

The bridge's strict normal compilation took 5.101 seconds, with 11 project
modules in its closure and 10 reused. The same final core hash had passed
strict normal compilation in 7.808 seconds in job
`cbd7db23744d41f0ace2787983e98cd6`, before its independent replay and full
owned audit passed in the final acceptance job above. The source counts
are the 17 explicit declarations in each module; the owned counts also
include Lean-generated declarations belonging to that module.

Accepted Lean bytes remain unchanged. Their source headers retain the
initial submission labels; this README and the receipts record the later
acceptance without altering those checked bytes.

The earlier logarithmic profile core and its `profile_tensor_budget` were
already independently accepted. These lightweight receipts do not validate
the original heavy arithmetic plateau or the complete marked-family proof.

## Exact physical function

The new domain is

```lean
Slot k r := Fin k ⊕ (Fin 2 ⊕ Fin r)
PhysicalPoint k r := Slot k r → ℝ
```

Every old-prefix prime, both fresh primes, and every rough-tail factor keep
separate coordinates. Repeated values preserve their factors. Either old
rank `k` or tail rank `r` may be zero: the old product is then one and its
logarithm zero, and an empty rough tail still represents the unit quotient.

`logPoint` forms the old-prefix coordinate by summing the individual old
logs. `safeLogPoint` replaces each slot log by
`log (positiveArg (b/2) (x i))`. The accepted original `positiveArg` and
`floorGate` definitions are reused, and

```lean
physicalProfile logQ N width b x =
  (∏ i, floorGate (x i / b)) *
    P2FiniteMarkedGamma5LogExtension.profile
      logQ (Real.log N) width (safeLogPoint b x)
```

has no primality, coprimality, coefficient, modulus, or output-prime branch.

## Accepted physical conclusions

All names in this section belong to
`ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension`.

- `contDiff_physicalProfile`: genuine global `ContDiff ℝ ∞` for `b>0`.
- `physicalProfile_eq_floor_mul_original`: global identity with the exact
  original log profile multiplied by the same floor factors.
- `physicalProfile_eq_original`: exact agreement whenever every slot is
  at least `b`; every floor equals one there.
- `physicalProfile_nonzero_lower`: nonzero weight forces every slot above
  `b/2`. `physicalProfile_eq_zero_of_slot_le_half` gives the zero region.
- `physicalProfile_nonzero_product_lt`: for positive `N` and `width`, the
  original `Gate.product` gives the complete-product cap `exp(width)*N`.
- `physicalProfile_nonzero_upper`: each slot is strictly below
  `exp(width)*N*(b/2)/(b/2)^Fintype.card(Slot k r)`.
- `support_physicalProfile_subset_box`,
  `tsupport_physicalProfile_subset_box`, and
  `hasCompactSupport_physicalProfile`: the derived closed rectangle
  contains both supports and is compact. It is independent of `logQ` and
  may be empty.

No compactness or support conclusion is an assumed premise. The parameter
`b` remains free and positive; neither `1/90` nor rank 200 is substituted.

## Accepted chart tensor conclusion

Namespace `ImbalancedChen.P2FiniteMarkedGamma5PhysicalEulerBudget` defines
`slotOrbit p y i := p i * exp (y i)`. Its main theorem is

```lean
physicalProfile_chart_tensor_budget (k r q : ℕ) :
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ logQ N b width : ℝ, 0 < b → 0 < width →
      ∀ p x : PhysicalPoint k r,
        ‖iteratedFDeriv ℝ q
          (fun y => physicalProfile logQ N width b (slotOrbit p y)) x‖ ≤
            C * (1 + width⁻¹)^q
```

The constant precedes every endpoint, target, cutoff, positive width,
physical base, and chart point. There is no `width≤1` condition.

The fixed `logSlotMap` sums every old slot and preserves every fresh/tail
slot. The accepted `profile_tensor_budget` supplies its actual logarithmic
factor. The original `log_floor_bound` supplies each translated physical
floor uniformly in `log(p_i)-log(b)`. Native finite-product and Leibniz
estimates combine them. If any base coordinate is nonpositive, the whole
physical chart is zero; the final statement therefore covers all real
bases. No derivative estimate is introduced as a new hypothesis.

## Accepted actual operator-word bridge

The existing `P5Z.AdmissibleAllRankIntegerGeometricFamily.Family.mixedEuler`
is not definitionally a chart tensor. It uses the genuine operators

```lean
eulerOne i f v := fderiv ℝ f v (Pi.single i (v i))
eulerWord w f := w.foldr eulerOne f
```

and requires natural constants `C,B` common to all allowed ranks, all
words of length at most a chosen order, all real base points, and all
targets. Its domain is `Fin rank → ℝ`.

The existing generic conversion is supplied in
`Part5OriginalH430ClassicalSmoothEulerConjugacy.word_chart` and
`norm_bound_at_zero`, in the original `t07/classical-fixed-box/smooth-word/
hb-licence/` source. They apply to every globally smooth function on
`Fin rank → ℝ`, including repeated coordinate words and nonpositive bases.
The new lightweight core moves these exact existing declarations and
their actual `eulerOne`, `eulerWord`, `E`, and `coord` prerequisites with
unchanged public names and statements. The initial extraction preserved
every source body; the compiler-directed typing and API repairs are
recorded in `EULER_CONJUGACY_API_REPAIRS.json`. It reuses the generic proof.

The new bridge namespace is
`ImbalancedChen.P2FiniteMarkedGamma5EulerWordBudget`. Its `slotEquiv`
concatenates all tagged slots as `Fin (k+(2+r))`, using two native
`finSumFinEquiv` equivalences. Explicit old/fresh/tail formulas and both
inverse identities preserve every slot. `finPhysicalProfile` is the same
physical function after this coordinate permutation, and
`finToPhysical_flow` states the exact chart identity. The continuous
linear permutation has norm at most one.

The accepted `finPhysicalProfile_mixedEuler_budget (k r m)` derives a
single nonnegative real constant for every original Euler word of length
at most `m`, uniformly in every real point and all moving parameters.
It applies the original `norm_bound_at_zero` to the accepted chart tensor
estimate, then sums the constants for orders `0` through `m`.

The accepted `finPhysicalProfile_boundedRank_mixedEuler_budget (K m)`
then sums the fixed-rank constants over the finite range to derive:

```lean
∃ C : ℝ, 0 ≤ C ∧
  ∀ k r : ℕ, k + 2 + r ≤ K →
  ∀ logQ N b width : ℝ, 0 < b → 0 < width →
  ∀ w : List (Fin (k + (2 + r))), w.length ≤ m →
  ∀ v : Fin (k + (2 + r)) → ℝ,
    |eulerWord w (finPhysicalProfile logQ N width b) v| ≤
      C * (1 + width⁻¹)^m
```

No Euler estimate, word conjugacy, or admitted-rank conclusion is a new
hypothesis of these derivations. `K` is arbitrary, and no particular rank
ceiling is substituted. Both modules passed strict compilation,
independent replay, and the full owned-declaration audits recorded above.

## Exact remaining Family and Licence boundary

The accepted quantitative analytic bound still needs the actual
manuscript rank-admission theorem and
parameter specialization. For fixed positive width the factor can be
absorbed in a natural positive constant and logarithmic exponent zero.
A width varying with the target instead needs its actual polylogarithmic
inverse-width bound. Neither specialization is silently assumed here.

`P5Z.LicensedOriginalIntegerProfile.Licence` itself has only `ambient`,
`smooth`, and `agrees_on_primes` fields. Its prime agreement still has to
refer to the real selected source and smoothing, not an assumed equality
with an unrelated sharp indicator.

The actual rank ceiling, original marked-source/prime agreement, common
positive cutoff, collar payment, same-coefficient PP/VM application, and
the final complete `Family` instance remain outside these receipts. The
classical `Family 200` and its `1/90` cutoff are different existing objects.
These accepted analytic modules do not complete the full `Family` or P2.

## Provenance and compiler repairs

`SCALAR_EULER_EXTRACTION_MANIFEST.json` records the exact initial extraction
of the original `ScalarBound`, `plateau_bound`, and `log_floor_bound`.
The helper's private-to-public visibility change is explicit: remaining
original scalar consumers reuse one proof through the new import. The
old heavy owner has an import/removal postimage but is not validated by
the lightweight receipt.

`SOURCE_API_REPAIRS.json` preserves the failed initial source hashes and
records the compiler-directed repairs and accepted corrected hashes.
The repairs keep theorem statements and mathematical arguments unchanged;
the current scalar proof bodies are not described as byte-identical to
the donor after those repairs. Previously accepted scalar-core bytes were
left unchanged.

`EULER_BUDGET_API_REPAIRS.json` records the compiler-directed chart-budget
repairs and its accepted receipt. `EULER_CONJUGACY_EXTRACTION_MANIFEST.json`
records the initial 17 exact moved declarations, current API-only deltas,
four original-owner import/removal postimages, and their hashes. The exact
postimages have now been applied to all four canonical
source-only owners, after preserving their complete preimages as
non-selected `history/*.lean.txt` files. The second extraction from
`EulerBounds` preserves the earlier scalar-core import and removals. No
private helper is moved in this extraction. The
old heavy closures remain unvalidated. `EULER_WORD_BRIDGE_PROVENANCE.json`
binds the derived bridge to its accepted physical/chart suppliers and
its accepted conjugacy supplier.
`EULER_WORD_BRIDGE_API_REPAIRS.json` records the single explicit-map API
correction, its original failed source hash, and identical active/source-only
postimages. The conjugacy and bridge records now include their actual
successful receipt from job `24e632b1c7794c4c8fede0d6fa606e78`, with source
declaration counts distinct from audited owned counts. Historical failed
attempts remain recorded as history. No theorem statement changed.
