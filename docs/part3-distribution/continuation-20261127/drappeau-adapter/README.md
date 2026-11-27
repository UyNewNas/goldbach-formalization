# P3.5 C4 normalization and cubic regular-envelope adapter

**Source candidate: strict compilation, kernel replay and complete declaration
acceptance are pending. Full P3.5 remains open.**

## Mathematical components

| Module | New derivation |
| --- | --- |
| [Part3ActualSpectralTestNormalization](../../../../ImbalancedChen/Part3ActualSpectralTestNormalization.lean) | Positive mode normalization; actual C4 unit tests for all positive scales; actual Fourier summability with degree-28 cost |
| [Part3DrappeauRegularEnvelope](../../../../ImbalancedChen/Part3DrappeauRegularEnvelope.lean) | Cubic test envelope into the existing shell consumer; finite and positive-measure bounds with coefficient `260*E`; proved global L1 before signed exhaustion |

These modules reuse the accepted actual test jets, Fourier budgets, shell
payment and measure exhaustion. They do not prove the outside Bessel theorem
or supply the unresolved native spectral rows. The envelope theorem has its
lower-level transform estimate as an explicit hypothesis; it does not assume
the target bilinear spectral return.

[Exact outside input and manuscript boundary](EXTERNAL_INPUT.md) ·
[Source recovery and existing-work audit](SOURCE_RECOVERY.md) ·
[Completed P2 source inventory](P2_SOURCE_RECOVERY.json)

## Acceptance route

The verifier group is `p35-drappeau-adapter`. The existing GitHub workflow
selects this group on the P3.5 branch. In a prepared pinned checkout:

```bash
python3 verification/verify_part3_continuation.py \
  --group p35-drappeau-adapter \
  --expected-head COMMIT \
  --output-dir .lake/p35-drappeau-verification
```

`--prepared-environment` additionally permits direct use of a prebuilt,
exactly pinned Lean environment without asking Lake to rebuild its imported
objects. Both modes verify every actual imported module's source and object
root, bind the source and object hashes before and after compilation, strictly
compile the owned modules, replay them with the bundled checker, and audit the
complete serialized declaration/type/transitive-axiom inventory.

The only allowed transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`. Imported dependencies retain normal imported-environment trust;
the group is not a replay certificate for the whole dependency graph.

The initial import-binding checks, including rejection of a shadowed object
and of a missing owned import, are recorded in
[IMPORT_GUARD_CHECKS.json](IMPORT_GUARD_CHECKS.json). Those scoped checks are not
acceptance evidence for the two Lean modules.
