# Independent review of the P3.5 Drappeau adapters

**Reviewed source commit:** `44743fb463011127f66274f197ff38bf4680c192`

**Review date:** 2026-11-27

**Conclusion:** accept the two adapter components within the scope below. No
unresolved Critical, Important or Minor review finding remains. **Full P3.5
remains open.**

## Scope and source identity

This review covers `Part3ActualSpectralTestNormalization`,
`Part3DrappeauRegularEnvelope`, the continuation verifier's imported-object
binding, and the corresponding outside-input boundary. Source review was
followed by independent inspection of the complete GitHub CI certificate for
the `p35-drappeau-adapter` group at the exact commit above.

| Reviewed source | SHA-256 |
| --- | --- |
| `ImbalancedChen/Part3ActualSpectralTestNormalization.lean` | `22be1365a38aad7c1ed49c5c18b80c6c1271ec035a1866865bdac97100872609` |
| `ImbalancedChen/Part3DrappeauRegularEnvelope.lean` | `232273e825d94ab4cf2035d2269335fbf1d07659437a0ec47eebbb121323e2c8` |
| `verification/verify_part3_continuation.py` | `7a0fb2761cae24eb999ae730723c03d24d126bd4b8f577ea2919a145592c5c58` |

The inspected CI archive, `p35-drappeau-ci-44743fb4.zip`, has independently
recomputed SHA-256
`ee69e0fc5ba9aad9c563c292d366f7553e82c930ceba4a82972a1462d1430de1`.
The review used its `report.json`, raw stage logs, generated Lean audit files,
`imported-environment.json`, `declarations.json`, and `theorem-types.txt`.

## Independent CI certificate checks

- The report records `PASSED` at the exact reviewed commit. All **36 stages**
  record exit code zero. Every stage log's SHA-256 and command header matches
  its report entry. The two strict compilations use `warningAsError=true`;
  both bundled-checker logs contain the expected owned-module replay record.
- All **109 source/configuration hashes** match the local candidate bytes.
  The initial and final working-tree logs are empty, as is the unchanged
  baseline-proof check. The raw pin and clean logs for all 11 dependencies
  match the frozen manifest.
- Both generated Lean audit sources reproduce byte-for-byte from the reviewed
  verifier. Their hashes and the imported-environment manifest hash match the
  report.
- The raw declaration audit, declaration JSON and complete theorem-type file
  agree exactly. The inventory contains **28 declarations: 17 normalization
  declarations and 11 envelope declarations**, comprising **24 theorem records
  and 4 definition records**. It includes both private envelope helper
  theorems and all four generated normalization helpers; coverage is not
  restricted to public theorem names.
- The observed transitive axioms are exactly **`propext`, `Classical.choice`
  and `Quot.sound`**. The serialized-inventory and defining-module checks are
  retained in the generated audit.
- The preflight and final actual-import inventories agree on **6,695
  non-owned modules**. The final inventory adds exactly the two owned modules.
  Every imported owner, source path, object path and artifact-hash key was
  checked. Independently recomputing the corresponding local source hashes
  matched all 6,695 records, including the 60 project dependencies, with no
  missing source or mismatch.

The key compiled theorem types preserve the reviewed mathematical scope:
the actual C4 Fourier budget chooses its constant before `rho` and `sigma`
and has degree 28; the normalized unit-family statement covers every `Y>0`;
the continuous adapter retains separate local L2 and cumulative-energy
premises; global `Integrable` is a conclusion. The signed exhaustion theorem
does not assume the desired bilinear spectral return or a separate global
integrability hypothesis.

## Resolved findings and source repairs

**Imported-object binding.** The first verifier draft checked resolution only
for owned objects. The accepted version enumerates actual imports through
`env.header.moduleNames` and `Lean.findOLean`, requires a unique pinned source
owner, and checks each resolved object against that owner's expected path.
Source and available `.olean`, `.server` and `.private` hashes are compared
before and after verification. The final environment must contain every
owned module at its expected path. The reviewer independently rebound the
978-module core probe and confirmed rejection of an external same-name
shadow path and a final inventory missing owned imports. The complete CI
import inventories subsequently exercised the accepted binding on the full
6,695-module imported environment. The Important finding is resolved.

**Parity of the external estimate.** [EXTERNAL_INPUT.md](EXTERNAL_INPUT.md)
now explicitly specializes Drappeau Lemma 4.4, equation (4.12), to `kappa = 0`.
It preserves the general same-sign parity factor instead of silently
discarding it, and distinguishes the registered outside theorem from its
pending application to actual native transforms. The documentation finding
is resolved.

**Real-to-complex inverse casts.** Three occurrences now explicitly use
`Complex.ofReal ((normalization d ell)⁻¹)`. Reverting just those three textual
changes reproduces the exact normalization-source hash from the initial
review. The correction fixes elaboration of the inverse and the associated
rewrite steps while preserving the mathematical normalization, parameter
ranges and conclusions. The accepted complete strict compilation verifies
the corrected source. The envelope source retains the reviewed explicit
intermediate bounds and coefficient `260*E`.

## Acceptance limits

This was a source and certificate review. The reviewer independently checked
the retained CI evidence and source bytes; the Lean strict compilations and
kernel replays were the recorded CI executions, not an additional compilation
run by the reviewer. Imported dependencies retain
`NORMAL_IMPORTED_ENVIRONMENT_TRUST`; this certificate does not kernel-replay
the entire imported dependency graph as owned work.

The separate **P1 cross-environment comparison was completed by the root
agent**. It is not claimed as an independent check performed in this review,
and its results are not combined with the CI counts above.

The two components establish actual C4 test normalization and the conditional
cubic-envelope payment, including genuine global L1 before signed integral
exhaustion. Applying the registered external estimate to the actual native
transforms, transporting positive scalar normalization, preserving the printed
row factors, recovering the six missing Y04 sources, and connecting the actual
spectral, level, Fourier and physical assemblies remain separate obligations.
The exact boundary is recorded in [EXTERNAL_INPUT.md](EXTERNAL_INPUT.md) and
the bounded source search in [SOURCE_RECOVERY.md](SOURCE_RECOVERY.md).

Acceptance of these two components does not close P3.5 or certify the full
spectral polynomial.
