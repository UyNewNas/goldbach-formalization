# Part 1: permits for the cap actually stored in a historical cell

## Status and identities

**Current status: VERIFIED.** The independent three-target strict original
frontend compilations and three original `leanchecker` calls all exited
zero. The complete defining-module census covers 36 declarations: 14 from
production and 22 from the computation probe, including generated items.
The observed transitive axioms are only `propext`, `Classical.choice` and
`Quot.sound`. The current-source receipt was collected at
`2026-10-12T12:56:10.056234+00:00`, SHA256
`7f687c1d1b61ec3142de63f1458b5dcf650928348e6b4231b871a121c99d4ee1`.
See [VERIFICATION.md](VERIFICATION.md), the exact
[VERIFICATION.json](VERIFICATION.json), and [EVIDENCE.tar.gz](EVIDENCE.tar.gz).
The historical geometry/integral candidates in the parent directory have
separate targets and do not inherit this successful permit result.

| Reference | Complete identity |
| --- | --- |
| Common mathematical baseline | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| Source branch | `codex/variable-envelope-boxes` |
| Delivery branch | `chatgpt/chen-p1-history` |
| Previously verified lower-fourth/history milestone | `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` |
| Observed delivery parent | `7f894bfb57b7aa561360e335c6d610b7c30614e0` |
| Frozen manuscript commit | `ba6ec11d800eccc54406490631895e174de85766` |
| Frozen manuscript body blob | `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` |
| Fixed toolchain | `leanprover/lean4:v4.33.0-rc1` |
| Production source SHA256 | `50a9dc07e98046a664711572bcf69b58a528c0a97502bbd9f75de245dd43bc0d` |

The parent changes only external CI timeouts after the previous P1
milestone. This batch preserves all parent files and pins. No public root,
workflow, dependency or final theorem entrypoint is edited.

## The interface gap closed by this module

The existing historical adapter receives midpoint caps made by
`selectedBoxCap`. A certificate can instead store another rational cap
strictly inside the same whole-box bounds. The new module checks and
licenses that actual value. Its general theorems require no equality to
the automatic midpoint.

`ImbalancedChen/StoredHistoricalBoxPermit.lean` imports only the existing
`SelectedPrefixRationalMesh` supplier. It reuses the existing rational
whole-box lower and upper bounds, square expressions, rational-to-real
dictionary, envelope interval bound and actual integer-product lemmas.
It does not duplicate the midpoint construction or modify its checker.

For mask `I`, supplied inherited level `old`, ceiling `nu`, endpoints
`lo, hi` and stored value `cap`, set

```text
L = selectedCapLower I old hi
U = selectedCapUpper I nu lo hi.
```

`storedBoxCapCheck I old nu lo hi cap` is exactly the rational Boolean
decision of `L < cap and cap < U`. The lower maximum includes `old`,
`1/2`, every full-prefix square expression at `hi`, and every selected
square expression at `hi` whose final index is outside `I`. The upper
bound is the minimum of `nu` and the existing interval lower bound for
the variable envelope. Thus all conditions are finite rational arithmetic.
Neither an integral estimate nor a final K/c bound is an input.

## Whole-box soundness and the exact arithmetic products

At every real point `t` of the closed endpoint box, a successful check
proves these six conclusions at the stored value itself:

1. `old < cap`;
2. `cap < nu`;
3. `1/2 < cap`;
4. `prefixSquareExpr t k < cap` for every index `k`;
5. `selectedSquareExpr I t k < cap` for every `k` outside `I`;
6. `cap < VariableEnvelope.v (sum_{i in I} t_i)`.

The proof uses the existing coordinate monotonicity to compare the two
square expressions with their upper-endpoint values. It uses the interval
bound `qVLo_le_v` to compare the rational upper bound with the actual
envelope value. Every final gate remains strict.

Given `N > 1`, natural labels `p` and `p_i <= N^(t_i)`, these inequalities
then imply the exact arithmetic licenses

```text
(product_{i<k} p_i) * p_k^2 < N^cap
```

and, for every `k` outside `I`,

```text
(product_{i in I} p_i)
  * (product_{i<k and i notin I} p_i) * p_k^2 < N^cap.
```

The second formula retains the selected subproduct as a separate actual
natural-number product. These theorems hold for all natural labels meeting
the displayed power bounds. Applying them to an actual prime carrier
therefore retains that carrier's primality, `p_i not dividing N`, ordering
and strict upper cutoff. This module does not construct or change that
carrier and does not establish its support or well-factorability.

These are square-product licenses. No old or new own-cube test is assumed
or merged into them.

## Common-mesh data contract

`storedMeshCapCheck a b m J I old nu cap` allows each selected cell to
have its own mask, inherited old level, ceiling and new stored level.
Its outer decision explicitly uses `Finset.decidableDforallFinset` over
`J`. It does not enumerate the entire function space of possible labels.

| Field or convention | Requirement and proved behavior |
| --- | --- |
| Fixed data | `a b m J I old nu cap` are supplied before the target `N`; all cap comparisons are rational. |
| Cell label | `Fin n -> Fin (m+1)`, in the existing processing-coordinate order. |
| Endpoints | The existing common rational mesh, cast by `cast_qLogPrimeMeshLo` and `cast_qLogPrimeMeshHi`. |
| Ownership | Soundness uses the original coordinatewise `Ico` cell membership. Its upper inequality is weakened only to invoke closed-box soundness; ownership remains left closed and right open. |
| Per-cell mask | The actual `I j` is used in both the finite endpoint check and the selected subproduct. |
| Per-cell old | The caller must identify `old j` with the effective inherited preceding level. The new theorem proves `old j < cap j` after that value is supplied. |
| Per-cell ceiling and cap | The actual `nu j` and stored `cap j` are checked, without a midpoint identity. |
| Processing order | The products retain index tests `i < k`; when applied to P1 histories these are the original descending processing coordinates, not the reverse-stored list indices. |
| Old/new own-cube indicators | They remain separate in the existing historical policy and integral interfaces; this permit adds no own-cube admission filter. |
| Unselected cells | The checker makes claims only on `J`. Actual historical fallback outside `J` must be supplied by the existing policy construction. |
| Global support | Not inferred from a local endpoint check; the adopted coefficient support and factorization interfaces remain separate obligations. |

`storedMeshCapCheck_old_lt` projects the successful check to all finite
strict inherited-level comparisons. `storedMeshCapCheck_sound` proves
the six analytic licenses on every selected Ico cell, and
`storedMeshCapCheck_actual_square_gates` proves the corresponding actual
products. The fixed data may be a manuscript certificate, but the theorem
does not assert that the current manuscript's complete tables have been
provided or accepted.

The compatibility lemmas `storedBoxCapCheck_midpoint` and
`storedMeshCapCheck_of_selectedBoxCapChecks` receive existing midpoint
certificates without changing either checker.

## Kernel computation probes

The small probe uses one coordinate, `I = {0}`, endpoints `1/10` and
`11/100`, `old = 1/2`, `nu = 3/5` and stored `cap = 53/100`. Its whole-box
bounds are `L = 1/2` and `U = 11/20`. The automatic midpoint is `21/40`,
different from the accepted stored cap.

The probes cover acceptance of that non-midpoint value, its exact midpoint
comparison, rejection of both equality endpoints, rejection when `old`
increases to `11/20`, rejection with an empty mask, rejection when the
ceiling decreases to `13/25`, and successful traversal of one selected
`m = 0` mesh cell. Decisions use `decide +kernel`; no native decision
shortcut is used. These are small interface regression examples, not an
adopted manuscript certificate.

## Files, validation and integration

| Owned new file | Purpose |
| --- | --- |
| `ImbalancedChen/StoredHistoricalBoxPermit.lean` | Two finite check definitions and ten public licensing/compatibility theorems. |
| `verification/parts/p1/round2/permit/StoredCapProbe.lean` | Kernel computation and strict-endpoint regression probes. |
| `verification/parts/p1/round2/permit/StoredCapAudit.lean` | Complete defining-module census of production and probe, including private/generated declarations, with unsafe/axiom rejection and transitive axiom checks. |
| `KEY_THEOREM_TYPES.md` | Complete definitions and theorem types, bound to the source and current audit. |
| `check.sh` | Explicit three-target stock-CLI reproduction commands for an environment where the pinned CLI starts. |
| `INTEGRATION.patch` | Frozen, unapplied cumulative verified-leaf import proposal against the original P1 parent root, retained with its evidence. |
| `../PART0_28FD_PERMIT_IMPORT.patch` / `../PART0_IMPORT_CHECK.json` | Incremental permit-only import proposal for P0's exact `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` root, with actual successful text applicability check. |
| `VERIFICATION.md` / `VERIFICATION.json` | Actual current-source compilation, replay, audit and source/object/pin bindings, with explicit scope limits. |
| `EVIDENCE.tar.gz` / `ARTIFACT.json` | Original text evidence and its path/hash inventory; compiled binaries are hashed and omitted. |
| `archive_evidence.py` | Evidence-only collector; checks the existing successful receipt and archives original records without invoking Lean, Git or CI. |

The independent validation targets are the production module, its probe
and its audit. The permitted transitive logical axioms are exactly
`propext`, `Classical.choice` and `Quot.sound`. No successful parent build
or historical receipt stands in for these new targets.

This environment's stock Lean CLI fails before parsing with
`failed to locate application`. Verification therefore uses the unchanged
official `Lean.Elab.runFrontend` through the original official Lake
runtime, at `trustLevel = 0` and `warningAsError = true`, followed by the
original `leanchecker` executable. The scheduling lock only serializes
resource use. It does not change the compiler, checker or proof trust.
The stock `check.sh` is provided for reproduction; its execution is not
claimed here.

The original checker replays declarations of each requested module; this
does not claim a fresh replay of every imported declaration. Supplier
sources, manifest pins, import object hashes and available artifact
bindings must be recorded separately in the receipt.

## Relation to the historical integral work

The previous `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` milestone remains the
actually verified lower-fourth integral and finite inherited cap/telescope
delivery. P0 now formally accepts its four production modules at
`28fd630ef7cc38eba86beb6c0ba123336b5d05f2` and imports them in the public
root. Exact-head GitHub step metadata reports that integration's build,
original checker, axiom audit and full-type export succeeded; no raw
artifact was downloaded or new local root replay run for this intake.
The new permit is not covered by those earlier P0 gates. Its incremental
proposal is [PART0_28FD_PERMIT_IMPORT.patch](../PART0_28FD_PERMIT_IMPORT.patch),
checked against an unchanged byte-exact copy of that P0 root. See
[PART0_IMPORT_CHECK.json](../PART0_IMPORT_CHECK.json) and the final
[P0 intake](../FINAL_P0_INTAKE.md).

The reported independent inherited-fifth integral source remains
**SOURCE_PENDING**. P0's newly stored `.lean.txt` snapshots are explicitly
the uncompiled joint-cell candidates from this round; their newly fixed
Git identities do not identify the independently reported source or supply
its missing same-source compilation receipt. The initial
[upstream intake](../UPSTREAM_INTAKE.md) is retained as a historical snapshot.

The two new historical fifth geometry/integral leaves and their probe in
the parent directory remain **UNCOMPILED CANDIDATES** until their separate
four-target gates finish. They describe an actual prime-tuple cell
correction and a genuine integral limit; they do not claim the missing
full nested-saving bridge or the complete adopted density formula.
They are excluded from this permit's validation and import proposal.

## Unclosed inputs and receiving Parts

| Receiver | What this milestone supplies and what remains |
| --- | --- |
| Part 0 | The previous four verified P1 leaves are already imported at `28fd630ef7cc38eba86beb6c0ba123336b5d05f2`. Integrate the new verified permit using the incremental patch, then run canonical integration gates at the resulting complete SHA. Preserve the separate candidate status of the two new historical integral leaves. |
| Part 2 | Instantiate `J`, `I`, actual inherited `old`, ceiling `nu` and stored `cap` on the adopted common grid; prove the finite check and the history-identification equations. The stored caps no longer have to equal midpoints. |
| Part 3 | Consume the exact full-prefix and selected-subproduct square inequalities after the actual carrier/coordinate dictionary is supplied. Complete the adopted support/factorization construction separately. |
| Part 4 | Consume the actual stored cap, envelope and strict product gates; prove the distribution/support interfaces at those same values. |
| Part 5 | Use these licenses when identifying the adopted arithmetic ledger and integral terms. This local permit proves no K/c bound or density limit. |
| Part 0 / Part 1 | Receive the independently reported fifth source; finish the full historical saving-to-tuple bridge, adopted multilevel policy instance, complete integral composition and any remaining truncation/boundary interfaces. |

The final [P2 intake](../FINAL_P2_INTAKE.md) records publication head
`e6d6d57323cc358cef060fb243ec386c13cb662d` and proof source
`f0c00f9ccce98e04af439321a92eb9fd0dd26203`. Its Prefix64 E0 batch extends
the earlier analytic integral certificate, while its P1 interface blob
`ad46c9e1bc9ef11692b7650fbb5372e8f4174706` remains unchanged. That contract
is accepted for coordinate and ownership conventions. The new batch has
not instantiated the present per-cell fields or their actual inherited
`old` identity; its `exact_Z` fibre cutoff cannot serve as a stored cap.
Lower-fourth, inherited fifth finite identities,
historical fifth cell-integral candidates and the present local permits
remain separately identified components of the eventual adopted proof.
