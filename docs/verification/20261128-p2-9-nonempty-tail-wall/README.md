# P2.9 continuation: uniform nonempty-tail wall payment

Recorded on 2026-11-28 (Asia/Shanghai), on `work/p2-9-formal-proof-20261125`.

## Accepted increment

| Module | Result of this continuation | Owned declarations |
| --- | --- | ---: |
| `P2FiniteMarkedGamma5OmittedPrimeWall` | Root acceptance of the complete original successful archive; no repeated Lean run | 13 |
| `P2FiniteMarkedGamma5NonemptyTailWallCount` | New target compilation, named kernel replay, full owned-declaration audit, and independent complete archive verification | 11 |

This accepts two module records and 24 owned declarations. Borrowed dependencies
receive no new credit. **P2.9 as a whole remains open.** The same-coefficient
signed prime-product estimate, the original J identification, and the actual
selected-history realization are not established by these records.

The root decisions are in [the Omitted record](omitted/ROOT_ACCEPTANCE.json) and
[the Nonempty record](nonempty/ROOT_ACCEPTANCE.json). The independent verifiers
deliberately leave their own `root_accepted` field false; the separate root
records make the acceptance decision after joining the original service tasks,
source review, and archive evidence.

## Mathematical result

The newly qualified public theorem is
`ImbalancedChen.P2FiniteMarkedGamma5NonemptyTailWallCount.eventually_properTuples_payment`.
For fixed old rank `k`, positive tail rank `r`, root-cell exponent `nu`, and
`epsilon > 0`, it supplies one eventual threshold in `N` such that, for every
`Q` satisfying `log Q / log N = nu` and every `0 < width <= 1`,

```text
norm N * (properTuples N k r Q width).card <= epsilon.
```

The threshold is chosen before `Q` and `width`. The carrier retains the original
ordered labelled prime tuple, the cutoff, product bound `<= 2*N`, coprimality,
and one-sided nonproduct strips `(-width, 0]`. The proof fixes a reservable
omitted coordinate and an affine width for each gate, uses sufficiently large
`log N`, and combines the finitely many gates by an ordinary union bound.

The exact 6,727-byte source with the explicit `NonradialSupport` import is
[saved here](sources/ImbalancedChen/P2FiniteMarkedGamma5NonemptyTailWallCount.lean).
Its original Git blob is `eaaa2b2d78c26668c3c4d54dca00876cd5bc1c8a`; no
mathematical source change was needed. The accepted Omitted source is
[also saved](sources/ImbalancedChen/P2FiniteMarkedGamma5OmittedPrimeWall.lean).

The manuscript reference remains the frozen 2026-11-06 release at
`UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`,
especially `sieve-appendix.tex` 1090–1101 for fixed finite feedback and thin
proper walls. This ordinary-count result does not supply a signed PP estimate.

## Validation evidence

The new P2 service task is `7dd70423f7f64b19bacfe57c71166457`: exit 0,
150.418 seconds, sampled peak RSS 6,288,281,600 bytes. Its original request,
terminal task record, and stdout are saved under `nonempty/`.

- Normal compilation uses warning-as-error and the unchanged original runtime
  guard, with effective Lean options `-t0 -j2 -M12288`.
- The named kernel replay covers exactly the new target. The owned audit covers
  all 11 declarations, including private declarations; its observed axiom union
  is `Classical.choice`, `Quot.sound`, and `propext`.
- The actual post-compilation graph has 6,357 modules and 31,089 facets. The
  pre/post graph comparison preserves all 31,088 existing facet identities
  and current stat snapshots; the sole addition is the target `.olean`.
- Every actual facet is rehashed after kernel and owned audits. Exactly one
  target source invocation occurs; borrowed source, kernel, and owned proofs
  are not replayed.
- The independent Nonempty verifier reads all 67 archive members, checks all
  66 manifest file identities, reparses raw import and owned logs, verifies
  runtime/process bindings, and checks the three live target files.
- The independent Omitted verifier reads all 374 original archive members and
  373 manifest identities and joins the original normal/kernel/owned evidence.
  The historical compile task is `32442b1b929641aaadccf28bae7d8f52`.

Complete compressed archives are included for both accepted targets. They
contain the actual import graphs, raw logs, compiled outputs, manifests, and
bound controllers. The verifier and controller source and their focused tests
are saved under `controllers/` and `verifiers/`.

## Exact-byte environment recovery

The original paths had lost 67 project objects. Their accepted original bytes
were restored into an independent directory: 53 from matching live copies and
14 from pinned original archives. The exact recovery map and a transport of
these 67 recovered objects are saved under `environment/`; this operation adds
no mathematical credit and invokes no Lean compiler.

Eight package configuration directories were selected from checkouts at the
original manifest revisions. The seven existing compiled-library search paths
were retained, including the 930 facets they supply. Only the unused missing
Cli fallback moved. Package revision equality never authorizes an object:
every actual imported facet still has to match its accepted physical path,
size, and SHA-256.

Another 1,812 existing files had different historical inode/time metadata, but
all retained their exact accepted bytes. The driver records the historical and
fresh snapshots and requires stability within the new run. The original
failed environment attempts are preserved separately; neither reached a Lean
proof invocation.

## Next unresolved boundary

[NEXT_ACTUAL_CHAIN_REVIEW.json](NEXT_ACTUAL_CHAIN_REVIEW.json) records the
source-only Actual chain, existing reusable objects, original declaration
owners, source choices still to be made, and the PowerErrorBudget object
variant boundary. It does not claim those combined imports have been accepted.

The next step is to establish a coherent, exact historical/arithmetic input
selection for `ActualRootCells` and its consumers, then qualify only new targets
in dependency order. A local log/rpow identity could remove the direct
`UnitSourceMass.scale_identity` call from `ActualHistoryScale`; it would not
remove the existing transitive dependency through the history chain. No such
source edit is made in this continuation.

The accepted UnitTailCount and other old radial objects should be reused with
their original evidence. Their combined receiving environment still needs
the recorded object-variant checks. No new manuscript-external estimate is
formalized, and no full-P2.9 closure or aggregate-PR readiness is claimed.
