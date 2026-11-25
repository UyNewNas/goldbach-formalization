# Original singleton proper-power comparison

## Current status

The six selected new owners are **source-only, pending P1 normal/kernel/full-owned verification**. The 19 P3 dependency files are reused from existing accepted work. This is not a completion claim for the whole P1.5 node.

The first four-owner run at source `1a259e113c0977c8cb2814492ff3bd6ab7cdc475`
installed all 26 permitted missing sources and verified existing dependencies
without rebuilding them. Two normal builds failed on three local expression
errors; the other two owners were held because those dependencies were not ready.
`FIRST_COMPILE_OBSERVATION.json` preserves the bounded result and stage hashes.
`FIRST_COMPILE_REPAIRS.json` records the exact two-source repairs: join the split
`.trans_eq` field notation in `profile_bounds`, and remove two redundant `tauto`
tactics after `simp` has closed its goals. Statements, definitions, imports,
and the signed fresh-minus-old identity are unchanged. Fresh acceptance of the
repaired bytes remains pending.

The preceding 23-owner fourth/fifth actual-mean chain remains accepted at source `29295f6a7196c523b525104f864da20035cc15d9`, with its final published evidence at `c6b89774822580c731a236ac66dcd7466ac8a0e6`. None of those owners is selected for recompilation here.

## Exact new conclusions

`P1OriginalSingletonProperPower` applies the existing P3 prime/von-Mangoldt comparison to the original `P5CanonicalTentNarrowSingletonTransfer.fullSmoothWeight`. For every fixed `kap < 1`, every real logarithmic exponent `A`, and every `eps > 0`, one eventual threshold precedes the collar order, finite modulus carrier `Q`, and signed real coefficient `rho`. The only arithmetic conditions on them are

```text
q in Q -> 0 < q and q < N^(599/1000)
q in Q -> |rho q| <= 1.
```

The conclusion compares the original prime-product signed error to the exact von Mangoldt signed error on `Icc 1 (2*N)`, with the same `Q`, `rho`, target residue, and coprime mean. Its norm is at most `eps * N / log(N)^A`.

The singular-normalization theorem takes `A = 2` and `eps = eta * twinPrimeConstant`, then uses the existing `singularNormalization_lower`. It gives the error budget `eta * singularNormalization N` for every fixed `eta > 0`.

`P1OriginalHistoricalProperPower` specializes this result to the original

```text
remainingModuli B N (trueDDeltaSupport old fresh N cap w z)
trueDDeltaRho old fresh N cap w z L
policyRemaining B kap old fresh N cap w z L.
```

The threshold precedes `B`, both policies, `cap`, `w`, `z`, and `L`. The recovered original unit-bound proof supplies the coefficient hypothesis; the original squarefree support supplies positive moduli, and the original filter supplies the strict `.599` upper bound. No desired error estimate is an input. The comparison history retains `old = S, fresh = R`; the saving history retains `old = eight, fresh = six`.

## Selected owners and reused sources

| Owner | Work performed |
|---|---|
| `P1OriginalSingletonPointwiseData` | Separate 18 historical definitions/basic proofs under their original names; one field-notation whitespace repair after the first compile. |
| `P1OriginalSingletonProperPower` | Instantiate the already accepted P3 arithmetic theorem on the original full singleton weight. |
| `P1Full87TrueDPolicyDelta` | Adopt the original provider, then remove two redundant post-`simp` tactics reported by the first compile. |
| `P1Full87TrueDUnitBound` | Adopt the original proof bodies; change only the first import from `ThreeBookNetInvoice` to its actual `PolicyDelta` dependency. |
| `P1OriginalHistoricalMiddlePointwiseData` | Separate the three unchanged original remainder definitions. |
| `P1OriginalHistoricalProperPower` | Apply the comparison with the original physical support and signed coefficient. |

`SOURCE_CLOSURE.json` binds all 316 project sources and their imports. `P3_REUSE.json` binds the original accepted P3 mathematical source `70e8f69cbbacb2b851147a5fa51948a106beeca7`, its 77-source closure, and the 19 added canonical files. The remaining 58 P3 paths are byte-identical to the preceding P1 branch. There are no same-path source conflicts.

`TRUE_D_ADOPTION.json` distinguishes original and installed bytes. The exact producer is `79c515ee26f363f4dc969d8df408f791e33e143c`. The newer P1.4 head `f81fae8c505b70bdda48223da24e7404dde82bee` was checked before adoption: neither TrueD provider was present, accepted, or selected in its current compilation stages.

## Source layering and unique declaration ownership

`POINTWISE_EXTRACTION.json` and `HISTORICAL_POINTWISE_EXTRACTION.json` retain the
original source blobs, exact byte intervals, and hashes of the 21 separated
declarations. Twenty current declaration blocks remain byte-identical; the
remaining `profile_bounds` block has only the recorded field-notation whitespace
repair. Their statements, names, and actual weight formulas are unchanged.
The verifier checks the repaired postimages by exact byte splices against the
frozen failed commit, then checks every historical extraction block against its
original preimage. Historical extraction, adoption and review records are not
silently retagged with the new hashes.

The original source-only archives remain untouched. The complementary files in `provider-postimages/` remove precisely the separated declarations and import their new common owner. They are **migration postimages, not accepted full providers**. Use those postimages when a full historical provider is later adopted; importing an unchanged archived provider together with its new declaration owner would create duplicates.

## Verification gate

The P1 compiler must first verify the existing dependency sources, objects, trace files, runtime and configuration. In particular, the 19 reused P3 objects must match their recorded acceptance hashes, and stock guarded `lake --no-build build +ImbalancedChen.Part3ProperPowerChartSum:olean` must succeed without changing their fingerprints.

Only selected new owners may then use the unchanged Batch13 normal-build, independent kernel replay, and full environment-owned declaration/type/axiom audit APIs. Dependency modules are not relabeled as newly accepted owners. Missing or incompatible cache evidence is a hold; no synthetic traces or fabricated normal receipts are permitted.

## Remaining P1.5 obligations

The new comparison does not bound the remaining signed von Mangoldt source itself. The original Atlas still contains its trim, medium, remaining Type-I, and chart-weighted proper-power terms.

The bare source comparison is not an equality with the old `properPowerReserve`: that reserve also carries the original extra `eta`, dyadic `psi`, and each chart's `roughWord (beforeHBCutoff K js)`. Their finite dictionary and corresponding original-weight instance must be supplied before that separate reserve is marked paid. In particular, `eta` is not an idempotent indicator, and the original minus sign on the proper-power reserve remains unchanged.

The mathematical source is the fixed 20261106 manuscript, Appendix D.3 / coefficient appendix proper-power deletion, at `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`. No manuscript-external theorem is newly formalized by this work.
