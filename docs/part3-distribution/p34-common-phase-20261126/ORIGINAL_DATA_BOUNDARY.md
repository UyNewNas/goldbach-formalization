# P3.4 exact original-row boundary audit — 2026-11-26

## Decision

The new commit `c5ccf81ce1a55e2dafeca0116cd70177bf169504` does **not** supply `OriginalMediumPhysicalE3Block.FixedBlock`, `Rectangle`, the original factor-window definitions, or an actual `OriginalData` row. It recovers the existing signed Poisson-window and dyadic-series core. It is useful neighboring work, but it does not close the original-row obligation recorded in `REMAINING_BOUNDARY.md`.

`OriginalData` itself is **already present** as an unchanged, eleven-field declaration. The immediate missing source is the genuine physical block supplier. The smallest next source-recovery target is therefore the **6,566-byte** `Part3OriginalMediumPhysicalE3Block.lean` with SHA-256 **`1ed9fec9d526f866fff9a29f9d8d0fa96d63def2a8b1e4e7a42ad759a8989982`**. Recovering that file would establish the first definition boundary; it would not, by itself, certify the whole original-row closure. The genuine `sCarrier` also reads the original `FactorData` window supplier, which remains missing in the existing source atlas.

No Lean source was edited or compiled in this audit. No cloud task, fetch into the local Git database, branch mutation, accepted-scope rerun, or broad historical/archive recovery scan was performed. The only written artifact is this report. The root agent owns current acceptance receipts and the newly assigned precise source-recovery task.

## Frozen evidence

The local source observations below use repository `/workspace/library-files/p34-proof-work`, baseline commit `b945f39a1e355ff4fcca9865ab59ffc97f2172c0`. The manuscript remains `paper/release-20261106/en/analytic-appendix.tex` at `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703` in `UyNewNas/chen-imbalanced-semiprimes`.

| Evidence | Exact identity |
|---|---|
| New core source commit | [`c5ccf81ce1a55e2dafeca0116cd70177bf169504`](https://github.com/UyNewNas/goldbach-formalization/commit/c5ccf81ce1a55e2dafeca0116cd70177bf169504), author timestamp `2026-11-26T01:49:44Z` |
| New core commit tree / parent | `5d2278542eead488abf6451eea876a5125ecc490` / `bd3a25c232b00151d000778f85f9d5a385964299` |
| New module | `ImbalancedChen/Part3OriginalCommonPoissonLanesCore.lean`, Git blob `042b6d813a23b3382dbc70b5696ba11ad76b7c97`, SHA-256 `d0b09f910ef866f36f400445cc3a3c1ddcbafe151ef952c2cb780bbb87f89bda` |
| Original Poisson-lanes donor | `docs/source-only/20261102-resume-30o/medium_spectral_dictionary/Part3OriginalCommonPoissonLanes.lean`, 16,078 bytes, Git blob `00a797ac77cb444479ce097f4b44c56930489e32`, SHA-256 `1c15c03a6fa6a1c188e8f5f2498aaee5f14da01b05e48676b263f9f3df1919e4` |
| OriginalData donor | `docs/source-only/20261102-resume-30o/medium_spectral_dictionary/Part3OriginalCompletedReciprocalSource.lean`, 15,467 bytes, Git blob `a99ba7e76f13c45beac5bd459334c9a75dc7c5a7`, SHA-256 `cc3785b59a379b1d39d79a09be87cb7d3b46acf9ee4510ebe0149feb9786d1b5` |
| Existing original packet-row consumer | `docs/source-only/20261102-resume-30p/medium_spectral_dictionary/Part3OriginalPrimaryPacketRows.lean`, 13,509 bytes, Git blob `4281ec328d4c3a0f4cb9ca21c2f0923604e6e47a`, SHA-256 `a3e1953d1a521d55aa62c5911c7b524a2dd61210417d891027ec28900f84e287` |
| Registry pin for the missing physical block | `docs/source-only/20261102-resume-30j/s3_cauchy/REGISTRY.json`, Git blob `66f2cbaaca66d57378f6c331b5283ad325c8d94e`, SHA-256 `cd2c6c1b118d123c33ff2ef7c01c4a3329d075e4f89956d1a7038095f6ade0da` |

These exact donor hashes were recomputed from the existing files. The new commit and its six changed paths were read through the GitHub connector. The canonical `ImbalancedChen/Part3OriginalMediumPhysicalE3Block.lean` contents request at the exact new commit returned GitHub 404. That is a statement about this exact canonical path, not every possible hidden attachment or archive.

### What the new commit actually adds

The commit adds one Lean module plus its closure/intake documentation, an execution plan, and a verifier selector. Its new Lean file imports only:

```lean
import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.InfiniteSum.Group
```

Its intake record preserves **17 named declarations, six definitions and eleven theorems**, in the original namespace `ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102`. It takes original donor lines 32–177 and 185–216. The two preserved source segments independently hash to `792cc6c97452f5510940ecfca6c4ef6a552ca2613d5e95a9492b737b15dba3cc` and `44cbcf7e1dfd5dcb36d319883646565103dcc7481abaff6160bd4482c7b1b9e2`.

The `CLOSURE.json` has 53 project modules, with strict replay selecting only the new core. Its only original-named module is this new core. Neither the physical block nor `OriginalCompletedReciprocalSource` is in that closure. The record explicitly does not claim replay of every historical provider or the entire external kernel closure. Its `SOURCE_INTAKE.json` points to the previously accepted Physical Poisson source hash `3f0218c06362bdd97cdc178e006f646c73e5cd4cd8dc18fc07b590fceffc2193` and the historical `baseline-c509267-report.json` receipt; the latter records that source under an accepted baseline. No repeated provider proof is required by this audit.

At this commit snapshot, the message and README explicitly leave acceptance pending, exclude `globalCutoff`, `OriginalData`, full six-family coupling, actual spectral `PacketData`, and `hkernel`. This report makes no claim about the later cloud status. Even a subsequent successful receipt for this same core cannot supply definitions that are absent from its source/import closure.

## The actual OriginalData declaration

The original declaration is at lines 42–53 of `Part3OriginalCompletedReciprocalSource.lean`, within `ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102`:

```lean
structure OriginalData where
  block : FixedBlock
  atom : MediumAtom
  roughCutoff : ℝ
  key : Key
  small : ℕ
  rectangle : Rectangle
  smoothLeft : ℕ × ℕ
  smoothRight : ℕ × ℕ
  polarS : Fin 4
  polarR : Fin 4
  polarN : Fin 4
```

There is no assumed packet equality, support theorem, coprimality conclusion, spectral bound, or preselected nonempty carrier among these fields. There is also **no field identifying `atom` with `block.atom`**. The scale and arithmetic residue use `block.atom`, whereas the coefficient and factor carrier use `atom`. Any source-preserving intake must retain both fields and their existing roles. A later actual branch constructor must justify its chosen values; an unrecorded identification must not be introduced into the type.

The `Key` in this declaration is the existing `MediumGlobalDyadicOwnership20261028.Key`, with exactly six natural fields `s t u v d w` and `deriving DecidableEq` at lines 20–22 of `docs/source-only/20261028-resume-30b/medium_s3/Part3MediumGlobalDyadicOwnership.lean`. Its text is available. Importing its whole current parent file, however, inherits the unavailable `Part3MediumInstalledSplitConverse` chain. An exact definition-only move could keep this same type and namespace; inventing a substitute key is unnecessary.

The physical-block registry identifies the `OriginalMediumPhysicalE3Block` namespace and its `FixedBlock.rectangleSum` consumer. The original `Rectangle` definition body is not recovered in the inspected sources; its exact supplier/export must be checked when the registered physical block source is recovered. Consumer field names below are known, not a reconstruction of that unseen structure.

### Field-to-definition boundary

| Actual expression | Existing source and meaning | Required genuine supplier |
|---|---|---|
| `D.bScale = D.block.atom.U * scaleR D.key` | CompletedReciprocalSource line 57; `scaleR k = (2^k.v : ℕ)` in MaskedOuterEnergy lines 37–44 | `FixedBlock.atom`, original `Key`; positivity uses `D.block.U_pos` |
| `D.cScale = D.bScale * scaleS D.key` | CompletedReciprocalSource line 58; `scaleS k = (2^k.u : ℕ)` | Same original block and key |
| `D.fScale = 2 * D.block.atom.U / D.block.atom.Q1` | CompletedReciprocalSource line 59 | Original `FixedBlock.atom`, `U_pos`, `Q_pos` |
| `D.sCarrier = commonS D.atom D.roughCutoff D.key D.small D.smoothLeft` | CompletedReciprocalSource lines 60–61 | Original factor-window definitions, described below |
| `D.hBound = Nat.ceil D.block.H` | CompletedReciprocalSource line 62 | Actual block height `H` |
| `D.omega = originalOmega D.block D.rectangle` | PrefixDictionary lines 41–42: indicator of `commonH B R` | Actual `B.hCarrier`, rectangle endpoints |
| `commonH B R = B.hCarrier ∩ Icc R.hLo R.hHi` | MaskSeparation lines 148–149 | Exact signed original height carrier; neither sign is erased |
| `D.lambda r = completedLambda D.atom D.smoothLeft D.smoothRight D.polarS D.key r` | CompletedReciprocalSource lines 64–65; PrefixCompletion lines 319–322 | Existing coefficient definitions, no Poisson `m` argument |
| `D.row r = finiteReciprocalRow 1 D.block.atom.residue D.sCarrier D.hBound (D.lambda r) D.omega` | CompletedReciprocalSource lines 66–67 | Genuine block residue and exact two masks, plus the existing finite reciprocal API |

The coefficient chain itself is present: `gamma2Slot atom s u` is the original `Q2`-support indicator multiplying `atom.gamma2 (u*s)`; `lambdaS` is `diagonal (gamma2Slot atom st.1) (gamma2Slot atom st'.1) e`; the diagonal uses `(a n + root4 e * b n)/2`. `prefixPeriod k = 2^k.u+1`, and `completedLambda` multiplies this same `lambdaS` by `ZMod.stdAddChar (r * (s - 2^k.u))` at that period. These are existing definitions in PolarizedProductCaller, ThreePairPolarization, FrozenReciprocalCauchy, and SimultaneousPrefixCompletion. They must remain the common `s`-frequency coefficient, distinct from the completed Poisson `m` variable.

### The first additional carrier dependency

`commonS` is not a free finite set and must not become one as a workaround. The exact chain in `Part3OriginalReciprocalMaskSeparation.lean` is:

```lean
def originalFactors (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ) :
    FactorData := (fixedBlock k small).factorData atom (strictReceiverCutoff z)

def commonS (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ)
    (st : ℕ × ℕ) : Finset ℕ :=
  (originalFactors atom z k small).roughU.filter
    (fun s => s * st.1 ∈ factorCarrier atom.Q2)
```

The exact `Block.factorData` definition is present in MediumCanonicalFixedBlock lines 130–138. It builds `smoothS/smoothT/roughU/roughV` from fixed closed intervals and the original small/rough prime predicates, retains the physical `Q2/Q3` and rough-product allowed predicate, and uses the original gamma coefficients. `fixedBlock` is present in MediumOwnedCanonicalReindex lines 30–41, with endpoints `2^k.*` and `2^(k.*+1)-1`. `strictReceiverCutoff z = floor(z)+1/2` is present in MediumReceiverCutoffArithmetic line 23. The missing `FactorData`/`Factor` supplier is not replaced by these callers: they still need its real type, fields and definition closure.

## Minimal named missing inputs and exact consumers

This is a boundary map derived from the recorded sources. It is not another 59-module search.

| Supplier / exact expected SHA-256 | Recorded size and original path | Existing consumer proving why it is needed |
|---|---|---|
| `ImbalancedChen.Part3OriginalMediumPhysicalE3Block` — `1ed9fec9d526f866fff9a29f9d8d0fa96d63def2a8b1e4e7a42ad759a8989982` | 6,566 bytes; `.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Phase-Sol6/Part3OriginalMediumPhysicalE3Block.lean` | `OriginalData.block : FixedBlock`; row scales, `H`, signed `hCarrier`; FrozenReciprocalCauchy `signedF`, original carrier and first phase; `FixedBlock.rectangleSum` in the original consumer registry |
| `ImbalancedChen.Part3OriginalMediumDoubleLambdaColorWindows` — `e034925f0c0fe6b3fbc1e74966848dadd66591910e7a074403151dbbb3e66f7a` | 7,882 bytes; `.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Charts-Sol6/Part3OriginalMediumDoubleLambdaColorWindows.lean` | Original `FactorData`/`Factor` API used by `Block.factorData`, `originalFactors`, and actual frozen source rows; also the explicitly qualified `diagonalSequence_norm_le_one` used by ThreePairPolarization |
| `ImbalancedChen.Part3OriginalMediumAbelOneCoordinate` — `316889d32fc9a6a48c829b3b69ae08a8387f56bc073324df87c81376d377b297` | 2,382 bytes; `.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Phase-Sol6/Part3OriginalMediumAbelOneCoordinate.lean` | ProductAbel imports this directly; `prefixEnvelope` reads `prefix`; `antitone_weighted_norm` calls `abel_once_norm`; the existing prefix-to-row proof chain retains these names |

The physical-block module's registered direct project dependency is only `ImbalancedChen.Part3DistributionTargets`; its other recorded imports are `Mathlib.Analysis.Complex.Exponential`, `Mathlib.Data.ZMod.Basic`, and `Mathlib.Tactic`. This makes that exact source a small, well-identified recovery target. The registry does not establish that its mathematical statements already compile against the currently selected DistributionTargets version.

The DoubleLambda supplier is already in the old 59-module unresolved union. Its recorded direct imports include the physical block and `Part3MediumClosedChartPolarization`; the latter is not in the resolved module catalog. Consequently, the first two rows are **at least two necessary named supplier files, not a sufficient full import closure**. Recovering the files must precede any claim about their exact internal type/declaration ownership and further imports.

The physical-block hash is an `inspected_supplier_pins` entry in the existing s3 registry, but it is **not** a key of the 59-module unresolved union. The old target-set hash scan therefore cannot be silently cited as a negative byte search for this newly isolated 6,566-byte hash. This report only establishes its registry provenance, absence from the existing resolved catalog, lack of a local visible Lean definition in the inspected source trees, and the exact new-commit canonical-path 404. The root agent has assigned its precise recovery separately.

For whole-file compilation, the old catalog also records the direct chain `OriginalCompletedReciprocalSource → OriginalSimultaneousPrefixCompletion → OriginalReciprocalPrefixDictionary → OriginalReciprocalProductAbel → OriginalMediumAbelOneCoordinate`. Another concrete retained chain reaches missing `OriginalMediumPhysicalE3RowReindex`, SHA-256 `f8c2ba25dfddc1093b41afbd09c731423a5067ce579e1343c045e26d27fffac6`. Its registry imports `OriginalMediumPhysicalQAbel`, 2,731 bytes, SHA-256 `5b61c5f652901a340df798e98dac56de95a3f45eb42e3ea4f7d2093d306771b1`, which in turn imports the physical block and OneCoordinate. These are reasons not to promise that recovering a single source file makes the existing heavy consumers compile unchanged.

## Smallest useful original-row integration contract

No currently verified new supplier closes the first original type boundary. The immediate actionable unit is **recover and identify the exact registered physical-block source**, then read its actual `FixedBlock` and rectangle definitions before choosing a source-preserving intake. The root owns that recovery; this audit did not repeat it.

After the primitive sources are genuinely available, the next meaningful original-row scope should preserve the existing `OriginalData` type and the finite row definitions above, then validate existing consumers in this order:

1. **Literal row identity:** `OriginalData.row_eq_completedBare`, CompletedReciprocalSource lines 77–83. Its proof calls the existing `completedBare_eq_finiteReciprocalRow`, SimultaneousPrefixCompletion lines 346–374. That endpoint keeps the original `commonS`, signed height window, original omega, same completed lambda, and the original `b,c,f` coordinates. It does not assume their equality as a new field.
2. **Actual finite source and witnesses:** `originalSource` at lines 251–253 is the existing `carrier 1` with original residue, `sCarrier`, `hBound`, and signed `fScale` interval. `original_output_licensed` at lines 292–296 derives positive level and residue coprimality from this carrier. `nonzero_beta_has_original_witness` at lines 308–317 obtains a source witness from the same nonzero beta. The `jointBeta` at lines 255–256 uses `beta U (D.lambda r) D.omega`, preserving the source multiplicities.
3. **Existing genuine arithmetic packet rows:** reuse `Part3OriginalPrimaryPacketRows.lean`. Its `rowPacket` at lines 176–181 applies the already existing `dyadicPacket` to `originalSource D` and obtains its positive/coprime level licences from actual membership. The smallest informative endpoint set is `rowPacket_beta`, `rowCoefficient_eq`, `sum_output_eq_rows`, and `nonzero_original_beta_has_row`. They identify the exact beta, signed cusp coefficient and finite output reindexing and produce nonempty rows only from a genuine nonzero original beta.

This is an implementation target once its true definitions are available, not an already accepted result. The currently accepted literal packet, primary arithmetic and dyadic scopes should be reused. Their proofs do not need to be recreated to validate these original-data consumers.

No `OriginalData` constructor selecting `poissonAtlasBlock` was located in the inspected O/P medium-spectral dictionary files: their endpoints quantify over the real original type. The earlier H registry explicitly identifies the actual physical caller `poissonAtlasBlock atom z y k hA Csep j small hd negative` for `FixedBlock.rectangleSum`. A later claim about the whole manuscript branch must make that actual instantiation and its retained labels concrete, rather than upgrading a theorem quantified over `D` into an unrecorded actual branch construction.

The separate oldform/spectral obligation remains unchanged. The primary row source itself says it does not manufacture a `PacketData.kernel` or the normalized Kuznetsov/ABL connection. The 1106 manuscript's lines 689–717 require both actual Poisson frequencies and a common interval/phase; lines 719–727 apply the cusp/packet operation. The new core covers the earlier signed-frequency bookkeeping, while the `OriginalData` chain supplies an actual coefficient row only after its source definitions are restored. Neither establishes the normalized spectral coefficient identity or the dilation-dependent oldform estimate.

## Adjacent finite work kept separate

For coordination only: the original CommonPoissonLanes donor contains an independent eight-declaration passage at lines 218–281, from `negative_block_literal` through `completedKernel_eq_m_lanes`. Its exact 3,291-byte segment SHA-256 is `d0c89e12ba2007afed131e94d7c8307403426424d9c1084593f4a509ec4c9a9a`. It retains the actual negative Fourier argument, c-unit filter, positive/negative dyadic kernels and explicit complementary tail. The first `OriginalData`-dependent joint assembly resumes at line 283.

That finite kernel identity is a candidate for the active P3.1 line, which already owns CommonPoissonLanesCore recovery and acceptance. It is not this turn's selected P3.4 implementation, and it is not a supplier for `FixedBlock` or `OriginalData`. The root has selected three existing dyadic/short common-phase consumers for the next P3.4 proof unit and will reuse the reliable P3.1 actual-interface acceptance at `acfa81c6` / `80560898`. No status or acceptance from those adjacent scopes should change this report's original-definition blocker.

## Source links

- [Current remaining P3.4 boundary](../p34-proof-work/docs/part3-distribution/p34-20261126/REMAINING_BOUNDARY.md)
- [Accepted sub-scope README](../p34-proof-work/docs/part3-distribution/p34-20261126/README.md)
- [Restored source-search limits](../p34-proof-work/docs/part3-distribution/p34-20261125/SOURCE_RECOVERY_RESTORED_P3.md)
- [Existing source atlas](../p34-proof-work/docs/part3-distribution/p34-20261125/source-resolution-recovery.json)
- [New core intake at exact commit](https://github.com/UyNewNas/goldbach-formalization/blob/c5ccf81ce1a55e2dafeca0116cd70177bf169504/docs/part3-distribution/p31-poisson-lanes-20261126/SOURCE_INTAKE.json)
- [New core closure at exact commit](https://github.com/UyNewNas/goldbach-formalization/blob/c5ccf81ce1a55e2dafeca0116cd70177bf169504/docs/part3-distribution/p31-poisson-lanes-20261126/CLOSURE.json)
- [OriginalData source at baseline](https://github.com/UyNewNas/goldbach-formalization/blob/b945f39a1e355ff4fcca9865ab59ffc97f2172c0/docs/source-only/20261102-resume-30o/medium_spectral_dictionary/Part3OriginalCompletedReciprocalSource.lean)
- [Original packet-row consumers at baseline](https://github.com/UyNewNas/goldbach-formalization/blob/b945f39a1e355ff4fcca9865ab59ffc97f2172c0/docs/source-only/20261102-resume-30p/medium_spectral_dictionary/Part3OriginalPrimaryPacketRows.lean)
- [Physical-block source pin at baseline](https://github.com/UyNewNas/goldbach-formalization/blob/b945f39a1e355ff4fcca9865ab59ffc97f2172c0/docs/source-only/20261102-resume-30j/s3_cauchy/REGISTRY.json)
