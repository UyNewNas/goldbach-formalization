# P1.4 — true-d actual signed delta to the owned 87-source raw trim invoice

**State:** SOURCE_ONLY / UNEVALUATED / UNCOMPILED. Parent P1.4: **YELLOW**.

## Pin and restart
- Exact prior P1.4 durable HEAD: `31b306cb870f92b3373a5fd4a8b711c29fe0bc59`; prior source `P1Full87ActualTrueDOrderedGap.lean`, blob `cba8f36679715aba611ebf5499d518eab8cde9f1`.
- This task branch: `chatgpt/p1-full87-true-d-owned87-invoice-20261120-0910`, branched from that HEAD. New source commit `85dd6f5a50282d11a81015483f0c9d9810f55067`.
- Candidate Lean source: `docs/source-only/20261120-true-d-owned87-invoice/P1Full87TrueDOwned87Invoice.lean`, 146 lines, blob `e79f478556138b88fba6a597600476ae87642b32`.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, verified blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Locked: Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Read `lean-toolchain` and `lake-manifest.json` at prior HEAD; no modification. `c=49044063/25000000`, `K=8452171/1250000` unchanged.

## Actual new mathematical step
Previous packet connected a single signed TRUE PHYSICAL d coefficient
`deltaRho = rho_LICENSED - rho_RAW` to the separate LICENSED and RAW
rank-eight frontiers and the original ordered rank-four stopped events.
But its RAW rank-eight term was still an opaque total, not the saved
87 original owner-cell source partition.

Read and reused *existing* source-only theorems:
- `P1Full87ActualTrueDOrderedGap.actual_full87_true_d_eq_ordered_events_and_frontiers`;
- `P4AOriginalFull87RawTrimSignedHighQ.actual_raw_highQ_unowned_trim_omitted`;
- `P4AOriginalFull87RawTrimSignedHighQ.abs_raw_highQ_minus_trimmed_le_outside_invoice`;
- original `P4AOriginalFull87SourceDictionary.Cell` and `sourceStates` with owner `ownerAtPrefix`.
The archive table and source dictionary are independently read: `Cell`
has 87 original classes with `globalIndex : Cell -> Fin 87`,
`globalIndex_bijective`; `archivedRecordForOriginalCell` is
**only provenance**, not physical gain certification.

Set (D) to the TRUE physical small/rough support union, and
(A=\sum_{d\in D}\delta\rho(d)G(d)) with the original `highQTest`.
Let (L_8) be the unchanged **licensed** rank-eight signed frontier,
(V_{5,6}) the ordered original **RAW minus LICENSED** stopped event,
(U_8) the **raw** unowned frontier, (T_{87}) the sum of the **raw**
owned strict-trim List contributions over all 87 actual source cells,
and (O_{87}) the separate raw owned-but-omitted List sum.

First new SOURCE_ONLY proof body establishes exactly
[
  A = L_8 - (U_8+T_{87}+O_{87})-V_{5,6}.
]
Neither the licensed frontier nor the unowned/omitted raw terms are
declared zero. The physical sign is LICENSED-RAW; hence the ordered
RAW-LICENSED stops have the negative sign. The same actual root and
original beta-attached `rawSignedHighQ` are used on each source state;
the List filtering preserves occurrence multiplicities.

Second new SOURCE_ONLY proof body produces an explicit *single* absolute
invoice using the previously established raw outside-trim budget:
[
 |A-(L_8-V_{5,6}-T_{87})|
 \le \mathrm{rawOutsideHighQInvoice}.
]
There is no second charge of the same outside-list residual, and
nothing implies that this finite absolute budget is small relative to
(H_N). These two candidate theorems are a literal link from the true
physical d difference to RAW's *owned 87-cell* production, not an
identification of numeric saved-archive values with arithmetic mass.

## Checks actually run
- GitHub source create + remote read: blob `e79f478556138b88fba6a597600476ae87642b32`, 146 lines; 2 theorem proof bodies.
- Static forbidden proof escapes: none found in this file.
- `lean --version`, `lake --version`, `elan --version`: exit **127** each (command not found).
- `/sys/fs/cgroup/memory.max` = **4294967296** (4 GiB); no GitHub DNS from this container.
- The exact fixed-pin source-only dependency closure could not be staged or elaborated. No local `lake env lean` was attempted after these environment checks. Therefore **UNCOMPILED**, not kernel checked.
- No CI/Actions, Codex, work on the user's computer, changes to main/master, merges, force pushes, pin upgrades or resource expansion.

## Still open
1. Compile this and its transitive source-only import closure under the fixed toolchain; correct real Lean errors (cannot infer elaboration from source text). Also replay kernel and audit transitive axioms separately.
2. Prove the licensed eighth frontier's original changed/tagged/BOTH/rank9/inherited coverage and their actual occurrence source membership; the raw 87 owner partition alone does **not** identify the two trees' states.
3. Determine whether actual delta coefficient is in the manuscript's **single** allowed PP coefficient class. Generic absolute coefficient bound 2 is not a proof of unit-bound eligibility or of the requisite causal/factorized class.
4. Authenticate one common smooth (W_N), original exact coprime mean, fixed-before-N quantifiers and one signed PP input for the same licensed/RAW delta or a genuinely eligible coefficient; register rather than prove external analytic input.
5. Pay actual outside trim invoice, lower-half three corrections, ordinary continuation integral, modulus-prime correction, primitive discrepancy, saved87 archive, both compiler/density reserves, all relative to (H_N).

Next local mathematical action: inspect actual **licensed** eighth frontier provenance against the original saved 87 cells; do not reuse raw owner partition on licensed states without proof. Then examine the real coefficient licence.
