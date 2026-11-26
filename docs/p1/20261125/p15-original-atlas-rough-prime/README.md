# Original singleton Atlas rough-prime reserve: exact source adoption

This directory records four new canonical owners for an existing rough-prime
reserve solution. It adds **no new arithmetic proof body**. The sixteen extracted
declaration blocks retain their original names, namespaces, statements, proof
bytes, attached documentation and trailing whitespace. The reserve-branches
provider is copied as one complete, unchanged file.

The status is **source adopted, uncompiled**. The static report checks source
identity and reachability. It grants no Lean elaboration, kernel replay, accepted
object, cache-readiness, or P1.5 completion credit. No compiler job, installer,
driver, or Git publication is performed by this adoption.

## Owners and precise scope

| New canonical owner | Exact adopted material | Declarations | Direct imports |
| --- | --- | ---: | --- |
| `P1OriginalSingletonSupportData` | Four original LogCollarFamily support declarations | 4 | `P1OriginalSingletonPointwiseData` |
| `P1OriginalSingletonCutoffData` | Original `active_psi_scale_each` plus the first six declarations of the frozen repaired UniformCutoff | 7 | `P5OriginalPrimeChartHBWitnesses` |
| `P5OriginalPrimeAtlasReserveBranches` | Complete original provider, including its original import/header | 11 | `P5OriginalPrimeAllGroupHBDiscrepancy` |
| `P1OriginalSingletonAtlasRoughPrime` | First five original t06 singleton rough-prime declarations | 5 | SupportData, CutoffData, SmoothLicence, ReserveBranches |

There are 27 declarations in total: 25 public declarations and two original
private cutoff helpers. The helpers keep their lexical names and proof bytes;
Lean's generated private-owner module identity necessarily follows the new
module. Neither remaining UniformCutoff declaration refers to those private
helpers. All public qualified names retain their historical namespaces.

The two payment terminals remain in
`ImbalancedChen.P1OriginalSingletonRoughPrimeReserveZero`:

- `exists_original_singleton_roughPrimeReserve_zero`;
- `eventually_original_singleton_roughPrimeReserve_sum_zero`.

For **fixed** `K : Nat`, `1 <= K`, `kappa : Real` and `kappa < 1`, the first
terminal selects `N0 >= 2`. For every `N >= N0`, it then permits arbitrary
`B : Nat`, `kappa0 : Real`, `Q : Finset Nat`, `rho : Nat -> Complex`, and every
`js` in the original `chartBank (2*N) 1`, and proves

```lean
roughPrimeReserve (actualLicence kappa B N)
  K (2*N) N kappa0 Q rho js = 0
```

The second terminal sums this equality over that exact chart bank. `K` and
`kappa` precede the threshold; they have not been moved after it. There is no
parity, modulus-level, coefficient-size, or positivity-of-`kappa` assumption.
The cap remains `2*N`, the residue target remains `N`, and the original complex
signed coefficient and exact count/coprime-mean expression remain unchanged.

## Manuscript alignment and existing proof route

The manuscript pin is
`UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/coefficient-appendix.tex`, Git blob
`10f3e2efb2074a9b97148a5151956e1d450be13f`. Lines 513–520 insert the original
nonnegative dyadic partition, fix the common roughness threshold before HB, and
state that every original prime eventually exceeds it.

The adopted proof already follows that route. Nonzero `actualLicence` gives the
strict source floor `N^(1-kappa) < p`; nonzero original chart terms give their
own same-word psi windows. For `N >= 2`, the existing `doubled_cap_floor` converts
the source floor to the cutoff supplier at ambient cap `2*N` with exponent
`(1-kappa)/2`. The repaired uniform cutoff places `beforeHBCutoff K js` strictly
below every original prime. `roughWord_one_on_prime_word` then makes the defect
factor zero term by term. No estimate replaces the signed coefficient or the
coprime mean, and no prime-power or divisor calculation is repeated here.

The adopted support, cutoff and terminal statements are existing proofs. This
change addresses their import and source-ownership packaging. It does not add a
mathematical assumption or replace a missing historical provider with a new
proof.

## Source selection

`SOURCE_VERSION_SELECTION.json` binds the t06 freeze and the t05 dependency
registry. The freeze explicitly selects the repaired UniformCutoff source from
`b6079159c2af12cb5c67a0055ef1db9d1e60f072`:

```text
docs/source-only/20261112-resume/t05/rank2-dependency-audit/repairs/
  P5IndependentTestPrimeChartUniformCutoff.lean
SHA256 d849269829a19b3b733082a0fe54291b0f920cc752ec900469cd49b3c8cd17c1
```

Its first six declaration blocks are also byte-identical to the later hidden
variant. That variant's only file difference qualifies `jointPresievedSigma`
inside a later, unadopted selected-W theorem. This adoption uses the original
frozen t05 selection throughout.

`EXTRACTION_MANIFEST.json` records zero-based, half-open UTF-8 byte intervals for
each source block, its destination interval, its exact hash, and the complementary
postimage deletion. `ADOPTION_MANIFEST.json` binds the complete provider, all four
destinations, the source records, and the protected earlier files.

### External first-compile dependency repair

While this source adoption was being verified, the parent task repaired a real
first-compile error in the existing `P1OriginalSingletonPointwiseData` dependency:
the field-notation dot and `trans_eq` name had been split across lines in the
original extracted `profile_bounds` proof. The parent task joined them, without
changing that declaration's statement. `EXTERNAL_DEPENDENCY_REPAIR.json` binds
the parent's `FIRST_COMPILE_REPAIRS.json`, the original pinned source, and the
single exact byte splice. The verifier reconstructs the entire current dependency
from that pinned preimage before checking it.

All 22 original protected fingerprint rows remain as recorded; 21 current files
still match those bytes, and this one dependency has the explicit external repair.
None of the four rough-prime owners, sixteen extracted blocks, original sources,
or earlier postimages was changed. The other phase1 repair concerns TrueD and is
outside this four-root source closure.

The current revision binds the exact phase2 six-owner/168-source closure and its
source-only verifier. `EXTERNAL_DEPENDENCY_REPAIR.json` also records the nine
accepted dependency postimages, the original finite-source layering, and the
five first-compile expression repairs in Core/Mellin. Those changes are upstream
source changes; none rewrites a rough-prime proof. The parent phase2 pin
synchronization flag is now false because the actual current source fingerprints
are checked against that pinned upstream closure.

The nine existing dependencies are the exact previously selected postimages
from `a392cd8efcf4f0b4adf3d12f2d8db41370309ed3`. The complete authoritative adoption
manifest remains in `p15-existing-atlas-dependencies/`; no new arithmetic body is
created here and no equality between old/new elaborated types is asserted.

The finite-source layering moves the original nine declarations to the single
Core owner, leaves the complementary sorted theorem in the inactive old Finite
provider, changes only the required AllK import, and preserves Family in full.
The original Core extraction is checked on the published preimage. The current
Core has exactly two recorded expression repairs; the first Mellin epoch has
three, as bound by unchanged phase2 `FIRST_COMPILE_REPAIRS.json` (SHA-256
`9b66ab9d6a8813612f77bdd109a0159c4e46836b5ce3aea980ad3a30d7f3b5bd`).
The later single-splice Mellin epoch is recorded separately below. Both epochs
preserve all declaration headers and literal imports. The phase2 verifier
reconstructs the fixed `ef450…` first-correction sources and then their original
`e1a80f6c306b58eadf2a8c6f58f4cbc7385e32d5` preimages; source verification still grants
no Lean acceptance.

The original `STATIC_VERIFICATION.json` and its duplicate remain unchanged as
the earlier Pointwise-only, 362-source static receipt. The later pending
362-source inventory, which already included the nine adopted postimages but
had not yet completed static revalidation before layering, is preserved in
`snapshots/source362-before-layering-sync/` and explicitly labelled pending.
Its old pass receipt is not relabelled as acceptance of that mixed stage or the
current 144-source revision. `SOURCE_LAYERING_REVISION.json` records the exact
set change and the two retained source-row changes. A fresh actual run writes
`CURRENT_STATIC_VERIFICATION.json` separately.

### Separate second Mellin correction epoch

`SECOND_COMPILE_REPAIR_BINDING.json` records the upstream second repair manifest
(SHA-256 `8607ba1bc2f7e3d65d9172647beeb4e9f4292a3247e29b6d26dd338d4fc4c43d`)
and the exact prior rough metadata bindings. The only later source change is
Mellin: from its fixed `ef450be0a89b6a3f88b3bca19d06e04e7967fa18` preimage,
`integrable_zero Ω ℂ μ` becomes `integrable_const_iff.mpr (Or.inl rfl)`.
The current source SHA-256 is
`7009aea59f5853791f869c46214d85af2d0dd8e43fe288e14342880f3e665df7`.
This selects the existing normed-space API instance; the original statement,
goal annotation, and imports are unchanged.

Exactly one row in the rough144 source inventory changes; the other143 rows and
all four rough owners remain byte-identical. Current upstream pins and the
explicit second-epoch record are updated. The verifier reverses those metadata
changes and reconstructs all four preceding metadata files exactly, including
the previous source closure, then checks their fingerprints against the earlier
actual144 receipt. Only the small receipt, verifier and README are saved in
`snapshots/source144-before-mellin-second-repair/`; another full source graph
snapshot is not duplicated.

The original first repair manifest and all original source/extraction records
remain intact. Core keeps its original accepted source identity and is not
requested for recompilation. This source-only check does not revalidate Core's
kernel acceptance or infer acceptance of the new Mellin source. The current
receipt reports the first epoch and the one-splice second epoch separately.

## Future-provider postimages

The four files in `provider-postimages/` are exact complementary deletions plus
one owner import. They are **future migration material, explicitly uncompiled**;
they are not included in the canonical source closure.

| Future provider | Preimage used | Remaining scope |
| --- | --- | --- |
| `P5ActualSingletonLogCollarFamily` | Existing phase2 combined postimage | Original remaining derivative/profile material, with the four additional support owners removed |
| `P5IndependentFourPrimeChartCutoff` | Original t05 source | Original remaining rank-four interfaces |
| `P5IndependentTestPrimeChartUniformCutoff` | Frozen repaired t05 source | The two original grouped/selected-W interfaces |
| `P1OriginalSingletonRoughPrimeReserveZero` | Original t06 source | Only `eventually_original_singletonAtlas_roughPrime_paid`, byte-preserved |

Future complete-provider adoption must use these complementary postimages
together with the already recorded pointwise/smooth migrations. Importing an
unmodified historical provider would redeclare migrated public names. The
earlier phase1/phase2 postimages have not been overwritten.

The last physical `singletonAtlas` caller still needs its original MiddleTensor,
Params, products and free interfaces. This adoption does not import, compile, or
replace that physical chain. The exact old terminal remains available in its
postimage for a later provider migration.

## Source closure and verification

`SOURCE_CLOSURE.json` v2 has four roots and **144 canonical project modules**:
four unchanged rough-prime owners and 140 existing dependencies. Every existing
dependency is already in the phase2 six-owner/168-source closure. The
phase2-plus-rough union is **172** modules; the phase1-plus-phase2-plus-rough
union is **353**. The original22 protected-input rows remain unchanged as
historical pins, with 21 current matches and the one explicit Pointwise repair.

Relative to the preserved pending362 inventory, 219 modules leave the active
import closure and Core enters as an already recorded phase2 dependency. Among
retained rows, only AllK's source/import fingerprint and Mellin's repaired source
fingerprint change. All four rough-prime owners remain byte-identical. The
current graph has no missing project imports or import cycles. These counts
describe source reachability; they do not establish compiled-object availability
or authorize rebuilding an existing accepted owner.

From the repository root, run:

```sh
python3 docs/p1/20261125/p15-original-atlas-rough-prime/verify_source_reuse.py
```

The default command is read-only. `--write-report` writes only this directory's
`CURRENT_STATIC_VERIFICATION.json`; it never overwrites a historical receipt.
The verifier checks original Git objects, all sixteen extracted block intervals,
complete-provider identity, exact complementary postimages, frozen version
selection, original protected bindings, the preserved pending362 snapshot and
its earlier nine-source reconstruction, all current144 source fingerprints and
imports, forbidden proof tokens, and a lexical canonical ownership scan for the
25 public names.

It also invokes the pinned phase2 **source-only verifier**, without write flags,
and requires its entire output to equal the pinned current receipt. That reuses
the existing exact-source checks for the nine accepted postimages, original Core
layering, and both Core/Mellin repair epochs, plus the 18 fake-only readiness cases.
No real driver, installer, compiler service, Lean, Lake, or cache readiness call
is executed. The current140 shared source rows must equal the phase2 source
rows. Source identity and lexical ownership remain distinct from actual Lean
elaboration of the new imports.
