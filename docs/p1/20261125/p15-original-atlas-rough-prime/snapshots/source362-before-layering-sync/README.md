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

The parent task will synchronize phase2 comparison pins and accepted dependency
postimages before the final publication receipt. This directory explicitly marks
that synchronization as pending. Its present static report describes the exact
current source snapshot; it is not a receipt for any later dependency revision.

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

`SOURCE_CLOSURE.json` has four roots and 362 canonical project modules: four new
owners and 358 existing dependencies. Every existing dependency is already in
the phase2 five-owner source closure. The phase2-plus-rough union is 390 modules;
the phase1-plus-phase2-plus-rough union is 479. There are no missing project
imports or project import cycles. These counts describe source reachability;
they do not establish compiled-object availability or authorize rebuilding an
existing accepted owner.

From the repository root, run:

```sh
python3 docs/p1/20261125/p15-original-atlas-rough-prime/verify_source_reuse.py
```

The default command is read-only. `--write-report` writes only this directory's
`STATIC_VERIFICATION.json`. The verifier checks original Git objects, all
extracted block intervals, complete-provider identity, postimage reconstruction,
frozen version selection, protected source bindings, all closure fingerprints
and imports, forbidden proof tokens, and a lexical canonical ownership scan for
the 25 public names. It never invokes Lean, Lake, a compiler service, or an
installer. The ownership scan is source-level evidence; it is not a claim that
Lean has elaborated the new import arrangement.
