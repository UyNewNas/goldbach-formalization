# Saving19 original_data_checks fastDet representation candidate

## Status

This is an **uncompiled performance candidate**, based on P1 source commit
`298670f119d24874b719facb3ef756f1e01223a1`. Production files and literal data are unchanged. No Lean or remote
compilation was started. No speedup or successful certificate evaluation is claimed.

## Exact change

The sole candidate Lean file is `ImbalancedChen/P2OriginalSaving19Original28918.lean`.
It adds exactly one import:

```lean
import ImbalancedChen.P2Winner9RowArithmeticChecker
```

It replaces only the proof body of the existing closed theorem:

```lean
theorem original_data_checks : ∀ r, RowDataChecks r := by
  simp only [RowDataChecks, ← P2Winner9RowArithmeticChecker.fastDet_eq]
  decide
```

`candidate.patch` is the complete diff. No declaration is added, removed or renamed.
All public statements, all definitions, and every other proof body remain unchanged.
Reversing this import and this one proof-body substitution recovers the original
source bytes exactly.

## Mathematical and data content retained

`RowDataChecks` contains exactly two `(edgeQ r).det` occurrences: determinant
nonvanishing and the physical-volume equality. The existing generic interface is:

```lean
theorem fastDet_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : fastDet A = A.det := by
  unfold fastDet
  rw [forceFn_eq _ (fun r k => forceFn_eq _ forceRat_eq r k)]
  exact fastDetCore_eq A
```

The candidate requests reverse rewriting with this existing equality at dimension
8 over the rationals, then requests the same closed finite proof with `decide`.
No determinant implementation or correctness theorem is introduced here.

The complete unchanged `RowDataChecks` conjunction still requires:

- determinant nonvanishing;
- every original vertex's full `PhysicalQ` condition;
- positive total gap;
- physical-volume equality and mean-gap equality;
- every factor's computed weighted mean;
- every factor maximum's domination and attainment;
- the original Jensen evaluator equality;
- the original geometry Q96 floor equality.

The universal quantifier remains over every original row. No geometry, mean,
maximum, Q96 or other conjunct is deleted or replaced by a premise. No source
literal or archive record is changed.

## Verification boundary

Static checks confirm exact preservation of the statement, definitions, other
proofs, declaration headers and literal references. The patch passes
`git apply --check --whitespace=error-all` on the specified P1 snapshot.

The `simp only` tactic has **not** been elaborated. Although the retained definition
contains the two intended determinant expressions and the reused theorem is generic
in `n`, actual rewriting under the outer universal binder, subsequent decidability
elaboration, runtime and kernel acceptance still require Lean validation. This
candidate does not assert that the transformed goal has already been observed.

The parent identified prior accepted source prefix `bef1fb6c...`. That historical
source/`.olean` acceptance is not transferred to the current P1 dependency version.
The current `P2Winner9RowArithmeticChecker` and its dependency chain must be
reaccepted in the actual target environment. This directory does not copy any
historical `.olean` or assign acceptance credit.

## Provenance

Original row module SHA-256: `ed126d258139d3ee671f164852f816255138657a035f74af67a0f610637c24b4`.
Current checker SHA-256: `bef1fb6c8358849f8a1cfdd320a30624235facad9ae1d7a285f1e773e1c14138`.
Unchanged `RowDataChecks` slice SHA-256: `1c0825496d7a015008a55dd0e33985429b4cdd319e5fc32fa09ef059ad3db04f`.
Candidate SHA-256: `fc0fe7cff7803afa5ef2b87a653fa384071988c485799b524f784b93f5790c49`.

`SOURCE_MANIFEST.json` records absolute paths, Git blob IDs and source commit
verification. `STATIC_AUDIT.json` records precisely which checks ran and which
Lean/resource checks remain unperformed. `build_candidate.py` reproduces this
single-file overlay without invoking a compiler.
