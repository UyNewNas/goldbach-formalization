# P1.5 Remaining Type I geometry: exact syntax repair

Status: **CORRECTED SOURCE; V3 WHOLE-MODULE PROBE PENDING; NO NORMAL OR KERNEL ACCEPTANCE.**

## Actual diagnostic history

The original full source was submitted at AK
`d4f88a20262af7d54ed0e6e58dfc533496c595e3`, job
`job_e7137c6b21bf4a48ae84662c77b633af`. Lean returned exit 1 because
`R` was ambiguous between the root real-argument function and the original
dyadic chart scale. Its dependent `linarith` context contained elaborator
placeholders. Source, result and compiler log remain bound to this run.

At AL `13981b6d4b60ed3d4d36b74ff2522fdce7811de0`, job
`job_87513dc92a5b4341b0a9bc70b046163c`, a local notation correctly resolved
the original scale. The complete module still returned exit 1: the new
notation token also captured the named parameter in `(R := R cj)`. The
compiler context now contains the intended scale bounds and cube identity;
the remaining reported failures follow the named-argument parser failure.
The raw AL result is 39,001 bytes / SHA256
`8a484f37d462a8c22aefa2adba2d552263f980c0d271e24e5fcfb0cf6188ed54`.

Both attempts passed source/object/evidence/Git preservation checks and
rebuilt no existing project module. Both remain failed.

## Current source

Relative to the original AJ source, the source has exactly two syntax edits:

```lean
local notation "R" => P5Z.ExactOriginalSmoothDyadicPartition.R
```

and the original named-argument call is spelled:

```lean
(«R» := R cj)
```

The escaped identifier still denotes the original parameter named `R`.
All five theorem headers remain byte-identical to the original. Four proof
blocks are byte-identical; the numerical-reserve proof changes only that
parameter's spelling. No premise, bound, physical target or quantifier order
changes. The corrected source is 11,341 bytes / SHA256
`2c3963d7847dc99aa809474b9b3ae387d0e75b67e37743682d3d9e53202dfa77`.

Its exact 141 dependencies remain inside the original accepted AG144 scope.
Geometry remains outside the original 21-target registry. The four public
source theorems and one private helper are not prefilled compiled counts.

## V3 whole-module probe

The immutable AI reader and original serializer/guard are unchanged. The
probe requires that the source equals the exact two edits above. The
complete original AK and AL failed-probe trees are now both protected,
with their original result fingerprints and failure identities. The new
source origin names the new probe publication, while AJ/AK/AL remain
separate historical identities.

The probe freezes a complete source outside the canonical project, requests
no object output and builds no dependency. It preserves old accepted source,
object, audit, installation and Git context and all 21 empty Geometry slots.
It never overwrites a prior attempt. A successful probe will still need a
separate exact installation, normal compilation, all-owned kernel audit,
final no-build readiness check and original-run readback.

Two new local Python boundary tests passed for the exact second edit and
AL failure binding. They are not Lean validation. Earlier unchanged test
suites were not repeated. The earlier namespace and v2-probe review is
retained under its historical scope; current source and v3 scope are recorded
separately.

The original registry remains **18/21 accepted, three proper-power HOLDs**.
TrimLog remains separately accepted under its original AI acceptance. P1.5
is open. A separate exact historical coefficient-dictionary probe uses its
own 288-project-dependency scope and does not claim a signed medium bound.
