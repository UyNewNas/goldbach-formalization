# P1.5 Remaining Type I geometry: exact namespace repair

Status: **CORRECTED SOURCE; WHOLE-MODULE PROBE PENDING; NO NEW NORMAL OR KERNEL ACCEPTANCE.**

The original full source was first submitted under publication
`d4f88a20262af7d54ed0e6e58dfc533496c595e3` (AK), task
`job_e7137c6b21bf4a48ae84662c77b633af`. The command returned exit 1:
Lean found `R` ambiguous between the root real-argument function and the
original dyadic chart scale. Its later `linarith` failure was in a context
containing elaborator placeholders from those ambiguities. The complete
original failure result and log are retained in this package and at their
original cloud paths. Preservation checks passed and no existing project
module was rebuilt. That attempt remains failed.

## Single source change

The corrected canonical source adds only:

```lean
local notation "R" => P5Z.ExactOriginalSmoothDyadicPartition.R
```

The accepted `P5ActualLabelledPrimeSmoothCharts` provider uses the same
notation for its `profile_nonzero_support` theorem. All five theorem blocks,
including the private helper, remain byte-identical. The source is now
11,337 bytes with SHA256
`2b982d9bedc546b5ef5f01cc64b0d6401ac5b2a830585e6998924dba74f0d91f`.
No premise or mathematical bound was added.

The original 141 dependencies, lying in the accepted AG 144-module scope,
are unchanged. There is no P3 HOLD in this dependency closure. Geometry is
outside the original 21-owner registry. Its four public source theorems and
one private source helper are not a prediction of the later compiled
all-owned declaration count.

## Corrected whole-module probe

The new probe uses the original AI acceptance reader, serializer and guard.
It verifies that the new source is exactly the old 11,273-byte source plus
the one local notation. It freezes a complete probe source outside the
canonical build and requests no object output. Before and after it checks
original AG/AE/AI acceptance evidence, accepted sources and full artifacts,
Git state, the complete original AK failed-probe tree, and all 21 empty
Geometry artifact slots. A pre-existing original or corrected canonical
Geometry source may be read, but its bytes may not change during this probe.
Started owner acceptance history or partial artifacts cause a stop.

The current publication gets a new attempt path; no old run is repeated or
relabelled. `source_origin.commit` names the corrected probe publication.
The historical AJ source and failed AK result have separate explicit fields.

`stage_geometry.py <publication>` deploys this exact probe without checkout.
The only Lean command is the serialized and guarded whole-module command:

```text
lake --no-build env lean <complete corrected Geometry probe source>
```

A successful probe would still require exact canonical source installation,
normal compilation, a complete audit of owned declarations including private
and generated declarations, a final no-build check, and an original-run
readback. No such acceptance is claimed by this checkpoint.

## Verification and continuing boundary

Three new local boundary tests passed: exact notation-only source binding,
old canonical source allowed without output, and immutable original failure
identity. The earlier eight unchanged probe tests were not repeated. These
Python tests are not Lean validation.

The original registry remains **18/21 accepted, three proper-power HOLDs**,
and TrimLog remains separately accepted under its original AI run. P1.5 is
open. The source-only historical coefficient dictionary remains at its AK
publication; it is an exact identity and does not provide the complete
signed medium estimate.
