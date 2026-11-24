# Preserve the three existing Batch8 cloud dependencies

This package contains exact existing source bytes. It authors no Lean proof and requests no cloud source replacement or compilation.

The independent cloud export from job `job_5712d2c9bd9647d9ae9ef9c408e46128`, its encoded source records, the Batch8 `PROJECT_SOURCE_CONTEXT.json`, and the public Git blobs at commit `a5a42f8f70418a7b2b8a378713911e829786ec8b` all agree byte-for-byte. These files are already present in the P1 cloud project. They differ from the local P1 canonical copies because those copies still contain older proof bodies.

| Module | Existing cloud SHA256 | Existing public Git blob |
| --- | --- | --- |
| `P2PositiveAffineSimplexLogJensen` | `2c4cac96d6b340d91478be773a80ccead2004a49e217026a5914ebd879e5101f` | `e6f14d4c857bef8550499fa1637904a6940ec416` |
| `P2DegreeSixLogGapSoundness` | `50efb68de1d444a77b8374e4c7245bba0b28977de006879f3a466aed1f4ef39c` | `d8501525f7fcc6449dbfcc1856e7e4d392cfc4ee` |
| `P2OriginalLogMomentQ96Checker` | `49dddfb3fd522baed9938278d1711030ce204e0954c83758590b173e4197925c` | `c6544018c3d6e78320c8a6d7590ad84a4699c59c` |

## Contract comparison

All 39 public theorem headers and all 22 definition bodies are unchanged. Namespace, owner, section variables, scopes, project imports and declaration names are unchanged. The exact differences are six existing proof bodies and one Mathlib import:

- Jensen: the existing explicit exponential Jensen arguments, integral-expression normalization, and compact-set integrability API fixes; it also imports `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`.
- DegreeSix: the existing derivative-function elaboration and rational derivative identity fixes.
- Q96Checker: `fixedNumerator_eq_floor` uses the existing restricted simplification `simpa only [Int.floor_intCast, Int.cast_natCast]`.

`DECLARATION_COMPARISON.json` gives every declaration header and definition comparison. `CANONICAL_ALIGNMENT.patch` describes the exact local canonical alignment; it is not an instruction to rewrite already-matching cloud files.

## Existing verification evidence

The published `20261123-local-pilot/VERIFICATION_RESULTS.json` records Jensen normal compilation, original-environment kernel replay and 10 theorem type/axiom audits. The published `20261123-yellow-leaf-continuation/VERIFICATION_RESULTS.json` records the corresponding results for DegreeSix (14 theorems) and Q96Checker (15 theorems). Their source SHA256 values match these exact files. `REUSED_ACCEPTANCE_RECORDS.json` preserves the relevant module records and summaries with their immutable published record paths and hashes.

Those historical receipts are evidence for existing work, not a new P1 full-owned audit. Current P1 source-plus-five-artifact fingerprints are recorded separately in `CLOUD_ARTIFACT_BINDINGS.json`, bound to the independent cloud export. No historical object was renamed or copied into the P1 environment.

## Higher package correction

The sibling `higher-full-after-batch8` package now uses these three actual cloud SHA256 values, while its other five dependency values remain unchanged. Its gate additionally requires the complete Batch8 source-context record SHA256 `abb849aec311b84e039b6c3ecfdde710f72517f6ab41064420e96149432d2fa2` before reading the dependency entries. Its existing live dependency check still requires the exact eight-module closure. The full Higher candidate, source preimage, successful probe bindings, runtime limits, serializer and worker API are unchanged.

Parent-controlled publication may align the three local canonical files to these existing public/cloud bytes. Subsequent cloud work must preserve these files; this package adds no compilation task.
