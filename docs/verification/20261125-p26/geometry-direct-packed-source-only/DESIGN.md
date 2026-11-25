# Direct packed geometry parser generator: bounded pilot scope

## Current deliverable and status

The generator is parameterized by cell ID, exact original raw input path, and private working directory. It accepts cells 01–12 and deliberately refuses cell00, whose parser and transport package is frozen. Python syntax has been checked. No new-cell Lean acceptance is claimed before the actual raw file is available and each emitted owner receives normal plus independent kernel.

The first requested original is cell01, 470901 bytes, SHA256 e19eee9d7e282cd3a618a71f12e93bcce28319485c9d0fd31bbeaf9f81a995a4. Its exact filename/path, v4 source hash and original observed-loader provenance are recorded in CELL01_INPUT_REQUIREMENT.json. No synthetic or regenerated witness is substituted.

## Reused components

- PackedChars, the unchanged production ArchivePackedLoader, SourceJson, CharInputBridge, SourceJsonCharInput and the data-independent ParseFromValue00 helper are copied as accepted source/object suppliers. This is a six-module closure and imports no old CharacterCore, old full parser or old geometryPacked00 transport owner.
- raw_planner.py is copied byte-for-byte from the already used pure moment planner. It only proposes spans, AST constants and sufficient fuel offsets.
- fragment_templates.py adapts the already verified arbitrary-tail value/array/object proof templates. It has explicit per-cell/raw configuration and no cell00 input path or import. The existing large-child field continuations preserve all original duplicate-key/separator/error branches.
- Exact new input bindings use (geometryPackedNN.drop start).toList and the accepted Tree.toList_drop/Tree.length_toList interfaces, avoiding large flat-list drops.

## Cell-specific data

The exact DataNN source is copied byte-for-byte from v4 after its recorded hash is checked. Its original relative path resolves inside a private project/goldbach-research mirror and is recorded in BOOTSTRAP.json. Raw bytes are read without newline normalization. This planner currently requires the checked actual file to be ASCII so byte offsets equal Char offsets; a non-ASCII file causes an explicit stop, never silent reinterpretation.

The production FQN, cell namespace, raw length/hash, field order, token spans, AST constants, node fuel offsets and per-owner source names come from that cell's actual data. All top-level fields are retained in RAW_PLAN.json even when a partial pilot proves only a prefix. No field is filtered from a claimed full parse; this pilot makes no full-parse claim.

## First measured pilot

The driver will create/check four owners in order: unchanged Data01; direct packed input/count/rest interfaces; the first five original metadata fields grouped into one arbitrary-tail root-value proof; and the first grouped active8_enumeration array transition. The metadata proof preserves the real reverse accumulator and original duplicate checks. The array proof has arbitrary tail and prior accumulator, retains exact original fuel recursion, and is bound to a real compact-input interval. The unfinished remainder stays as an original SourceJson.array call.

Small chunks contain at most two items and 768 raw bytes; at most four chunks are grouped per owner, with a 4096-byte owner span budget. This starts below the measured successful cell00 compact interval sizes. Self-delimiting nested children up to the owner's span budget use the same recursively composed templates inside that owner, avoiding one owner per trivial token or small child object. A selected nested child over 4096 bytes is explicitly held for a separately grouped supplier; it is not evaluated with an unbounded whole-node rfl or silently truncated. That external large-child hierarchy is a follow-up extension, not a claimed implemented whole-cell backend.

## Original reader invariants

Fuel is a structural bound, not remaining byte count. value(f+1) passes f to its child; array/object(f+1) use f for the current element and comma continuation. Numeric tokens are only emitted inside separator frames; arbitrary-tail standalone numeric certificates are rejected. Strings and structured children retain their full closing delimiters. Returned whitespace/tails, reverse-accumulator order, empty-array/object branches, duplicate checks and CRLF remain exactly those of SourceJson.

Every closed theorem is checked in Lean. Host tokenization, SHA matching and grouping decisions are not accepted as parsing proofs. Each owner uses the unchanged 4 GiB RSS / 180 second / one-thread local runner, with normal success required before independent kernel. Existing accepted suppliers are not rebuilt; failed source and logs must be preserved before any local repair. No P1 job or production modification is part of this generator.

## Invocation

Use generate.py with --cell 1 --raw /workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-01-cell.witness.json --out /workspace/p26-recovery-candidates/geometry-direct-packed/cell01 and --action prepare, input, metadata, or array-block. The default metadata count is 5; the default array key is active8_enumeration and block index is 0. These commands generate candidates only; the separate pilot driver invokes the fixed normal/kernel checks.
