# Frozen source-only checkpoint: direct packed geometry pilot

**Status: SOURCE ONLY. No new-cell Lean owner has been generated, compiled or accepted in this checkpoint.** Python syntax inspection is not Lean verification.

The parameterized generator accepts original cells 01–12, refuses frozen cell00, and requires exact raw bytes matching the frozen v4 input provenance. The first required input is cell01: 470901 bytes, SHA256 `e19eee9d7e282cd3a618a71f12e93bcce28319485c9d0fd31bbeaf9f81a995a4`. It was not locally available when this checkpoint was frozen.

The intended first pilot has exactly four owners, in order:

1. The unchanged production `ArchiveGeometryData01` source, in a private original-relative-path mirror.
2. Direct packed input/count/drop interfaces.
3. The first five original metadata fields as one reader transition.
4. The first grouped `active8_enumeration` block, with arbitrary fuel/tail/accumulator and an exact compact-input span binding.

Six accepted packed/parser suppliers are reused as existing objects. No cell00 geometry parser, flat CharacterCoreDiagnostic value or production packed transport is regenerated. The fixed local normal → independent kernel limits are 4 GiB process-tree RSS, 180 seconds, one thread per owner. The scripts submit no P1/P3 jobs.

The array grouping policy starts with at most two items / 768 raw bytes per chunk and four chunks / 4096 raw bytes per owner. A selected nested child above 4096 bytes is explicitly held. **The external grouped supplier extension for such a child is not implemented.** Full-array composition, full-cell parsing, typed geometry decoding and all13 success are outside this pilot's claimed scope. Host planning is never reader acceptance.

`SOURCE_ONLY_MANIFEST.json` pins the source files, upstream provenance, runner and intended scope. `SOURCE_ONLY_FILELIST.txt` is the exact checkpoint whitelist; it excludes objects, raw files, later attempts and unrelated independent reviews.

This baseline is frozen. When exact raw arrives, run the read-only baseline with output in a fresh `attempts/cell01-pilot-v1/` directory. Preserve any failure there. Any generator repair must be made in a new attempt/checkpoint copy, with its own diff and hashes, without editing this baseline or re-running accepted owners.

The initial invocation is:

```sh
python3 /workspace/p26-recovery-candidates/geometry-direct-packed/run_pilot.py --cell 1 --raw /workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-01-cell.witness.json --out /workspace/p26-recovery-candidates/geometry-direct-packed/attempts/cell01-pilot-v1
```

After the four actual owner receipts exist and all succeed, `collect_pilot.py --out <that attempt>` can freeze their measured evidence. It runs no compiler and refuses missing or mismatched acceptance. It has not been run in this source-only checkpoint.
