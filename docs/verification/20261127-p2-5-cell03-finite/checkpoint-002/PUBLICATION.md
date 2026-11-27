# Checkpoint 002 publication

The five deliverables named in `DELIVERY_MANIFEST.json` are preserved exactly.
The two compressed archives are split into byte-preserving 512 KiB Git blobs
listed in `ARTIFACT_PARTS.json`; they have not been recompressed. The manifest's
`FULL_EVIDENCE_LOCAL_ONLY.json.xz` entry identifies an independent local audit
input, deliberately excluded from publication because it duplicates prior
evidence. `independent-review/` preserves the completed independent inspection.

From the repository root, restore the two new archives with the previously
published helper (replace `/tmp/p25-checkpoint002` with the chosen output path):

```sh
python3 -B docs/verification/20261127-p2-5-cell03-finite/restore_artifacts.py \
  --parts-root docs/verification/20261127-p2-5-cell03-finite/checkpoint-002 \
  --output /tmp/p25-checkpoint002
```

Verify the entire 775-file evidence view from the delta and pinned Git history:

```sh
python3 -B docs/verification/20261127-p2-5-cell03-finite/checkpoint-002/restore_evidence.py \
  --repo . --delta /tmp/p25-checkpoint002/EVIDENCE_DELTA_DICT64.json.xz
```

Add `--output /tmp/p25-checkpoint002-evidence` to reconstruct those evidence
files. Different existing files are preserved by refusal. These commands do
not execute Lean, rebuild accepted dependencies, or grant new proof credit.

The new object archive contains exactly 48 objects. Seven earlier objects remain
in the original `a0eb3b8f66f47f382b0e551be1d5d7c319f8bdab` publication. A future
checkpoint must reference these 55 objects and publish only newly accepted
objects. Three decoder resource retries and five downstream joins remain;
none receives acceptance from this checkpoint.
