#!/usr/bin/env bash
set -euo pipefail
# Accepted commands. Full attempt history, including the auxiliary type exporter failure, is in commands-and-results.json.
# Existing fixed imports and stock toolchain are required.
export LEAN_SYSROOT=/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux
export LAKE_HOME=/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux
export LEAN_NUM_THREADS=1
export LEAN_PATH=/workspace/scratch/cd30ec11ea1d/goldbach-formalization/.lake/build/lib/lean:/workspace/scratch/535d89efd063/p0-round2/validation/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/goldbach/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/mathlib/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/LeanArchitect/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/plausible/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/importGraph/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/proofwidgets/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/aesop/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/Qq/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/batteries/.lake/build/lib/lean:/workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/Cli/.lake/build/lib/lean
cd /workspace/scratch/cd30ec11ea1d/goldbach-formalization

# compile: actual exit 0
/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux/bin/lake -d /workspace/scratch/cd30ec11ea1d/p5-round2/runtime/frontend-driver -f lakefile.lean script run compileOne /workspace/scratch/127408f63891/goldbach-formalization/.lake/packages/goldbach/MathlibNt/SieveTheory/LiLiuGoldbachS1Carrier.lean MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier /workspace/scratch/cd30ec11ea1d/goldbach-formalization/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuGoldbachS1Carrier.olean strict

# replay: actual exit 0
/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux/bin/leanchecker --verbose MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier

# audit: actual exit 0
/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux/bin/lake -d /workspace/scratch/cd30ec11ea1d/p5-round2/runtime/frontend-driver -f lakefile.lean script run compileOne /workspace/scratch/cd30ec11ea1d/goldbach-formalization/verification/parts/p5/S1CarrierAudit.lean verification.parts.p5.S1CarrierAudit /workspace/scratch/cd30ec11ea1d/goldbach-formalization/.lake/build/lib/lean/verification/parts/p5/S1CarrierAudit.olean strict

# types: actual exit 0
/workspace/scratch/127408f63891/lean-runtime/lean-4.33.0-rc1-linux/bin/lake -d /workspace/scratch/cd30ec11ea1d/p5-round2/runtime/frontend-driver -f lakefile.lean script run compileOne /workspace/scratch/cd30ec11ea1d/goldbach-formalization/verification/parts/p5/S1CarrierPublicTypes.lean verification.parts.p5.S1CarrierPublicTypes /workspace/scratch/cd30ec11ea1d/goldbach-formalization/.lake/build/lib/lean/verification/parts/p5/S1CarrierPublicTypes.olean strict
