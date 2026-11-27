#!/bin/sh
set -eu
cd /workspace/scratch/6faf06385519
python -I -B shape_executor_review/readback/readback.py \
  --recovery materials/recovery-20261127/capture-attempt-v2/RECOVERY_EXPORT.tar.xz \
  --recovery-size 4245880 \
  --recovery-sha 8a0b3afab2c32114fc124a69071160f05a1c3dc8ef84d4a19b3ae4866a66b8c6 \
  --certificate-sha 3ce215e5339bf2363d6004c8427a3c8c5e8197d82ca6b933bf4e49d9aef1f089 \
  --workflow-sha e3f9588b43b5d3bb08a24f6938c1e6dde2e9968a719f06f28bbcd8166e822d3e \
  --capture-external-observation materials/recovery-20261127/capture-attempt-v2/EXTERNAL_OBSERVATION.json
