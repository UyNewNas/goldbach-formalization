#!/usr/bin/env bash
set -euo pipefail
control_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
python3 -B "${control_dir}/stage_join_only.py" \
  --archive "${control_dir}/cell05-join-only-v1.tar.xz" \
  --manifest "${control_dir}/MANIFEST.json" --install
python3 -B \
  /workspace/p26-cell05-connections14-stage-557a12f3bcd7/tools/p26/cell05-connections14-run-20261126/fields_only_join.py \
  --provider /workspace/p26-cell05-connections14-provider-557a12f3bcd7
