#!/usr/bin/env bash
# Continue delivery after the queued proof job. Page 0 packages once; later
# pages only read that package. A receiver must independently compare the
# manifest anchor below with the original export job's recorded SHA-256.
set -euo pipefail
p27_page="${1:-0}"
[[ "$p27_page" =~ ^[0-9]+$ ]]
p27_export=.lake/p2-private/exports/p27-complete-20261125/manifest.json
test -f "$p27_export"
p27_manifest_sha="$(python3 -B - "$p27_export" <<'PY'
from pathlib import Path
import hashlib
import sys
print(hashlib.sha256(Path(sys.argv[1]).read_bytes()).hexdigest())
PY
)"
printf 'P27_DELIVERY_MANIFEST_ANCHOR %s\n' "$p27_manifest_sha"
if [[ "$p27_page" = 0 ]]; then
  bash docs/p2/20261125/p27/prepare-delta-evidence.sh "$p27_manifest_sha"
fi
python3 -B - "$p27_page" "$p27_manifest_sha" <<'PY'
from pathlib import Path
import base64
import hashlib
import json
import math
import subprocess
import sys

page = int(sys.argv[1])
manifest_sha = sys.argv[2]
path = Path('.lake/p27-delivery/attempt-001/P27_COMPLETE.delta.tar.xz')
assert path.is_file() and not path.is_symlink()
size = path.stat().st_size
page_bytes = 1480000
pages = math.ceil(size / page_bytes)
with path.open('rb') as stream:
    archive_sha = hashlib.file_digest(stream, 'sha256').hexdigest()
if page >= pages:
    print(json.dumps({'status': 'NO_SUCH_DELIVERY_PAGE', 'page': page,
                      'pages': pages, 'bytes': size, 'sha256': archive_sha}))
    raise SystemExit(0)
with path.open('rb') as stream:
    stream.seek(page * page_bytes)
    payload = stream.read(page_bytes)
encoded = base64.b64encode(payload).decode('ascii')
assert len(encoded) <= 1980000
print('P27_DELTA_PAGE_METADATA ' + json.dumps({
    'page': page, 'pages': pages, 'offset': page * page_bytes,
    'page_bytes': len(payload), 'page_sha256': hashlib.sha256(payload).hexdigest(),
    'archive_bytes': size, 'archive_sha256': archive_sha,
    'manifest_sha256': manifest_sha,
    'manifest_anchor_boundary': 'Must match the independently observed original exporter SHA-256',
    'git_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'path': str(path), 'proof_credit': False,
}, sort_keys=True), flush=True)
print('P27_DELTA_BASE64_BEGIN', flush=True)
print(encoded, flush=True)
print('P27_DELTA_BASE64_END', flush=True)
PY
