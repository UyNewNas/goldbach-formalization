set -euo pipefail
cd /workspace/p2-7-20261125
python3 -B - <<'PY'
from pathlib import Path
import base64,hashlib,json,zlib
raw=zlib.decompress(base64.b64decode('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',validate=True))
assert len(raw)==8111 and hashlib.sha256(raw).hexdigest()=='1bbb7611d4d463585894f4849e0b09dee3df4914606307b6162fd82864fcbd82'
destination=Path('/tmp/p27-reviewed-20261126/recompress_delta_stream.py')
assert not destination.is_symlink()
destination.parent.mkdir(parents=True,exist_ok=True)
if destination.exists():
    assert destination.is_file() and destination.read_bytes()==raw
else:
    with destination.open('xb') as stream:
        stream.write(raw)
assert destination.read_bytes()==raw
print('P27_REENCODER_SOURCE_VERIFIED',json.dumps({'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'proof_credit':False}),flush=True)
PY
python3 -B /tmp/p27-reviewed-20261126/recompress_delta_stream.py .lake/p27-delivery/attempt-001/P27_COMPLETE.delta.tar.xz .lake/p27-delivery/attempt-001/P27_COMPLETE.compact.delta.tar.xz --input-sha256 684f34c3019c533b40fa45b960f478ba4ec2eadebfd843efbcc5a745ddf527f5
python3 -B - <<'PY'
from pathlib import Path
import base64,hashlib,json,math,subprocess
path=Path('.lake/p27-delivery/attempt-001/P27_COMPLETE.compact.delta.tar.xz')
assert path.is_file() and not path.is_symlink()
size=path.stat().st_size
assert size<12157720,'Keep original delivery if reencoding has no size benefit'
with path.open('rb') as stream:
    digest=hashlib.file_digest(stream,'sha256').hexdigest()
page_bytes=1480000
with path.open('rb') as stream:
    payload=stream.read(page_bytes)
meta={'page':0,'pages':math.ceil(size/page_bytes),'offset':0,'page_bytes':len(payload),
      'page_sha256':hashlib.sha256(payload).hexdigest(),'archive_bytes':size,
      'archive_sha256':digest,'manifest_sha256':'73179a250532882aa5a945ba149fb734ee776dd3fdcef5d386af69b6303eca08',
      'manifest_anchor_boundary':'Independently observed original exporter SHA-256',
      'git_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
      'path':str(path),'proof_credit':False,
      'transport_encoding':'lossless_xz_reencoding_same_complete_tar_stream',
      'original_delta_sha256':'684f34c3019c533b40fa45b960f478ba4ec2eadebfd843efbcc5a745ddf527f5'}
encoded=base64.b64encode(payload).decode('ascii')
assert len(encoded)<=1980000
print('P27_DELTA_PAGE_METADATA '+json.dumps(meta,sort_keys=True),flush=True)
print('P27_DELTA_BASE64_BEGIN',flush=True)
print(encoded,flush=True)
print('P27_DELTA_BASE64_END',flush=True)
PY
