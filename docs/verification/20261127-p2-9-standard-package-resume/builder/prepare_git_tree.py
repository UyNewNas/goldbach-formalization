from pathlib import Path
import hashlib
import json

ROOT = Path('/workspace/scratch/c397bfd2830f')
STAGE = ROOT / 'p29-package-resume'
REL = Path('docs/verification/20261127-p2-9-standard-package-resume')
OUT = STAGE / REL
skip = {'CACHE_PROBE_RESULT.json', 'CACHE_PROBE_STDOUT.log', 'CACHE_PROBE_TRANSPORT_RESPONSES.json',
        'PROBE_COMPLETE_OUTPUT_RESPONSE.json', 'V4_COMPLETE_OUTPUT_RESPONSE.json'}
paths = sorted(p for p in OUT.rglob('*') if p.is_file() and p.name not in skip
               and 'original-cache-records' not in p.relative_to(OUT).parts
               and '__pycache__' not in p.relative_to(OUT).parts
               and p.name != 'GIT_PACKET_MANIFEST.json')
paths += [STAGE / Path('docs/verification/20261126-p2-9-continuation/RESUME.json'),
          STAGE / Path('docs/verification/20261125-p2-9-geometric-family/CURRENT_RUN_STATUS.json')]
paths += sorted((STAGE / 'docs/verification/20261127-p2-9-omitted-observation-resume').glob('*'))
precreated = {
    'postimage.py': '0da2ac76324dad71f5ffce8ab35914c8e962e57a',
    'bootstrap.py': 'af682144e0ed979f27a8b657f8389c2f8caff026',
    'V4_TO_V5.patch': 'b4f3765ace036a4947102c2b55325dbf9dd8ed50',
    'CACHE_PROBE_RESULT.json.zlib': 'a4a935f00d7f79e4d4127612c84a8ffefcc7ed88',
}
entries = []
pins = {}
for p in paths:
    data = p.read_bytes()
    sha = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    rel = p.relative_to(STAGE).as_posix()
    pins[rel] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(), 'git_blob': sha}
    item = {'path': rel, 'mode': '100644', 'type': 'blob'}
    if p.name in precreated:
        assert sha == precreated[p.name]
        item['sha'] = sha
    else:
        item['content'] = data.decode('utf-8')
    entries.append(item)
manifest = {'schema': 'p29_standard_package_resume_git_packet_manifest_v1',
            'base_commit': 'dbea6b7c0cfc1057ee2be84c3bce1a5f30e1a243',
            'files': pins,
            'cache_transport': 'Exact zlib bytes of the original completed cache-probe JSON; full raw stdout and tool responses remain in the delivery archive.',
            'new_formal_credit': 0}
mp = OUT / 'GIT_PACKET_MANIFEST.json'
mp.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
entries.append({'path': mp.relative_to(STAGE).as_posix(), 'mode': '100644', 'type': 'blob', 'content': mp.read_text()})
print(json.dumps({'entries': entries, 'file_count': len(entries), 'base_tree': '8f673af774795ff50f981c608e286a9d5a69a557'}))
