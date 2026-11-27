from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path('/workspace/scratch/c397bfd2830f')
STAGE = ROOT / 'p29-package-resume'
archive = ROOT / 'P2.9-package-path-resume-20261127.zip'
files = sorted(p for p in STAGE.rglob('*') if p.is_file() and p.name != 'DELIVERY_MANIFEST.json')
assert not any(p.is_symlink() for p in files)
manifest = {'schema': 'p29_package_path_resume_delivery_manifest_v1',
            'files': {p.relative_to(STAGE).as_posix(): {'bytes': p.stat().st_size,
                      'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in files}}
manifest_path = STAGE / 'DELIVERY_MANIFEST.json'
manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as z:
    for p in [*files, manifest_path]:
        z.write(p, p.relative_to(STAGE).as_posix())
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
print(json.dumps({'path': str(archive), 'members': len(files)+1,
                  'bytes': archive.stat().st_size, 'sha256': hashlib.sha256(archive.read_bytes()).hexdigest()}))
