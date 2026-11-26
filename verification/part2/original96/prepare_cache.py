"""Reuse the six exact objects and original records from the accepted export."""
from pathlib import Path
import hashlib
import json
import shutil

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def prepare(root, library):
    root = Path(root).resolve()
    library = Path(library).resolve()
    assert root == Path('/workspace/p2-1-original96-20261126') and library.is_relative_to(root)
    pins = json.loads((root / 'verification/part2/original96/accepted-dependencies.json').read_text())
    assert pins['original_export_sha256'] == '6e9da9d095b500c85c85d70a358db135e1b19b6eea4d80f5a2de40974e85ed0f'
    original = Path('/workspace/p2-1-20261125/.lake/p2-private')
    original_records = original / 'records.json'
    all_records = json.loads(original_records.read_text())
    selected, files = {}, {}
    for module, expected in pins['modules'].items():
        rel = Path(module.replace('.', '/'))
        source = root / rel.with_suffix('.lean')
        obj = original / 'lib' / rel.with_suffix('.olean')
        record = all_records[module]
        assert sha(source) == expected['source_sha256'], module + ': source changed'
        assert sha(obj) == expected['object_sha256'], module + ': object changed'
        assert record['cache_schema'] == 2 and record['exit_code'] == 0
        for field in ['source_sha256', 'object_sha256']:
            assert record[field] == expected[field], module + ': record mismatch'
        assert record['closure_signature'] == expected['compile_closure_signature']
        for original_file in obj.parent.glob(obj.name + '*'):
            if original_file.is_file():
                expected_file = sha(original_file)
                target = library / rel.parent / original_file.name
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.exists():
                    assert sha(target) == expected_file, 'existing reused object differs'
                else:
                    shutil.copy2(original_file, target)
                assert sha(original_file) == sha(target) == expected_file
                files[str(target.relative_to(root))] = expected_file
        selected[module] = record
    return {'original_records_path': str(original_records),
            'original_records_sha256': sha(original_records), 'original_selected_records': selected,
            'copied_files': files, 'pins': pins}
