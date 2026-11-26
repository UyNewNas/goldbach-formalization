"""Exact helper extracted from original collector773e4eab; source only."""
from pathlib import Path

def lake_descriptor_binding(output_descrs: dict, stem: Path, ir_stem: Path) -> list:
    # Lake's own sidecar hashes supplement the independent SHA256 receipt.
    # Missing sidecars are explicit; they never become fabricated hash matches.
    rows = []
    mapping = {'i': stem.with_suffix('.ilean'), 'rs': stem.with_suffix('.ir.sig'),
               'r': stem.with_suffix('.ir'), 'c': ir_stem.with_suffix('.c'),
               'b': ir_stem.with_suffix('.bc')}
    for key, path in mapping.items():
        if key in output_descrs:
            sidecar = Path(str(path) + '.hash')
            value = sidecar.read_text().strip() if sidecar.is_file() else None
            descriptor = output_descrs[key]
            rows.append({'part': key, 'path': str(path), 'descriptor': descriptor,
                         'sidecar_hash': value,
                         'matched': isinstance(descriptor, str) and value is not None
                         and descriptor.split('.', 1)[0] == value})
    for i, descriptor in enumerate(output_descrs.get('o', [])):
        if i >= 3:
            rows.append({'part': 'o', 'matched': False, 'unexpected_olean_part': i})
            continue
        path = stem.with_suffix(['.olean', '.olean.server', '.olean.private'][i])
        sidecar = Path(str(path) + '.hash')
        value = sidecar.read_text().strip() if sidecar.is_file() else None
        rows.append({'part': 'o', 'path': str(path), 'descriptor': descriptor,
                     'sidecar_hash': value,
                     'matched': isinstance(descriptor, str) and value is not None
                     and descriptor.split('.', 1)[0] == value})
    return rows

