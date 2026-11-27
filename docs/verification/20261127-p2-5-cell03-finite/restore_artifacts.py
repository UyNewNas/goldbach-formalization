"""Reconstruct published, hash-pinned evidence/cache archives without Lean work."""
from pathlib import Path
import argparse
import hashlib
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parts-root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--only', nargs='+')
    args = parser.parse_args()
    root = args.parts_root.resolve(strict=True)
    document = json.loads((root / 'ARTIFACT_PARTS.json').read_bytes())
    selected = args.only or list(document['artifacts'])
    if not set(selected) <= set(document['artifacts']):
        raise ValueError('Unknown artifact selection')
    args.output.mkdir(parents=True, exist_ok=True)
    for name in selected:
        row = document['artifacts'][name]
        if Path(name).name != name:
            raise ValueError('Artifact output must be a basename')
        pieces = []
        offset = 0
        for part in row['parts']:
            path = (root / part['path']).resolve(strict=True)
            if not path.is_relative_to(root) or part['offset'] != offset:
                raise ValueError('Part path/order differs')
            raw = path.read_bytes()
            if len(raw) != part['bytes'] or hashlib.sha256(raw).hexdigest() != part['sha256']:
                raise ValueError('Part bytes differ: ' + part['path'])
            pieces.append(raw)
            offset += len(raw)
        raw = b''.join(pieces)
        if len(raw) != row['bytes'] or hashlib.sha256(raw).hexdigest() != row['sha256']:
            raise ValueError('Assembled artifact bytes differ: ' + name)
        target = args.output / name
        if target.exists():
            if target.read_bytes() != raw:
                raise ValueError('Preserve different existing artifact: ' + str(target))
        else:
            target.write_bytes(raw)
        print(name, len(raw), row['sha256'])


if __name__ == '__main__':
    main()
