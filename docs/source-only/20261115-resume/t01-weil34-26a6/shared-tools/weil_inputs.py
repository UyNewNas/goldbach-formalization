"""Strict header-only source closure for the fixed Lean module syntax.

No declaration, tactic, helper or Lean binary is evaluated by this module.
The runtime caller uses the current exact pinned source and artifact files.
"""
import re

from coherent_cache import require

IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def header(text):
    offset = 0
    def token():
        nonlocal offset
        while offset < len(text):
            if text[offset].isspace() or text[offset] == '\ufeff': offset += 1; continue
            if text.startswith('--', offset):
                end = text.find('\n', offset); offset = len(text) if end < 0 else end+1
                continue
            if text.startswith('/-', offset):
                depth = 1; offset += 2
                while depth:
                    require(offset < len(text), 'Unclosed header comment')
                    if text.startswith('/-', offset): depth += 1; offset += 2
                    elif text.startswith('-/', offset): depth -= 1; offset += 2
                    else: offset += 1
                continue
            match = IDENT.match(text, offset)
            if match:
                offset = match.end(); return match.group()
            # The first body punctuation is a boundary, not a reason to scan
            # strings/comments inside a declaration as if they were imports.
            value = text[offset]; offset += 1; return value
        return None
    current = token(); modern = current == 'module'
    if modern: current = token()
    prelude = current == 'prelude'
    if prelude: current = token()
    imports = []
    while current in {'public', 'private', 'meta', 'import'}:
        exported, meta = not modern, False
        if current in {'public', 'private'}:
            exported = current == 'public'; current = token()
        if current == 'meta': meta = True; current = token()
        if current != 'import':
            # `public section`, `private def`, etc. starts the source body.
            require(current not in {'public', 'private', 'meta'}, 'Unknown module-header modifier sequence')
            break
        name = token(); all_private = name == 'all'
        if all_private: name = token()
        require(isinstance(name, str) and IDENT.fullmatch(name) is not None,
                'Unsupported/unknown module import identifier; HOLD')
        imports.append(dict(module=name, import_all=all_private, is_meta=meta, is_exported=exported))
        current = token()
    require(current not in {'module', 'prelude'}, 'Misplaced or unsupported module-header form; HOLD')
    names = [r['module'] for r in imports]
    return dict(is_module=modern, prelude=prelude, explicit_imports=imports,
                imports=names if prelude else ['Init', *names])


def source_closure(session, seeds):
    records, pending = {}, list(seeds)
    while pending:
        name = pending.pop()
        if name in records: continue
        identity = session.locate(name)
        from pathlib import Path
        parsed = header(Path(identity['source']['path']).read_text(encoding='utf-8'))
        require(identity['modern'] == parsed['is_module'], 'Source header mode differs from physical identity')
        records[name] = dict(identity=identity, header=parsed)
        pending.extend(parsed['imports'])
    require(all(imp in records for row in records.values() for imp in row['header']['imports']),
            'Header source graph is not recursively closed')
    return records
