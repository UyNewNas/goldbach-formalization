"""Pure source/hash helpers; no verification commands or import-time actions."""
import hashlib
import re

def digest(b):
    return hashlib.sha256(b).hexdigest()

def blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()

def strip_comments(s):
    out = list(s)
    i = 0
    depth = 0
    in_string = False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif s.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if s[i] != '\n': out[i] = ' '
                i += 1
        elif in_string:
            if s[i] == '\\': i += 2
            elif s[i] == '"': in_string = False; i += 1
            else: i += 1
        elif s.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            if j == -1: j = len(s)
            out[i:j] = ' ' * (j-i); i = j
        elif s[i] == '"':
            in_string = True; i += 1
        else:
            i += 1
    return ''.join(out)

def namespace_at(clean, pos):
    stack = []
    for m in re.finditer(r'^\s*(namespace|section|end)(?:\s+([^\s]+))?\s*$', clean[:pos], re.M):
        kind, name = m.group(1), m.group(2)
        if kind != 'end': stack.append((kind, name or ''))
        elif stack: stack.pop()
    return '.'.join(name for kind, name in stack if kind == 'namespace' and name)

def extract_types(s, module, sha256):
    clean = strip_comments(s)
    result = []
    pat = r'^[ \t]*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([^\s({\[:]+)'
    for m in re.finditer(pat, clean, re.M):
        i = m.end(); stack = []; end = None; in_string = False
        while i < len(clean):
            ch = clean[i]
            if in_string:
                if ch == '\\': i += 2; continue
                if ch == '"': in_string = False
            elif ch == '"': in_string = True
            elif clean.startswith(':=', i) and not stack:
                end = i; break
            elif ch in '([{⦃': stack.append(ch)
            elif ch in ')]}⦄' and stack: stack.pop()
            i += 1
        if end is None:
            raise RuntimeError(f'No source proof delimiter for {module}:{m.group(1)}')
        name = m.group(1)
        ns = namespace_at(clean, m.start())
        result.append({'module': module, 'source_sha256': sha256,
                       'source_name': name, 'namespace_context': ns,
                       'source_qualified_name': f'{ns}.{name}' if ns else name,
                       'source_line': s.count('\n', 0, m.start())+1,
                       'source_declaration_head': s[m.start():end].strip(),
                       'compiler_printed_type_available': False,
                       'classification': 'source-extracted declaration head; implicit elaboration/coercions are not compiler output'})
    return result
