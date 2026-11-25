import re

def mask_comments(text: str) -> str:
    """Mask nested Lean comments while preserving source offsets and newlines."""
    out = list(text)
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i + 2] = [' ', ' ']
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                out[i:i + 2] = [' ', ' ']
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i + 2] = [' ', ' ']
            depth = 1
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            j = len(text) if j < 0 else j
            out[i:j] = [' '] * (j - i)
            i = j
        else:
            i += 1
    assert depth == 0
    return ''.join(out)


def declarations(text: str) -> dict[str, dict]:
    code = mask_comments(text)
    matches = list(re.finditer(r'^(private )?(theorem|def|structure)\s+([A-Za-z0-9_.]+)', code, re.M))
    boundaries = [m.start() for m in re.finditer(r'^(?:namespace|end)(?:\s|$)', code, re.M)]
    result = {}
    for i, m in enumerate(matches):
        stop = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        stop = min([stop] + [p for p in boundaries if m.start() < p < stop])
        end = m.start() + len(code[m.start():stop].rstrip())
        assert m[3] not in result
        result[m[3]] = {'kind': m[2], 'private': bool(m[1]),
                        'text': text[m.start():end], 'line': text.count('\n', 0, m.start()) + 1}
    return result


def header(decl: dict) -> str:
    text = decl['text']
    if decl['kind'] == 'structure':
        return text
    stops = [m.start() for m in re.finditer(r':=|\bwhere\b|\n  \|', mask_comments(text))]
    assert stops
    return text[:min(stops)].rstrip()


def proof_body(text: str) -> str:
    assert ':=' in text
    return text.split(':=', 1)[1]


def with_body(original: dict, body: str) -> str:
    return original['text'].split(':=', 1)[0] + ':=' + body


def normalize(text: str) -> str:
    return re.sub(r'\s+', ' ', text).strip()
