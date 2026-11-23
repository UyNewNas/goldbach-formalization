"""Read-only Lean declaration text extraction; no elaboration or compiler."""
import hashlib
import re


def mask_comments_and_strings(text):
    chars = list(text)
    i, block_depth = 0, 0
    while i < len(text):
        if block_depth:
            if text.startswith('/-', i):
                chars[i:i+2] = [' ', ' ']
                block_depth += 1
                i += 2
            elif text.startswith('-/', i):
                chars[i:i+2] = [' ', ' ']
                block_depth -= 1
                i += 2
            else:
                if text[i] not in '\r\n':
                    chars[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            chars[i:i+2] = [' ', ' ']
            block_depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            for j in range(i, end):
                if text[j] != '\r':
                    chars[j] = ' '
            i = end
        elif text[i] == '"':
            chars[i] = ' '
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    chars[i] = ' '
                    i += 1
                    if i < len(text):
                        chars[i] = ' '
                        i += 1
                elif text[i] == '"':
                    chars[i] = ' '
                    i += 1
                    break
                else:
                    if text[i] not in '\r\n':
                        chars[i] = ' '
                    i += 1
        else:
            i += 1
    assert block_depth == 0, 'unclosed block comment'
    return ''.join(chars)


def theorem_headers(text):
    masked = mask_comments_and_strings(text)
    pattern = re.compile(r'(?m)^[ \t]*(?:@\[[^\n]*\][ \t]*)?'
                         r'(?P<private>private[ \t]+)?(?:theorem|lemma)[ \t]+'
                         r'(?P<name>[^\s({:]+)')
    out = []
    for match in pattern.finditer(masked):
        end = masked.index(':=', match.end()) + 2
        header = text[match.start():end]
        out.append({'name': match.group('name'), 'private': bool(match.group('private')),
                    'header': header, 'header_sha256': hashlib.sha256(header.encode()).hexdigest(),
                    'line': text.count('\n', 0, match.start()) + 1})
    return out
