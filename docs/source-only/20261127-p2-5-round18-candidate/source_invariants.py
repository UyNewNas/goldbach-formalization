"""Reject changes outside proof bodies in the fixed Cell0 chronology source."""
from dataclasses import dataclass
import hashlib
import re


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int
    line: int
    column: int


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def tokens(source):
    """Tokenize comments and strings explicitly; comments never become commands."""
    result = []
    i, line, column = 0, 1, 0

    def advance(end):
        nonlocal i, line, column
        part = source[i:end]
        count = part.count('\n')
        if count:
            line += count
            column = len(part.rsplit('\n', 1)[1])
        else:
            column += len(part)
        i = end

    while i < len(source):
        if source[i].isspace():
            advance(i + 1)
            continue
        if source.startswith('--', i):
            end = source.find('\n', i)
            advance(len(source) if end < 0 else end)
            continue
        if source.startswith('/-', i):
            depth, end = 1, i + 2
            while end < len(source) and depth:
                if source.startswith('/-', end):
                    depth += 1
                    end += 2
                elif source.startswith('-/', end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            require(depth == 0, 'Unterminated Lean block comment')
            advance(end)
            continue
        start, token_line, token_column = i, line, column
        if source[i] == '"':
            end = i + 1
            while end < len(source):
                if source[end] == '\\':
                    end += 2
                elif source[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
            require(end <= len(source) and source[end - 1] == '"', 'Unterminated Lean string')
        elif source.startswith(':=', i):
            end = i + 2
        else:
            match = re.match(r"[\w']+", source[i:], re.UNICODE)
            end = i + (len(match.group(0)) if match else 1)
        result.append(Token(source[start:end], start, end, token_line, token_column))
        advance(end)
    return result


COMMANDS = {'import', 'namespace', 'section', 'noncomputable', 'open', 'end',
            'variable', 'variables', 'private', 'protected', 'theorem', 'lemma',
            'def', 'abbrev', 'set_option', 'attribute', 'instance', 'local',
            'scoped', 'notation', 'macro', 'elab', 'syntax', 'opaque', 'axiom'}
DECLARATIONS = {'theorem', 'lemma', 'def', 'abbrev'}
FORBIDDEN = {'axiom', 'sorry', 'admit', 'native_decide', 'unsafe', 'partial'}


def structure(raw):
    source = raw.decode('utf-8').replace('\r\n', '\n')
    stream = tokens(source)
    require(not ({t.text for t in stream} & FORBIDDEN), 'Forbidden Lean construct')
    starts = [i for i, t in enumerate(stream) if t.column == 0 and t.text in COMMANDS]
    require(starts and starts[0] == 0, 'Unexpected preamble before the first command')
    starts.append(len(stream))
    inventory, skeleton, proofs, imports = [], [], [], []
    all_declarations = sum(t.text in DECLARATIONS for t in stream)
    for begin, end in zip(starts, starts[1:]):
        block = stream[begin:end]
        values = [t.text for t in block]
        offset = 1 if values[0] in {'private', 'protected'} else 0
        kind = values[offset]
        if kind == 'import':
            imports.append(tuple(values))
        if kind not in DECLARATIONS:
            skeleton.extend(values)
            continue
        require(len(values) > offset + 1, 'Missing declaration name')
        name = values[offset + 1]
        inventory.append((kind, name))
        if kind not in {'theorem', 'lemma'}:
            skeleton.extend(values)
            continue
        depth = 0
        split = None
        for j, token in enumerate(values):
            if token in {'(', '[', '{', '⟨'}:
                depth += 1
            elif token in {')', ']', '}', '⟩'}:
                depth -= 1
            elif token == ':=' and depth == 0:
                split = j
                break
        require(split is not None, 'Theorem lacks an explicit proof: ' + name)
        skeleton.extend(values[:split + 1])
        skeleton.append('<THEOREM_PROOF>')
        proofs.append((name, tuple(values[:split + 1])))
    require(all_declarations == len(inventory), 'Nested or nonstandard declaration was introduced')
    # The fixed source has no options. Reject scoped options inside proof bodies too.
    options = [t.text for t in stream if t.text == 'set_option']
    return {'inventory': inventory, 'skeleton': skeleton, 'proofs': proofs,
            'imports': imports, 'options': options}


def validate_proof_only(before, after, require_changed=True):
    left, right = structure(before), structure(after)
    require(not require_changed or before != after, 'Candidate equals its preimage')
    require(left['inventory'] == right['inventory'], 'Declaration inventory changed')
    require(left['proofs'] == right['proofs'], 'Theorem headers or hypotheses changed')
    require(left['imports'] == right['imports'], 'Imports changed')
    require(left['options'] == right['options'] == [], 'Options changed')
    require(left['skeleton'] == right['skeleton'], 'Definition or nonproof command changed')
    return {'source_sha256': hashlib.sha256(before).hexdigest(),
            'candidate_sha256': hashlib.sha256(after).hexdigest(),
            'declaration_count': len(left['inventory']),
            'theorem_count': len(left['proofs']),
            'theorem_headers_unchanged': True, 'definition_tokens_unchanged': True,
            'imports_unchanged': True, 'options_unchanged': True,
            'nonproof_tokens_unchanged': True, 'new_public_hypotheses': 0}
