"""Untrusted raw-span planner copied from the geometry generator's pure
classes/templates. This copy has no geometry input paths or module import.
A planned AST is candidate data; only Lean original-reader equalities certify it.
"""
from __future__ import annotations
from dataclasses import dataclass, field
import hashlib
WHITE = b' \r\n\t'

def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def quote_char(c: str) -> str:
    escapes = {'\r': r'\r', '\n': r'\n', '\t': r'\t', '\\': r'\\', "'": r"\'"}
    if ord(c) < 32 and c not in escapes:
        return f'(Char.ofNat {ord(c)})'
    return "'" + escapes.get(c, c) + "'"

def quote_list(s: str) -> str:
    return '[' + ', '.join(quote_char(c) for c in s) + ']'

def chars(raw: bytes, start: int, end: int) -> str:
    return quote_list(raw[start:end].decode('ascii'))

@dataclass
class Node:
    kind: str
    start: int
    end: int
    scalar: str | bool | None = None
    children: list['Node'] = field(default_factory=list)
    fields: list['Field'] = field(default_factory=list)
    need: int = 1
    quoted_need: int | None = None

    def plan(self) -> dict:
        result = {'kind': self.kind, 'token_span': [self.start, self.end],
                  'value_fuel_sufficient_offset': self.need}
        if self.kind in {'str', 'number', 'boolean', 'null'}:
            result['candidate_scalar'] = self.scalar
        if self.quoted_need is not None:
            result['quoted_fuel_sufficient_offset'] = self.quoted_need
        if self.children:
            result['children'] = [n.plan() for n in self.children]
        if self.fields:
            result['fields'] = [f.plan() for f in self.fields]
        return result

@dataclass
class Field:
    prefix_start: int
    key: Node
    value: Node
    separator: str
    separator_pos: int
    prefix_end: int

    def plan(self) -> dict:
        return {'prefix_span': [self.prefix_start, self.prefix_end],
                'key': self.key.plan(), 'value': self.value.plan(),
                'header_span': [self.prefix_start, self.value.start],
                'separator': self.separator, 'separator_pos': self.separator_pos,
                'object_fuel_sufficient_offset': 1 + max(self.key.quoted_need, self.value.need)}

class RawPlanner:
    """Restricted SourceJson-compatible tokenizer; output is candidate data only."""

    def __init__(self, raw: bytes):
        assert raw.isascii(), 'This pilot uses exact ASCII byte = Char offsets.'
        self.raw = raw
        self.farthest_scanned = 0

    def at(self, pos: int) -> int:
        assert 0 <= pos < len(self.raw), ('unexpected end', pos)
        self.farthest_scanned = max(self.farthest_scanned, pos + 1)
        return self.raw[pos]

    def white(self, pos: int) -> int:
        while pos < len(self.raw) and self.at(pos) in WHITE:
            pos += 1
        return pos

    def quoted(self, pos: int) -> Node:
        assert self.at(pos) == ord('"'), ('expected quote', pos)
        start = pos
        pos += 1
        out = []
        escapes = {ord('"'): '"', ord('\\'): '\\', ord('/'): '/', ord('b'): '\b',
                   ord('f'): '\f', ord('n'): '\n', ord('r'): '\r', ord('t'): '\t'}
        while True:
            c = self.at(pos)
            pos += 1
            if c == ord('"'):
                text = ''.join(out)
                # quoted consumes one recursive layer per decoded character;
                # its closing quote needs one further positive fuel layer.
                return Node('str', start, pos, text, need=len(out) + 2,
                            quoted_need=len(out) + 1)
            if c == ord('\\'):
                esc = self.at(pos)
                pos += 1
                assert esc in escapes, ('SourceJson rejects this escape', pos - 1)
                out.append(escapes[esc])
            else:
                assert c >= 32, ('unescaped control character', pos - 1)
                out.append(chr(c))

    def value(self, pos: int) -> Node:
        pos = self.white(pos)
        start = pos
        first = self.at(pos)
        if first == ord('"'):
            return self.quoted(pos)
        if first == ord('['):
            items = []
            pos = self.white(pos + 1)
            if self.at(pos) == ord(']'):
                return Node('arr', start, pos + 1, children=[], need=2)
            while True:
                item = self.value(pos)
                items.append(item)
                pos = self.white(item.end)
                delim = self.at(pos)
                if delim == ord(']'):
                    need = max(i + 2 + n.need for i, n in enumerate(items))
                    return Node('arr', start, pos + 1, children=items, need=need)
                assert delim == ord(','), ('array separator', pos)
                pos = self.white(pos + 1)
                assert self.at(pos) != ord(']'), ('trailing array comma', pos)
        if first == ord('{'):
            fields = []
            pos = self.white(pos + 1)
            if self.at(pos) == ord('}'):
                return Node('obj', start, pos + 1, fields=[], need=2)
            while True:
                f = self.object_field(pos)
                fields.append(f)
                if f.separator == '}':
                    need = max(i + 2 + max(x.key.quoted_need, x.value.need)
                               for i, x in enumerate(fields))
                    return Node('obj', start, f.prefix_end, fields=fields, need=need)
                pos = f.prefix_end
        for token, kind, scalar in [(b'true', 'boolean', True),
                                     (b'false', 'boolean', False),
                                     (b'null', 'null', None)]:
            if self.raw.startswith(token, pos):
                self.farthest_scanned = max(self.farthest_scanned, pos + len(token))
                return Node(kind, start, pos + len(token), scalar, need=1)
        if first == ord('-'):
            pos += 1
        digits_start = pos
        while pos < len(self.raw) and ord('0') <= self.at(pos) <= ord('9'):
            pos += 1
        assert pos > digits_start, ('missing integer digits', digits_start)
        digits = self.raw[digits_start:pos]
        assert digits == b'0' or not digits.startswith(b'0'), ('leading zero', start)
        return Node('number', start, pos, self.raw[start:pos].decode('ascii'), need=1)

    def object_field(self, pos: int) -> Field:
        prefix_start = pos
        key = self.quoted(self.white(pos))
        colon = self.white(key.end)
        assert self.at(colon) == ord(':'), ('object colon', colon)
        value = self.value(colon + 1)
        sep = self.white(value.end)
        c = chr(self.at(sep))
        assert c in ',}', ('object separator', sep)
        return Field(prefix_start, key, value, c, sep, sep + 1)

    def first_fields(self, count: int) -> list[Field]:
        assert self.at(0) == ord('{')
        pos = 1
        result = []
        for i in range(count):
            f = self.object_field(pos)
            if i == 0:
                # The root first-field prefix also includes its opening brace.
                f.prefix_start = 0
            result.append(f)
            pos = f.prefix_end
            if i + 1 < count:
                assert f.separator == ','
        return result

def lean_node(n: Node) -> str:
    if n.kind in {'str', 'number'}:
        return f'.{n.kind} (String.ofList {quote_list(n.scalar)})'
    if n.kind == 'boolean':
        return '.boolean ' + str(n.scalar).lower()
    if n.kind == 'null':
        return '.null'
    if n.kind == 'arr':
        return '.arr [' + ', '.join(lean_node(c) for c in n.children) + ']'
    return '.obj [' + ', '.join('(String.ofList ' + quote_list(f.key.scalar) + ', ' +
                               lean_node(f.value) + ')' for f in n.fields) + ']'
