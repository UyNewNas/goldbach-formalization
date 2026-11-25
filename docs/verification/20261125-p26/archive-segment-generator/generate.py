#!/usr/bin/env python3
"""Produce untrusted raw-span plans and original-SourceJson Lean certificates.

Only the first four fields of the one pinned fixture are scanned.  Host token
recognition plans proof obligations; it never certifies a parse.  Generated Lean
equalities must separately pass normal elaboration and the independent kernel.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
ACCEPTED = Path('/workspace/p26-recovery-candidates/archive-character-core')
READER_ROOT = Path('/workspace/p26-recovery-candidates/archive-char-input/local')
FIXTURE = Path('/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json')
FIXTURE_SHA = '87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691'
READER_SHA = 'ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424'
NS = 'ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic'
MODULE = 'ImbalancedChen.P2OriginalSaving19PositiveBalanceSegments00'
WHITE = b' \r\n\t'


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def fingerprint(p: Path) -> dict:
    b = p.read_bytes()
    return {'path': str(p), 'bytes': len(b), 'sha256': sha(b)}


def require_hash(p: Path, expected: str) -> dict:
    row = fingerprint(p)
    assert row['sha256'] == expected, (str(p), row, expected)
    return row


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


@dataclass(frozen=True)
class ValueCertificateRef:
    """An opaque supplier of an original value-reader equality.

    Expected type, checked by Lean at use:
      forall fuel tail, SourceJson.value (fuel + fuel_offset)
        (chars_name ++ tail) = .ok (value_name, tail)

    This append-tail interface is only admissible for self-delimiting tokens.
    Integer certificates require a separate explicit non-digit delimiter frame.
    """
    module: str
    theorem: str
    chars_name: str
    value_name: str
    fuel_offset: int
    span: tuple[int, int]
    source_path: str | None = None
    source_sha256: str | None = None
    self_delimiting: bool = True

    def validate(self, node: Node) -> None:
        assert self.span == (node.start, node.end)
        assert self.self_delimiting and node.kind != 'number'
        assert self.fuel_offset >= node.need
        for s in [self.module, self.theorem, self.chars_name, self.value_name]:
            assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', s), s
        if self.source_path is not None:
            assert self.source_sha256 is not None
            require_hash(Path(self.source_path), self.source_sha256)


def marker(stage: str) -> str:
    return ('run_cmd do\n  let err ← IO.getStderr\n'
            f'  err.putStrLn "P26_POSITIVE_BALANCE {stage}"\n  err.flush\n\n')


def reproduce_dimension(raw: bytes, first: Field) -> tuple[bytes, dict]:
    root_fuel = len(raw) + 1
    base = 2 + max(first.key.quoted_need, first.value.need)
    continuation = base - 2
    replacements = {
        '@PREFIX_CHARS@': chars(raw, 0, first.prefix_end),
        '@KEY_CHARS@': quote_list(first.key.scalar),
        '@NUMBER_CHARS@': quote_list(first.value.scalar),
        '@PREFIX_LENGTH@': str(first.prefix_end),
        '@VALUE_BASE@': str(base), '@OBJECT_BASE@': str(continuation),
        '@ROOT_FUEL@': str(root_fuel), '@POST_FUEL@': str(root_fuel - 2),
        '@EXCESS_FUEL@': str(root_fuel - base),
    }
    text = (ROOT / 'templates/DimensionPrefix00.lean.tmpl').read_bytes().decode('utf-8')
    for old, new in replacements.items():
        text = text.replace(old, new)
    assert not re.search(r'@[A-Z_]+@', text)
    original = ACCEPTED / 'ImbalancedChen/P2OriginalSaving19DimensionPrefix00.lean'
    require_hash(original, 'd64263d9c3e35fe05bd998cdaf5f523ea7ae2db933bcd41ca31f9033f5b162aa')
    assert text.encode() == original.read_bytes(), 'Dimension reproduction drift.'
    return text.encode(), {
        'accepted_source': fingerprint(original),
        'reproduced_byte_identical': True, 'recompiled': False,
        'prefix_span': [0, first.prefix_end],
        'key_content_span': [first.key.start + 1, first.key.end - 1],
        'number_span': [first.value.start, first.value.end],
        'generic_offsets': [base, continuation],
        'actual_fuels': [root_fuel, root_fuel - 2],
        'root_excess_fuel': root_fuel - base,
        'origin': 'Accepted proof template; all quoted data, spans and fuel offsets are planned from pinned bytes.'}


def array_chunks(raw: bytes, node: Node, count: int) -> list[dict]:
    assert node.kind == 'arr' and node.children and count >= 1
    chunks = []
    start = node.start + 1
    for first in range(0, len(node.children), count):
        after = min(first + count, len(node.children))
        final = after == len(node.children)
        if final:
            end = node.end
        else:
            end = node.children[after - 1].end
            while raw[end] in WHITE:
                end += 1
            assert raw[end] == ord(',')
            end += 1
        before_offset = node.need - 1 - first
        after_offset = before_offset - (after - first)
        assert before_offset > 0 and after_offset >= 0
        for j in range(first, after):
            assert before_offset - (j - first) - 1 >= node.children[j].need
        chunks.append({'index': len(chunks), 'span': [start, end],
                       'item_interval': [first, after], 'final': final,
                       'before_offset': before_offset,
                       'after_offset': None if final else after_offset,
                       'last_char': chr(raw[end - 1]),
                       'prefix_sha256': sha(raw[start:end])})
        start = end
    assert start == node.end
    return chunks


def emit_fourth(raw: bytes, f: Field, chunks: list[dict],
                external: ValueCertificateRef | None = None) -> tuple[bytes, dict]:
    n = f.value
    value_base = n.need if external is None else external.fuel_offset
    base = 1 + max(f.key.quoted_need, value_base)
    child_base = base - 1
    actual_before = len(raw) + 1 - 4
    actual_after = actual_before - 1
    excess = actual_before - base
    start, end = f.prefix_start, f.prefix_end
    assert f.separator == ',' and raw[n.end:end] == b','
    assert f.key.scalar == 'positive_normal_balance' and n.kind == 'arr'
    if external:
        external.validate(n)
    ref = external or ValueCertificateRef(MODULE, 'value_positive_balance_array',
        'positiveBalanceArrayChars00', 'positiveBalanceValue00', value_base,
        (n.start, n.end))
    p = ['import ImbalancedChen.P2OriginalSaving19FirstThreeFields00\n']
    if external:
        p.append('import ' + external.module + '\n')
    p.append('''
/-!
Generated fourth-field pilot on exact raw CRLF bytes. The 11-item array is
proved by small original-reader transitions, and its theorem is composed into
the original object continuation. Accumulators stay in the reader's reverse
order. The full unconsumed suffix is always an arbitrary tail or a drop of the
accepted geometryChars00; it is never copied into the generated proof.
Host token/AST/fuel planning is untrusted. The theorems below are its checks.
-/
namespace ''' + NS + '''

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

''')
    p.append(f'def positiveBalanceHeaderChars00 : List Char := {chars(raw, start, n.start)}\n')
    for c in chunks:
        p.append(f'def positiveBalanceChunk{c["index"]}Chars00 : List Char := '
                 f'{chars(raw, *c["span"])}\n')
    chunk_names = [f'positiveBalanceChunk{c["index"]}Chars00' for c in chunks]
    chain = ' ++ '.join(chunk_names)
    p.append(f"def positiveBalanceArrayChars00 : List Char := '[' :: ({chain})\n")
    p.append(f'def positiveBalancePrefixChars00 : List Char := {chars(raw, start, end)}\n')
    p.append(f'def positiveBalanceKey00 : String := String.ofList {quote_list(f.key.scalar)}\n')
    p.append('def positiveBalanceItems00 : List SourceJson := [\n    ' +
             ',\n    '.join(lean_node(c) for c in n.children) + '\n  ]\n')
    p.append('def positiveBalanceValue00 : SourceJson := .arr positiveBalanceItems00\n')
    p.append('def positiveBalanceAcc00 : List (String × SourceJson) :=\n'
             '  (positiveBalanceKey00, positiveBalanceValue00) :: facetIndicesAcc00\n\n')
    for c in chunks:
        previous = list(reversed(n.children[:c['item_interval'][0]]))
        p.append(f'def positiveBalanceArrayAcc{c["index"]}00 : List SourceJson := [' +
                 ', '.join(lean_node(x) for x in previous) + ']\n')
    p.append('\n' + marker('before_raw_bindings'))
    p.append(f'''theorem geometryChars00_positive_balance_prefix :
    (geometryChars00.drop {start}).take {end-start} = positiveBalancePrefixChars00 := by
  rfl

theorem positive_balance_prefix_decomposition :
    positiveBalancePrefixChars00 =
      positiveBalanceHeaderChars00 ++ positiveBalanceArrayChars00 ++ [','] := by
  rfl

theorem geometryChars00_positive_balance_split :
    geometryChars00.drop {start} = positiveBalancePrefixChars00 ++ geometryChars00.drop {end} := by
  calc
    geometryChars00.drop {start} =
        (geometryChars00.drop {start}).take {end-start} ++ (geometryChars00.drop {start}).drop {end-start} :=
      (List.take_append_drop {end-start} (geometryChars00.drop {start})).symm
    _ = positiveBalancePrefixChars00 ++ (geometryChars00.drop {start}).drop {end-start} :=
      congrArg (fun p => p ++ (geometryChars00.drop {start}).drop {end-start})
        geometryChars00_positive_balance_prefix
    _ = positiveBalancePrefixChars00 ++ geometryChars00.drop {end} := by
      rw [List.drop_drop]

''')
    p.append(marker('after_raw_bindings'))
    if external is None:
        for c in chunks:
            idx = c['index']
            before = c['before_offset']
            if c['final']:
                rhs = '.ok (positiveBalanceValue00, tail)'
            else:
                rhs = (f'SourceJson.array (fuel + {c["after_offset"]}) (SourceJson.white tail)\n'
                       f'        positiveBalanceArrayAcc{idx+1}00')
            p.append(f'''/-- Original array reader; item interval {c['item_interval']} and raw span {c['span']}.
The fixed prefix ends in {repr(c['last_char'])}; the arbitrary tail is not inspected. -/
theorem array_positive_balance_chunk_{idx} (fuel : Nat) (tail : List Char) :
    SourceJson.array (fuel + {before})
      (SourceJson.white (positiveBalanceChunk{idx}Chars00 ++ tail)) positiveBalanceArrayAcc{idx}00 =
      {rhs} := by
  rfl

''')
            p.append(marker(f'after_array_chunk_{idx}'))
        def remaining(i: int) -> str:
            result = 'tail'
            for name in reversed(chunk_names[i:]):
                result = f'{name} ++ ({result})'
            return result
        payload = remaining(0)
        p.append(f'''/-- Composition of the opaque original-array transition theorems. -/
theorem value_positive_balance_array (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + {value_base}) (positiveBalanceArrayChars00 ++ tail) =
      .ok (positiveBalanceValue00, tail) := by
  have hinput : positiveBalanceArrayChars00 ++ tail = '[' :: ({payload}) := by
    simp only [positiveBalanceArrayChars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + {value_base}) (positiveBalanceArrayChars00 ++ tail) =
        SourceJson.value (fuel + {value_base}) ('[' :: ({payload})) :=
      congrArg (SourceJson.value (fuel + {value_base})) hinput
    _ = SourceJson.array (fuel + {value_base-1}) (SourceJson.white ({payload}))
        positiveBalanceArrayAcc000 := by rfl
''')
        for c in chunks:
            idx = c['index']
            rest = remaining(idx+1)
            if c['final']:
                p.append(f'    _ = .ok (positiveBalanceValue00, tail) :=\n'
                         f'      array_positive_balance_chunk_{idx} fuel tail\n\n')
            else:
                p.append(f'    _ = SourceJson.array (fuel + {c["after_offset"]})\n'
                         f'        (SourceJson.white ({rest})) positiveBalanceArrayAcc{idx+1}00 :=\n'
                         f'      array_positive_balance_chunk_{idx} fuel ({rest})\n')
    else:
        p.append(f'''/-- External child-owner interface: original bytes and result data are
definitionally checked again, and its original-reader theorem is used opaquely. -/
theorem value_positive_balance_array (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + {value_base}) (positiveBalanceArrayChars00 ++ tail) =
      .ok (positiveBalanceValue00, tail) := by
  have hchars : positiveBalanceArrayChars00 = {ref.chars_name} := by rfl
  calc
    SourceJson.value (fuel + {value_base}) (positiveBalanceArrayChars00 ++ tail) =
        SourceJson.value (fuel + {value_base}) ({ref.chars_name} ++ tail) :=
      congrArg (fun cs => SourceJson.value (fuel + {value_base}) (cs ++ tail)) hchars
    _ = .ok ({ref.value_name}, tail) := {ref.theorem} fuel tail
    _ = .ok (positiveBalanceValue00, tail) := by rfl

''')
    p.append(marker('after_array_composition'))
    p.append(f'''/-- The original post-value continuation. The header theorem below
reduces the original duplicate-key test against all three accepted prior keys. -/
def positiveBalanceAfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}}' :: ending =>
      .ok (.obj (((positiveBalanceKey00, result.1) :: facetIndicesAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((positiveBalanceKey00, result.1) :: facetIndicesAcc00)
  | _ => .error "object separator missing"

theorem object_positive_balance_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + {base}) (SourceJson.white (positiveBalanceHeaderChars00 ++ rest))
      facetIndicesAcc00 =
      (SourceJson.value (fuel + {child_base}) rest).bind
        (positiveBalanceAfterValue00 (fuel + {child_base})) := by
  rfl

theorem object_positive_balance_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + {base}) (SourceJson.white (positiveBalancePrefixChars00 ++ tail))
      facetIndicesAcc00 =
      SourceJson.object (fuel + {child_base}) (SourceJson.white tail) positiveBalanceAcc00 := by
  have hinput : positiveBalancePrefixChars00 ++ tail =
      positiveBalanceHeaderChars00 ++ (positiveBalanceArrayChars00 ++ (',' :: tail)) := by
    rw [positive_balance_prefix_decomposition]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  calc
    SourceJson.object (fuel + {base}) (SourceJson.white (positiveBalancePrefixChars00 ++ tail))
        facetIndicesAcc00 =
      SourceJson.object (fuel + {base})
        (SourceJson.white (positiveBalanceHeaderChars00 ++ (positiveBalanceArrayChars00 ++ (',' :: tail))))
        facetIndicesAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + {base}) (SourceJson.white s) facetIndicesAcc00)
        hinput
    _ = (SourceJson.value (fuel + {child_base}) (positiveBalanceArrayChars00 ++ (',' :: tail))).bind
        (positiveBalanceAfterValue00 (fuel + {child_base})) :=
      object_positive_balance_header fuel (positiveBalanceArrayChars00 ++ (',' :: tail))
    _ = (Except.ok (positiveBalanceValue00, ',' :: tail)).bind
        (positiveBalanceAfterValue00 (fuel + {child_base})) :=
      congrArg (fun r => r.bind (positiveBalanceAfterValue00 (fuel + {child_base})))
        (value_positive_balance_array (fuel + {child_base-value_base}) (',' :: tail))
    _ = SourceJson.object (fuel + {child_base}) (SourceJson.white tail) positiveBalanceAcc00 := by
      rfl

''')
    p.append(marker('after_object_composition'))
    p.append(f'''theorem geometryChars00_positive_balance_step :
    SourceJson.object {actual_before} (SourceJson.white (geometryChars00.drop {start})) facetIndicesAcc00 =
      SourceJson.object {actual_after} (SourceJson.white (geometryChars00.drop {end})) positiveBalanceAcc00 := by
  exact (congrArg (fun s => SourceJson.object {actual_before} (SourceJson.white s) facetIndicesAcc00)
      geometryChars00_positive_balance_split).trans
    (object_positive_balance_prefix {excess} (geometryChars00.drop {end}))

/-- Exact four-field transition on the complete original character input.
The remaining object parse is retained, not assumed or claimed successful. -/
theorem geometryChars00_through_positive_balance :
    SourceJson.value {len(raw)+1} geometryChars00 =
      SourceJson.object {actual_after} (SourceJson.white (geometryChars00.drop {end})) positiveBalanceAcc00 := by
  exact geometryChars00_through_facet_indices.trans geometryChars00_positive_balance_step

''')
    p.append(marker('after_closed_original_reader_step'))
    names = ['geometryChars00_positive_balance_prefix', 'positive_balance_prefix_decomposition',
             'geometryChars00_positive_balance_split']
    if external is None:
        names += [f'array_positive_balance_chunk_{c["index"]}' for c in chunks]
    names += ['value_positive_balance_array', 'object_positive_balance_header',
              'object_positive_balance_prefix', 'geometryChars00_positive_balance_step',
              'geometryChars00_through_positive_balance']
    p += ['#print axioms ' + name + '\n' for name in names]
    p.append('\nend ' + NS + '\n')
    return ''.join(p).encode(), {
        'field': f.plan(), 'chunks': chunks, 'array_value_offset': value_base,
        'object_offsets': [base, child_base], 'actual_object_fuels': [actual_before, actual_after],
        'object_excess_fuel': excess, 'final_object_accumulator': 'positiveBalanceAcc00',
        'child_certificate': ref.__dict__, 'declaration_names_checked_for_axioms': names,
        'source_output_contains_copied_full_suffix': False}


def dependencies() -> list[dict]:
    rows = []
    sources = [
        ('P2OriginalSaving19SourceJson', READER_ROOT/'reader-source/ImbalancedChen',
         READER_ROOT/'lib/lean/ImbalancedChen', READER_SHA,
         'ec7361a2e508c323bf2dfa5f384d31a4bd71ffd47e032bfbf428c13bc1c2e467'),
        ('P2OriginalSaving19CharacterCore00', ACCEPTED/'ImbalancedChen', ACCEPTED/'objects/ImbalancedChen',
         '2e5f28f61658c1cfd84112417585e9df09b0cdafcd56e66f94a9ab0cf244f362',
         'e8d785d76de156581dc5ae2c986d98bc7cc44387695ebb31f10110d0ea2719d9'),
        ('P2OriginalSaving19CharacterLength00', ACCEPTED/'ImbalancedChen', ACCEPTED/'objects/ImbalancedChen',
         '17c3dacad6c8acbae2be804c9ca1f27ba663d9db7b44cd16374e9635ec3508cc',
         '4dcfa678dad2b10c69798981a79d40d2408c26671b4957b6882b459adea5e498'),
        ('P2OriginalSaving19DimensionPrefix00', ACCEPTED/'ImbalancedChen', ACCEPTED/'objects/ImbalancedChen',
         'd64263d9c3e35fe05bd998cdaf5f523ea7ae2db933bcd41ca31f9033f5b162aa',
         '2792ba91cb949245fefb1cd11b21990399a6eb7e44359f9d95b95d4c28784304'),
        ('P2OriginalSaving19FirstThreeFields00', ACCEPTED/'ImbalancedChen', ACCEPTED/'objects/ImbalancedChen',
         '917489d7281d18b9bdd25027ff6fd4b58e65a16d98465dff7c6ecee0bb3e68a0',
         '1c49efaa3ffa5fac22e9906a8413036f7087e3ca74a979d08d123a2c8f337a79'),
    ]
    for name, src, obj, src_sha, obj_sha in sources:
        rows.append({'module': 'ImbalancedChen.' + name,
                     'source': require_hash(src/(name+'.lean'), src_sha),
                     'object': require_hash(obj/(name+'.olean'), obj_sha),
                     'action': 'reuse byte-identical object; never recompile'})
    return rows


def write_checked(path: Path, content: bytes, check: bool, revise: bool) -> None:
    if path.exists():
        old = path.read_bytes()
        if old == content:
            return
        assert revise and not check, ('Refusing drift/overwrite; use explicit --revise after review.', str(path))
        backup = ROOT/'revisions'/sha(old)/path.relative_to(ROOT)
        backup.parent.mkdir(parents=True, exist_ok=True)
        if backup.exists():
            assert backup.read_bytes() == old
        else:
            backup.write_bytes(old)
    else:
        assert not check, ('Missing generated artifact', str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--revise', action='store_true')
    ap.add_argument('--chunk-items', type=int, default=4)
    ap.add_argument('--child-certificate', type=Path,
                    help='Optional original value-reader supplier; source fingerprint and type are rechecked.')
    args = ap.parse_args()
    assert not (args.check and args.revise)
    raw = FIXTURE.read_bytes()
    assert len(raw) == 195134 and sha(raw) == FIXTURE_SHA and raw.isascii()
    planner = RawPlanner(raw)
    fields = planner.first_fields(4)
    assert [f.key.scalar for f in fields] == [
        'dimension', 'physical_jacobian', 'facet_original_indices', 'positive_normal_balance']
    dim, dim_plan = reproduce_dimension(raw, fields[0])
    chunks = array_chunks(raw, fields[3].value, args.chunk_items)
    external = None
    if args.child_certificate:
        data = json.loads(args.child_certificate.read_text())
        data['span'] = tuple(data['span'])
        external = ValueCertificateRef(**data)
        assert external.module != MODULE, 'Self-import is forbidden.'
    source, fourth_plan = emit_fourth(raw, fields[3], chunks, external)
    source_path = ROOT/(MODULE.replace('.', '/') + '.lean')
    reproduced = ROOT/'reproduced/P2OriginalSaving19DimensionPrefix00.lean'
    plan = {'schema': 'source-json-segments-v1', 'trust': 'untrusted host plan; all outputs require Lean',
            'fixture': fingerprint(FIXTURE), 'ascii_byte_offsets_equal_char_offsets': True,
            'line_endings': 'original CRLF preserved by read_bytes; no newline normalization',
            'scan_limit': 'first four fields only', 'farthest_byte_scanned_exclusive': planner.farthest_scanned,
            'root_value_fuel': len(raw)+1, 'fields': [f.plan() for f in fields],
            'dimension_reproduction': dim_plan, 'fourth_field': fourth_plan,
            'accepted_parent_state': {
                'theorem': NS+'.geometryChars00_through_facet_indices',
                'value_fuel': len(raw)+1, 'object_fuel': len(raw)+1-4,
                'rest': 'SourceJson.white (geometryChars00.drop 179)',
                'reverse_accumulator': 'facetIndicesAcc00'},
            'no_whole_parse_success_claim': True, 'no_old_string_equivalence_claim': True}
    reused = dependencies()
    manifest = {'schema': 'source-json-segment-owner-v1', 'status': 'generated; see separate diagnostic receipts',
        'scope': 'one new fourth-field owner, 3 original-array chunks; dimension byte reproduction only',
        'fixture': fingerprint(FIXTURE), 'reader_sha256': READER_SHA,
        'files': [{'module': MODULE, 'path': str(source_path.relative_to(ROOT)),
                   'bytes': len(source), 'sha256': sha(source),
                   'imports': ['ImbalancedChen.P2OriginalSaving19FirstThreeFields00'] +
                              ([external.module] if external else [])}],
        'generator': fingerprint(Path(__file__)),
        'dimension_template': fingerprint(ROOT/'templates/DimensionPrefix00.lean.tmpl'),
        'dimension_reproduction': {'path': str(reproduced.relative_to(ROOT)),
                                   'bytes': len(dim), 'sha256': sha(dim), 'compile': False},
        'reused_dependencies': reused,
        'direct_new_owner_count': 1, 'new_array_chunk_theorem_count': len(chunks),
        'new_Lean_declaration_names': fourth_plan['declaration_names_checked_for_axioms'],
        'limits_local_each_step': {'rss_bytes': 4*1024**3, 'wall_seconds': 180,
                                  'lean_threads': 1, 'maxRecDepth': 1000000, 'maxHeartbeats': 0},
        'compile_order': ['new owner normal', 'independent kernel on new owner only if normal succeeds'],
        'production_modified': False, 'remote_jobs_submitted': False,
        'accepted_dependencies_recompiled': False, 'host_parse_is_evidence': False,
        'old_string_equivalence_claimed': False, 'whole_parse_success_claimed': False,
        'external_child_mode': 'type-checked interface implemented; not exercised by this pilot' if not external else
                               'requires a separate recorded Lean diagnostic'}
    for p, b in [(reproduced, dim), (source_path, source),
                 (ROOT/'SEGMENT_PLAN.json', (json.dumps(plan, indent=2)+'\n').encode()),
                 (ROOT/'SOURCE_MANIFEST.json', (json.dumps(manifest, indent=2)+'\n').encode())]:
        write_checked(p, b, args.check, args.revise)
    print(json.dumps({'check': args.check, 'source': {'path': str(source_path), 'bytes': len(source),
          'sha256': sha(source)}, 'dimension_reproduced_sha256': sha(dim),
          'raw_field_span': [fields[3].prefix_start, fields[3].prefix_end],
          'array_value_offset': fourth_plan['array_value_offset'],
          'object_offsets': fourth_plan['object_offsets'], 'chunks': chunks}, indent=2))


if __name__ == '__main__':
    main()
