#!/usr/bin/env python3
"""Generate exact original-reader certificates; all host planning is untrusted.

The RawPlanner/Node/Field classes are executed verbatim from the preserved P2.6
donor. No host result is proof evidence: each emitted equality must pass Lean.
Only this package is written. Existing input, parser, decoder and archive owners
are never modified.
"""
from __future__ import annotations

import argparse
import ast
import dataclasses
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PACKAGE = ROOT.parent
REPO = PACKAGE.parents[2]
INPUT = REPO / '.lake/p25-original-inputs/eighth-prefix-family-20261009-cell-00.witness.json'
INPUT_SHA = '360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6'
DONOR_SHA = '3114c68369ad3a6e3f7e3171aedadb40830917cf1592cc09e99932afdf71703d'
NS = 'ImbalancedChen.P2Saving16Cell00Segments'
WHITE = b' \r\n\t'


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def quote_char(c: str) -> str:
    escapes = {'\r': r'\r', '\n': r'\n', '\t': r'\t', '\\': r'\\', "'": r"\'"}
    if ord(c) < 32 and c not in escapes:
        return f'(Char.ofNat {ord(c)})'
    return "'" + escapes.get(c, c) + "'"


def qlist(data: bytes | str) -> str:
    s = data.decode('ascii') if isinstance(data, bytes) else data
    return '[' + ', '.join(quote_char(c) for c in s) + ']'


def concatenate(names: list[str], tail: str = '[]') -> str:
    out = tail
    for name in reversed(names):
        out = f'{name} ++ ({out})'
    return out


def load_planner():
    donor = (PACKAGE/'donor/generate.py').read_bytes()
    assert sha(donor) == DONOR_SHA
    tree = ast.parse(donor)
    body = [n for n in tree.body if isinstance(n, ast.ClassDef) and n.name in {'Node', 'Field', 'RawPlanner'}]
    ns = {'dataclass': dataclasses.dataclass, 'field': dataclasses.field,
          'WHITE': WHITE, '__name__': '__main__'}
    exec(compile(ast.Module(body=body, type_ignores=[]), '<unchanged donor planner classes>', 'exec'), ns)
    return ns['RawPlanner']


class Emitter:
    def __init__(self, raw: bytes):
        self.raw = raw
        self.next_id = 0
        self.plans = []

    def identify(self, node):
        node.uid = f'n{self.next_id:05d}'
        self.next_id += 1
        for c in node.children:
            self.identify(c)
        for f in node.fields:
            self.identify(f.value)

    def value(self, n):
        if n.kind in {'str', 'number'}:
            return f'.{n.kind} (String.ofList {qlist(n.scalar)})'
        if n.kind == 'boolean':
            return '.boolean ' + str(n.scalar).lower()
        if n.kind == 'null':
            return '.null'
        if n.kind == 'arr':
            return '.arr [' + ', '.join(c.uid+'Value' for c in n.children) + ']'
        return '.obj [' + ', '.join(f'({n.uid}Key{i}, {f.value.uid}Value)' for i, f in enumerate(n.fields)) + ']'

    def module_header(self, imports):
        return ''.join('import '+s+'\n' for s in imports) + f'''\n/-!
Generated candidate equalities for the unchanged original SourceJson reader.
Raw bytes, fuel offsets and AST data are untrusted until these proofs check.
Every continuation retains exact whitespace, delimiters, reverse accumulators,
duplicate-key checks, and the complete arbitrary unconsumed tail.
-/
namespace {NS}
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open P2OriginalSaving19Archive
noncomputable section
\n'''

    def module_footer(self):
        return f'\nend\nend {NS}\n'

    def emit(self, n, recurse=True):
        chunks = []
        if recurse:
            for c in n.children:
                chunks.append(self.emit(c))
            for f in n.fields:
                chunks.append(self.emit(f.value))
        p = []
        ident = n.uid
        self.plans.append({'node': ident, 'kind': n.kind, 'span': [n.start,n.end], 'fuel_offset':n.need})
        if n.kind not in {'arr','obj'} or not (n.children or n.fields):
            p.append(f'def {ident}Chars : List Char := {qlist(self.raw[n.start:n.end])}\n')
            p.append(f'def {ident}Value : SourceJson := {self.value(n)}\n')
            if n.kind == 'number':
                delimiter = self.raw[n.end:n.end+1].decode('ascii')
                assert len(delimiter) == 1 and not delimiter.isdigit()
                frame = f'{quote_char(delimiter)} :: tail'
                p.append(f'theorem {ident}Parse (fuel : Nat) (tail : List Char) :\n'
                         f'    SourceJson.value (fuel + {n.need}) ({ident}Chars ++ ({frame})) =\n'
                         f'      .ok ({ident}Value, {frame}) := by\n'
                         f'  rw [SourceJson.value_succ]\n  rfl\n\n')
            else:
                p.append(f'theorem {ident}Parse (fuel : Nat) (tail : List Char) :\n'
                         f'    SourceJson.value (fuel + {n.need}) ({ident}Chars ++ tail) =\n'
                         f'      .ok ({ident}Value, tail) := by\n'
                         f'  rw [SourceJson.value_succ]\n  rfl\n\n')
            return ''.join(chunks+p)

        is_arr = n.kind == 'arr'
        children = n.children if is_arr else [f.value for f in n.fields]
        count = len(children)
        parts = []
        cursor = n.start + 1
        for i,c in enumerate(children):
            if is_arr:
                ending = c.end
                while self.raw[ending] in WHITE:
                    ending += 1
                assert self.raw[ending] == ord(',' if i+1<count else ']')
                ending += 1
            else:
                ending = n.fields[i].prefix_end
                p.append(f'def {ident}Key{i} : String := String.ofList {qlist(n.fields[i].key.scalar)}\n')
            head = self.raw[cursor:c.start]
            endraw = self.raw[c.end:ending]
            p.append(f'def {ident}Header{i} : List Char := {qlist(head)}\n')
            p.append(f'def {ident}Ending{i} : List Char := {qlist(endraw)}\n')
            p.append(f'def {ident}Part{i} : List Char := {ident}Header{i} ++ ({c.uid}Chars ++ {ident}Ending{i})\n')
            parts.append(ident+f'Part{i}')
            cursor = ending
        assert cursor == n.end
        opening = '[' if is_arr else '{'
        p.append(f'def {ident}Chars : List Char := {quote_char(opening)} :: ({concatenate(parts)})\n')
        p.append(f'def {ident}Value : SourceJson := {self.value(n)}\n')
        acc_type = 'SourceJson' if is_arr else '(String × SourceJson)'
        p.append(f'def {ident}Acc0 : List {acc_type} := []\n')
        for i,c in enumerate(children):
            v = c.uid+'Value' if is_arr else f'({ident}Key{i}, {c.uid}Value)'
            p.append(f'def {ident}Acc{i+1} : List {acc_type} := {v} :: {ident}Acc{i}\n')
        p.append('\n')

        parser = 'array' if is_arr else 'object'
        after = 'arrayAfter' if is_arr else 'objectAfter'
        for i,c in enumerate(children):
            before = n.need - 1 - i
            subfuel = before - 1
            assert subfuel >= c.need
            cont = f'({after} (fuel + {subfuel}) {ident}Acc{i}' + ('' if is_arr else f' {ident}Key{i}') + ')'
            if is_arr:
                p.append(f'theorem {ident}Head{i} (fuel : Nat) (rest : List Char) :\n'
                         f'    SourceJson.array (fuel + {before})\n'
                         f'      (SourceJson.white ({ident}Header{i} ++ ({c.uid}Chars ++ rest))) {ident}Acc{i} =\n'
                         f'      (SourceJson.value (fuel + {subfuel}) ({c.uid}Chars ++ rest)).bind {cont} := by\n'
                         f'  rw [SourceJson.array_succ]\n  rfl\n\n')
            else:
                p.append(f'theorem {ident}Head{i} (fuel : Nat) (rest : List Char) :\n'
                         f'    SourceJson.object (fuel + {before})\n'
                         f'      (SourceJson.white ({ident}Header{i} ++ rest)) {ident}Acc{i} =\n'
                         f'      (SourceJson.value (fuel + {subfuel}) rest).bind {cont} := by\n'
                         f'  rw [SourceJson.object_succ]\n  rfl\n\n')
            rhs = (f'.ok ({ident}Value, tail)' if i+1==count else
                   f'SourceJson.{parser} (fuel + {subfuel}) (SourceJson.white tail) {ident}Acc{i+1}')
            parsed_tail = f'{ident}Ending{i} ++ tail'
            # Integer tokens need the actual non-digit next character inside the
            # theorem frame, rather than an unsound arbitrary-tail interface.
            if c.kind == 'number':
                end = c.end
                while self.raw[end] in WHITE:
                    end += 1
                end += 1
                child_arg = f'({qlist(self.raw[c.end+1:end])} ++ tail)'
            else:
                child_arg = f'({parsed_tail})'
            p.append(f'theorem {ident}Step{i} (fuel : Nat) (tail : List Char) :\n'
                     f'    SourceJson.{parser} (fuel + {before})\n'
                     f'      (SourceJson.white ({ident}Part{i} ++ tail)) {ident}Acc{i} =\n'
                     f'      {rhs} := by\n'
                     f'  have hinput : {ident}Part{i} ++ tail =\n'
                     f'      {ident}Header{i} ++ ({c.uid}Chars ++ ({parsed_tail})) := by\n'
                     f'    simp only [{ident}Part{i}, List.append_assoc]\n'
                     f'  have hchild : SourceJson.value (fuel + {subfuel})\n'
                     f'      ({c.uid}Chars ++ ({parsed_tail})) = .ok ({c.uid}Value, {parsed_tail}) :=\n'
                     f'    {c.uid}Parse (fuel + {subfuel-c.need}) {child_arg}\n'
                     f'  calc\n'
                     f'    _ = SourceJson.{parser} (fuel + {before})\n'
                     f'        (SourceJson.white ({ident}Header{i} ++ ({c.uid}Chars ++ ({parsed_tail})))) {ident}Acc{i} :=\n'
                     f'      congrArg (fun cs => SourceJson.{parser} (fuel + {before}) (SourceJson.white cs) {ident}Acc{i}) hinput\n'
                     f'    _ = (SourceJson.value (fuel + {subfuel}) ({c.uid}Chars ++ ({parsed_tail}))).bind {cont} :=\n'
                     f'      {ident}Head{i} fuel '+(f'({parsed_tail})' if is_arr else f'({c.uid}Chars ++ ({parsed_tail}))')+'\n'
                     f'    _ = (Except.ok ({c.uid}Value, {parsed_tail})).bind {cont} :=\n'
                     f'      congrArg (fun r => r.bind {cont}) hchild\n'
                     f'    _ = {rhs} := by rfl\n\n')

        payload = concatenate(parts,'tail')
        p.append(f'theorem {ident}Parse (fuel : Nat) (tail : List Char) :\n'
                 f'    SourceJson.value (fuel + {n.need}) ({ident}Chars ++ tail) =\n'
                 f'      .ok ({ident}Value, tail) := by\n'
                 f'  have hinput : {ident}Chars ++ tail = {quote_char(opening)} :: ({payload}) := by\n'
                 f'    simp only [{ident}Chars, List.cons_append, List.append_assoc, List.nil_append]\n'
                 f'  calc\n'
                 f'    _ = SourceJson.value (fuel + {n.need}) ({quote_char(opening)} :: ({payload})) :=\n'
                 f'      congrArg (SourceJson.value (fuel + {n.need})) hinput\n'
                 f'    _ = SourceJson.{parser} (fuel + {n.need-1}) (SourceJson.white ({payload})) {ident}Acc0 := by\n'
                 f'      rw [SourceJson.value_succ]\n      rfl\n')
        for i,c in enumerate(children):
            if i+1 == count:
                p.append(f'    _ = .ok ({ident}Value, tail) := {ident}Step{i} fuel tail\n\n')
            else:
                remaining = concatenate(parts[i+1:],'tail')
                p.append(f'    _ = SourceJson.{parser} (fuel + {n.need-2-i})\n'
                         f'        (SourceJson.white ({remaining})) {ident}Acc{i+1} :=\n'
                         f'      {ident}Step{i} fuel ({remaining})\n')
        return ''.join(chunks+p)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--check',action='store_true')
    args=ap.parse_args()
    raw=INPUT.read_bytes()
    assert len(raw)==53305 and sha(raw)==INPUT_SHA and raw.isascii()
    root=load_planner()(raw).value(0)
    assert root.end==53303 and raw[root.end:]==b'\r\n' and root.need==371
    emitter=Emitter(raw); emitter.identify(root)
    sources=[]; field_modules=[]
    def save(name,text):
        p=ROOT/'ImbalancedChen'/(name+'.lean'); data=text.encode()
        if args.check:
            assert p.read_bytes()==data, str(p)
        else:
            p.write_bytes(data)
        sources.append({'module':'ImbalancedChen.'+name,'bytes':len(data),'sha256':sha(data)})
    for i,f in enumerate(root.fields):
        name=f'P2Saving16Cell00SegmentField{i:02d}'
        field_modules.append('ImbalancedChen.'+name)
        text=emitter.module_header(['ImbalancedChen.P2Saving16Cell00SegmentSupport'])
        text+=emitter.emit(f.value)
        text+=f'#print axioms {f.value.uid}Parse\n'+emitter.module_footer()
        save(name,text)
    text=emitter.module_header(field_modules+['ImbalancedChen.P2Saving16StringCharBinding00'])
    text+=emitter.emit(root,recurse=False)
    text+='''
def rootValue : SourceJson := n00000Value

def completeChars : List Char := n00000Chars ++ ['\r', '\n']

theorem completeChars_eq_chars00 :
    completeChars = P2Saving16StringCharBinding00.chars00 := by
  rfl

theorem chars00_length : P2Saving16StringCharBinding00.chars00.length = 53305 := by
  rfl

theorem cell00_value :
    SourceJson.value 53306 P2Saving16StringCharBinding00.chars00 =
      .ok (rootValue, ['\r', '\n']) := by
  rw [← completeChars_eq_chars00]
  exact n00000Parse 52935 ['\r', '\n']

#print axioms completeChars_eq_chars00
#print axioms chars00_length
#print axioms cell00_value
'''.replace("['\r', '\n']",r"['\r', '\n']")
    text+=emitter.module_footer()
    save('P2Saving16Cell00SegmentedParse',text)
    plan={'status':'GENERATED_SOURCE_ONLY_NOT_COMPILED','input':{'path':str(INPUT.relative_to(REPO)),'bytes':len(raw),'sha256':INPUT_SHA},
          'donor':{'commit':'bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3','path':'docs/verification/20261125-p26/archive-segment-generator/generate.py','sha256':DONOR_SHA,
                   'reused_classes':['Node','Field','RawPlanner'],'classes_source_unchanged':True},
          'root_fuel':53306,'generic_root_offset':371,'sources':sources,'nodes':emitter.plans}
    if not args.check:
        (ROOT/'SOURCE_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
    print(json.dumps({'sources':len(sources),'nodes':len(emitter.plans),'bytes':sum(s['bytes'] for s in sources),'check':args.check}))


if __name__=='__main__':
    main()
