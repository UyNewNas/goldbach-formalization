#!/usr/bin/env python3
"""Data-only child value certificates, preserving the original reader and raw text."""
import raw_planner as base

RAW = b''
CELL = None
CHUNKS = None
LIMIT = 768

def configure(cell, raw, chunks):
    global CELL, RAW, CHUNKS
    assert 1 <= cell <= 12 and raw.isascii()
    CELL, RAW, CHUNKS = cell, raw, chunks

def mark(label):
    return ('run_cmd do\n  let err ← IO.getStderr\n'
            f'  err.putStrLn "P26_DIRECT_PACKED {label}"\n  err.flush\n\n')


def ref(node):
    assert CELL is not None and RAW
    stem=f'fragment{node.start:07d}'
    short=f'P2OriginalSaving19Geometry{CELL:02d}ValueFragment{node.start:07d}'
    return {'short':short,'module':'ImbalancedChen.'+short,
            'stem':stem,'chars':stem+'Chars','value':stem+'Value',
            'theorem':'value_'+stem,'need':node.need,'node':node}


def needs_ref(node):
    return node.end-node.start>LIMIT


def append_chain(names, tail=None):
    assert names
    if tail is None:return ' ++ '.join(names)
    result=tail
    for name in reversed(names):result=f'{name} ++ ({result})'
    return result


def children_to_certify(node):
    if node.kind=='arr':return [n for n in node.children if needs_ref(n)]
    if node.kind=='obj':return [f.value for f in node.fields if needs_ref(f.value)]
    return []


def array_segment(name, theorem, start, end, nodes, before, after, final):
    """Return candidate chars/push defs and original array theorem for one chunk."""
    large=[n for n in nodes if needs_ref(n)]
    assert before>0
    if large:
        assert len(nodes)==1 and len(large)==1
        child=large[0];r=ref(child)
        assert child.kind!='number' and before-1>=child.need
        lead=name+'LeadChars00';suffix=name+'SuffixChars00'
        text=f'def {lead} : List Char := {base.chars(RAW,start,child.start)}\n'
        text+=f'def {suffix} : List Char := {base.chars(RAW,child.end,end)}\n'
        text+=f'def {name}Chars00 : List Char := {lead} ++ {r["chars"]} ++ {suffix}\n'
        text+=f'def {name}Push00 (acc : List SourceJson) : List SourceJson := {r["value"]} :: acc\n\n'
    else:
        text=f'def {name}Chars00 : List Char := {base.chars(RAW,start,end)}\n'
        push='acc'
        for node in nodes:push=f'({base.lean_node(node)}) :: ({push})'
        text+=f'def {name}Push00 (acc : List SourceJson) : List SourceJson :=\n  {push}\n\n'
    rhs=(f'.ok (.arr (({name}Push00 acc).reverse), tail)' if final else
         f'SourceJson.array (fuel + {after}) (SourceJson.white tail) ({name}Push00 acc)')
    statement=f'''theorem {theorem} (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + {before}) (SourceJson.white ({name}Chars00 ++ tail)) acc =
      {rhs} := by
'''
    if not large:return text+statement+'  rfl\n\n', []
    cont=name+'AfterValue00';header=theorem+'_head'
    text+=f'''def {cont} (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem {header} (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + {before})
      (SourceJson.white ({lead} ++ ({r['chars']} ++ rest))) acc =
      (SourceJson.value (fuel + {before-1}) ({r['chars']} ++ rest)).bind
        ({cont} (fuel + {before-1}) acc) := by rfl

'''
    text+=statement+f'''  have hinput : {name}Chars00 ++ tail = {lead} ++ ({r['chars']} ++ ({suffix} ++ tail)) := by
    simp only [{name}Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + {before}) (SourceJson.white ({name}Chars00 ++ tail)) acc =
        SourceJson.array (fuel + {before})
          (SourceJson.white ({lead} ++ ({r['chars']} ++ ({suffix} ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + {before}) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + {before-1}) ({r['chars']} ++ ({suffix} ++ tail))).bind
        ({cont} (fuel + {before-1}) acc) := {header} fuel ({suffix} ++ tail) acc
    _ = (Except.ok ({r['value']}, {suffix} ++ tail)).bind
        ({cont} (fuel + {before-1}) acc) :=
      congrArg (fun result => result.bind ({cont} (fuel + {before-1}) acc))
        ({r['theorem']} (fuel + {before-1-child.need}) ({suffix} ++ tail))
    _ = {rhs} := by rfl

'''
    return text,[header]


def emit_small(node):
    r=ref(node)
    assert node.kind!='number', 'Numeric child certificates require an explicit delimiter frame.'
    text=f'def {r["chars"]} : List Char := {base.chars(RAW,node.start,node.end)}\n'
    text+=f'def {r["value"]} : SourceJson := {base.lean_node(node)}\n\n'
    text+=f'''theorem {r['theorem']} (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + {node.need}) ({r['chars']} ++ tail) =
      .ok ({r['value']}, tail) := by rfl

'''
    return text,[r['theorem']]


def emit_array(node):
    assert CHUNKS is not None
    r=ref(node);stem=r['stem']
    chunks=CHUNKS(node,2,LIMIT)
    text=f'def {stem}Acc00000 : List SourceJson := []\n\n';names=[];char_names=[]
    for c in chunks:
        i=c['index'];name=f'{stem}Chunk{i:03d}';thm=f'array_{stem}_chunk_{i:03d}'
        emitted,extra=array_segment(name,thm,c['start'],c['end'],
            node.children[c['first']:c['after']],c['before_offset'],c['after_offset'],c['final'])
        text+=emitted
        text+=f'def {stem}Acc{i+1:03d}00 : List SourceJson := {name}Push00 {stem}Acc{i:03d}00\n\n'
        text+=mark(stem+f'_array_chunk_{i:03d}')
        names+=extra+[thm];char_names.append(name+'Chars00')
    text+=f"def {r['chars']} : List Char := '[' :: ({append_chain(char_names)})\n"
    text+=f'def {r["value"]} : SourceJson := .arr ({stem}Acc{len(chunks):03d}00.reverse)\n\n'
    payload=append_chain(char_names,'tail')
    text+=f'''theorem {r['theorem']} (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + {node.need}) ({r['chars']} ++ tail) =
      .ok ({r['value']}, tail) := by
  have hinput : {r['chars']} ++ tail = '[' :: ({payload}) := by
    simp only [{r['chars']}, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + {node.need}) ({r['chars']} ++ tail) =
        SourceJson.value (fuel + {node.need}) ('[' :: ({payload})) :=
      congrArg (SourceJson.value (fuel + {node.need})) hinput
    _ = SourceJson.array (fuel + {node.need-1}) (SourceJson.white ({payload})) {stem}Acc00000 := by rfl
'''
    for i,c in enumerate(chunks):
        rest=append_chain(char_names[i+1:],'tail') if i+1<len(chunks) else 'tail'
        if c['final']:rhs=f'.ok ({r["value"]}, tail)'
        else:rhs=f'SourceJson.array (fuel + {c["after_offset"]}) (SourceJson.white ({rest})) {stem}Acc{i+1:03d}00'
        text+=f'    _ = {rhs} := array_{stem}_chunk_{i:03d} fuel ({rest}) {stem}Acc{i:03d}00\n'
    text+='\n';names.append(r['theorem'])
    return text,names


def emit_object(node):
    r=ref(node);stem=r['stem'];text=f'def {stem}Acc00000 : List (String × SourceJson) := []\n\n'
    names=[];char_names=[]
    for i,f in enumerate(node.fields):
        name=f'{stem}Field{i:03d}';key=name+'Key00';value=name+'Value00'
        acc=f'{stem}Acc{i:03d}00';nextacc=f'{stem}Acc{i+1:03d}00'
        before=node.need-1-i;after=before-1;last=i+1==len(node.fields)
        start=node.start+1 if i==0 else f.prefix_start
        child=ref(f.value) if needs_ref(f.value) else None
        value_expr=child['value'] if child else base.lean_node(f.value)
        text+=f'def {key} : String := String.ofList {base.quote_list(f.key.scalar)}\n'
        text+=f'def {value} : SourceJson := {value_expr}\n'
        text+=f'def {nextacc} : List (String × SourceJson) := ({key}, {value}) :: {acc}\n'
        if child:
            header=name+'HeaderChars00';suffix=name+'SuffixChars00'
            text+=f'def {header} : List Char := {base.chars(RAW,start,f.value.start)}\n'
            text+=f'def {suffix} : List Char := {base.chars(RAW,f.value.end,f.prefix_end)}\n'
            text+=f'def {name}Chars00 : List Char := {header} ++ {child["chars"]} ++ {suffix}\n\n'
        else:text+=f'def {name}Chars00 : List Char := {base.chars(RAW,start,f.prefix_end)}\n\n'
        thm=f'object_{stem}_field_{i:03d}'
        rhs=(f'.ok (.obj ({nextacc}.reverse), tail)' if last else
             f'SourceJson.object (fuel + {after}) (SourceJson.white tail) {nextacc}')
        statement=f'''theorem {thm} (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + {before}) (SourceJson.white ({name}Chars00 ++ tail)) {acc} =
      {rhs} := by
'''
        if not child:text+=statement+'  rfl\n\n'
        else:
            assert f.value.kind!='number' and after>=f.value.need
            cont=name+'AfterValue00';hthm=thm+'_header'
            text+=f'''def {cont} (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}}' :: ending => .ok (.obj ((({key}, result.1) :: {acc}).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) (({key}, result.1) :: {acc})
  | _ => .error "object separator missing"

theorem {hthm} (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + {before}) (SourceJson.white ({header} ++ rest)) {acc} =
      (SourceJson.value (fuel + {after}) rest).bind ({cont} (fuel + {after})) := by rfl

'''
            text+=statement+f'''  have hinput : {name}Chars00 ++ tail = {header} ++ ({child['chars']} ++ ({suffix} ++ tail)) := by
    simp only [{name}Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + {before}) (SourceJson.white ({name}Chars00 ++ tail)) {acc} =
        SourceJson.object (fuel + {before})
          (SourceJson.white ({header} ++ ({child['chars']} ++ ({suffix} ++ tail)))) {acc} :=
      congrArg (fun s => SourceJson.object (fuel + {before}) (SourceJson.white s) {acc}) hinput
    _ = (SourceJson.value (fuel + {after}) ({child['chars']} ++ ({suffix} ++ tail))).bind
        ({cont} (fuel + {after})) := {hthm} fuel ({child['chars']} ++ ({suffix} ++ tail))
    _ = (Except.ok ({child['value']}, {suffix} ++ tail)).bind ({cont} (fuel + {after})) :=
      congrArg (fun result => result.bind ({cont} (fuel + {after})))
        ({child['theorem']} (fuel + {after-f.value.need}) ({suffix} ++ tail))
    _ = {rhs} := by rfl

'''
            names.append(hthm)
        text+=mark(stem+f'_object_field_{i:03d}')
        names.append(thm);char_names.append(name+'Chars00')
    text+=f"def {r['chars']} : List Char := '{{' :: ({append_chain(char_names)})\n"
    text+=f'def {r["value"]} : SourceJson := .obj ({stem}Acc{len(node.fields):03d}00.reverse)\n\n'
    payload=append_chain(char_names,'tail')
    text+=f'''theorem {r['theorem']} (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + {node.need}) ({r['chars']} ++ tail) =
      .ok ({r['value']}, tail) := by
  have hinput : {r['chars']} ++ tail = '{{' :: ({payload}) := by
    simp only [{r['chars']}, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + {node.need}) ({r['chars']} ++ tail) =
        SourceJson.value (fuel + {node.need}) ('{{' :: ({payload})) :=
      congrArg (SourceJson.value (fuel + {node.need})) hinput
    _ = SourceJson.object (fuel + {node.need-1}) (SourceJson.white ({payload})) {stem}Acc00000 := by rfl
'''
    for i,f in enumerate(node.fields):
        rest=append_chain(char_names[i+1:],'tail') if i+1<len(node.fields) else 'tail'
        if i+1==len(node.fields):rhs=f'.ok ({r["value"]}, tail)'
        else:rhs=f'SourceJson.object (fuel + {node.need-2-i}) (SourceJson.white ({rest})) {stem}Acc{i+1:03d}00'
        text+=f'    _ = {rhs} := object_{stem}_field_{i:03d} fuel ({rest})\n'
    text+='\n';names.append(r['theorem'])
    return text,names

