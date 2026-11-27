#!/usr/bin/env python3
"""Render the pinned Cell03 finite-archive specialization without invoking Lean."""
import argparse
import hashlib
import importlib.util
import json
import re
from fractions import Fraction
from pathlib import Path

from typed_literals import render as render_typed

HERE = Path(__file__).resolve().parent
SOURCES = HERE.parent
REPO = SOURCES.parents[1]
PARSER = SOURCES / "20261126-p2-5-cell01-parser-typed"
DECODE = SOURCES / "20261127-p2-5-cell01-decoder"
ARITH = SOURCES / "20261127-p2-5-cell01-arithmetic"
FACTS = SOURCES / "20261127-p2-5-cell01-source-facts"
CANON = SOURCES / "20261125-p2-5-canonical-char-loader"
CACHE = REPO / "docs/verification/20261127-p2-5-pulling-sourcefacts/CACHED_OBJECTS.json"
WITNESS_SHA = "c03bdf2cf22aabd8fcb6828ac3a405129bbdfe0837afc17208156405bf06b414"
OLD_SUM = "292535084187454643081"
PREFIX = "P2Saving16Cell03"
pins = {}
outputs = {}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def checked(path):
    relative = str(path.relative_to(REPO))
    data = path.read_bytes()
    if sha(data) != pins[relative]:
        raise ValueError("Changed source input: " + relative)
    return data


def host_module(path):
    checked(path)
    spec = importlib.util.spec_from_file_location(path.stem, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def specialize(s):
    return (s.replace("Cell01", "Cell03").replace("cell01", "cell03")
             .replace("chars01", "chars03").replace("originalText1", "originalText3")
             .replace("(1 : Fin 14)", "(3 : Fin 14)").replace("archive 1", "archive 3"))


def template(folder, suffix):
    filename = "P2Saving16Cell01" + suffix + ".lean"
    return specialize(checked(folder / "ImbalancedChen" / filename).decode())


def put(module, source):
    key = "ImbalancedChen/" + module + ".lean"
    if key in outputs:
        raise ValueError("Duplicate owner: " + module)
    outputs[key] = source.encode()


def dump(key, obj):
    outputs[key] = (json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode()


def read_original(path):
    data = path.read_bytes()
    if len(data) != 125188 or sha(data) != WITNESS_SHA or not data.isascii():
        raise ValueError("Unexpected original Cell03 bytes")
    planner_mod = host_module(PARSER / "measure_input.py")
    ns, schemas = planner_mod.donor_namespace()
    tree = ns["RawPlanner"](data).value(0)
    doc = json.loads(data)
    assert doc["cell_id"] == 3 and doc["dimension"] == 8 and doc["physical_jacobian"] == 1
    assert list(doc) == [f.key.scalar for f in tree.fields] == [k for k, _ in schemas["FIELDS"]]
    rows = doc["simplices"]
    assert len(rows) == 21 and len(doc["vertices"]) == 23 and len(doc["active8_enumeration"]) == 165
    assert all(r["simplex_id"] == i and list(r) == [k for k,_ in schemas["SIMPLEX_FIELDS"]]
               for i,r in enumerate(rows))
    assert data[tree.end:] == bytes([13,10])
    rat = [*doc["positive_normal_balance"], *doc["all_original_constraint_minima"],
           doc["physical_volume"], doc["integral_gap"]]
    for v in doc["vertices"]:
        rat.extend(v)
    integers = []
    for r in rows:
        rat.extend(r[k] for k in ("physical_volume","mean_gap","max_bound","jensen_bound"))
        rat.extend(r["factor_maxima"])
        rat.extend(r["gap_weighted_means"])
        integers.extend((r["max_floor_Q96"],r["jensen_floor_Q96"]))
        q = Fraction(r["jensen_bound"]) * 2**96
        assert int(r["jensen_floor_Q96"]) == q.numerator // q.denominator
    counts = {"unique_rational_strings":len(set(rat)), "rational_occurrences":len(rat),
              "unique_integer_strings":len(set(integers)), "integer_occurrences":len(integers),"simplices":21}
    typed, spec = render_typed(data,tree,doc,ns,schemas,{"counts":counts})
    put(PREFIX + "TypedPayload",typed)
    return data, tree, ns, doc, typed, spec, counts


def parser_sources(data, tree, ns):
    path = CANON / "ImbalancedChen/P2Saving16CanonicalCell01Binding.lean"
    put("P2Saving16CanonicalCell03Binding",specialize(checked(path).decode()))
    old = template(PARSER,"DirectParse")
    start = old.index("def rootValue : SourceJson :=\n  ") + len("def rootValue : SourceJson :=\n  ")
    end = old.index("\n\ntheorem cell03_value",start)
    old = old[:start].replace("cell03 AST","Cell03 AST") + ns["lean_node"](tree) + old[end:].replace("532",str(tree.need))
    put(PREFIX + "DirectParse",old)
    for suffix in ("SegmentedParse","OriginalJson"):
        s = template(PARSER,suffix).replace("344874",str(len(data)+1)).replace("344873",str(len(data))).replace("532",str(tree.need))
        put(PREFIX+suffix,s)


def scalar_sources(spec,typed,cache):
    mod = host_module(DECODE / "generate_scalar_decode.py")
    mod.PREFIX, mod.SCALAR, mod.FIELD_NS = PREFIX, PREFIX+"ScalarDecode", PREFIX+"FieldDecode"
    mod.HEADER = specialize(mod.HEADER)
    names=mod.scalar_definitions(typed)
    old_proofs={}
    for cell, folder in (("00", SOURCES/"20261126-p2-5-cell00-decoded"),("01",PARSER)):
        oldspec=json.loads(checked(folder/"TYPED_PAYLOAD_MANIFEST.json"))
        for j,r in enumerate(oldspec["rational_candidates"]+oldspec["integer_candidates"]):
            key=(r["name"][:7],r["original_string"])
            owner="P2Saving16Cell"+cell+"ScalarDecode"+(f"Part{j//128:02}" if cell=="01" else "")
            theorem="ImbalancedChen.P2Saving16Cell"+cell+"ScalarDecode."+r["name"]+"_decoded"
            if "ImbalancedChen."+owner not in cache:
                raise ValueError("Missing accepted scalar owner "+owner)
            old_proofs.setdefault(key,(owner,theorem,r.get("lean_expression",r["original_string"])))
    rows=[];used=[]
    for kind,parser in (("rational","parseRational"),("integer","parseInteger")):
        for r in spec[kind+"_candidates"]:
            k=(r["name"][:7],r["original_string"]); donor=old_proofs.get(k)
            if donor and donor[2]!=names[r["name"]]:
                raise ValueError("Different scalar result for original spelling "+str(k))
            rows.append((r["name"],parser,r["original_string"],None))
            used.append(donor)
    blocks=[]
    for offset in range(0,len(rows),128):
        block=PREFIX+f"ScalarDecodePart{offset//128:02}"
        batch=rows[offset:offset+128]; refs=used[offset:offset+128]
        s=mod.scalar_block(batch)
        extra=sorted({r[0] for r in refs if r})
        s="".join("import ImbalancedChen."+owner+"\n" for owner in extra)+s
        for (name,parser,_,_),donor in zip(batch,refs,strict=True):
            if donor:
                start=s.index("theorem "+name+"_decoded :")
                a=s.index("  rw ["+parser+"_ofList]\n  rfl",start)
                s=s[:a]+"  exact "+donor[1]+s[a+len("  rw ["+parser+"_ofList]\n  rfl"):]
        put(block,s);blocks.append(block)
    put(PREFIX+"ScalarDecode","".join("import ImbalancedChen."+b+"\n" for b in blocks))
    simp=checked(SOURCES/"20261126-p2-5-cell00-field-split/ImbalancedChen/P2Saving16Cell00FieldSimp.lean").decode()
    put(PREFIX+"FieldSimp",mod.field_simp(rows,mod.nat_keys(typed)[0],simp))
    return {r[0]:d[1] for r,d in zip(rows,used,strict=True) if d}


def decode_sources(typed):
    fields=host_module(DECODE/"generate_fields.py")
    defs=fields.definitions(typed)
    base=template(DECODE,"FieldBase")
    a=base.index("theorem vertex23_decoded");b=base.index("theorem vertices_mapped",a)
    base=base[:a]+base[b:];put(PREFIX+"FieldBase",base)
    for i in range(21):
        tag=f"{i:02}"; original=template(DECODE,"Simplex"+tag+"Decode")
        fs=fields.row_fields(defs["rawSimplex"+tag])
        for key,value in fs:
            pattern=r'(rawSimplex'+tag+r'\.getObjVal\? '+re.escape(json.dumps(key))+r' = \.ok \()([^\n]*)(\) := by)'
            original,n=re.subn(pattern,lambda m:m[1]+value+m[3],original)
            if n!=1: raise ValueError((tag,key,n))
        put(PREFIX+"Simplex"+tag+"Decode",original)
    final=template(DECODE,"FieldDecode")
    final=re.sub(r'^import ImbalancedChen.P2Saving16Cell03Simplex(\d\d)Decode\n',
                 lambda m:m[0] if int(m[1])<21 else "",final,flags=re.M)
    final=re.sub(r' (vertex|simplex)(\d\d)_decoded\b',lambda m:m[0] if int(m[2])<(23 if m[1]=="vertex" else 21) else "",final)
    put(PREFIX+"FieldDecode",final)
    for suffix in ("Decoded","PayloadBinding","OriginalParse"):
        put(PREFIX+suffix,template(DECODE,suffix))


def arithmetic_sources(doc):
    rows=doc["simplices"]
    numerator=str(sum(int(r["jensen_floor_Q96"]) for r in rows))
    assert numerator=="41059550060734548977"
    floors=template(ARITH,"StoredFloors").replace(OLD_SUM,numerator)
    floors=re.sub(r'^theorem simplex(\d\d)_stored_jensen_floor :\n[^\n]*\n\n',
                  lambda m:m[0] if int(m[1])<21 else "",floors,flags=re.M)
    floors=re.sub(r'^  · exact simplex(\d\d)_stored_jensen_floor\n',
                  lambda m:m[0] if int(m[1])<21 else "",floors,flags=re.M)
    floors=re.sub(r'\b81\b',"21",floors)
    floors=floors.replace("active8.size = 495","active8.size = 165").replace("vertices.size = 35","vertices.size = 23")
    assert re.findall(r'^theorem simplex(\d\d)_stored_jensen_floor',floors,re.M)==[f"{i:02}" for i in range(21)]
    put(PREFIX+"StoredFloors",floors)
    for i in range(21):
        name=f"Row{i:02}Arithmetic"
        s=template(ARITH,name)
        assert s.count(f"({i} : Fin 81)")==3
        put(PREFIX+name,s.replace(f"({i} : Fin 81)",f"({i} : Fin 21)"))
    total=template(ARITH,"AllRowsArithmetic").replace(OLD_SUM,numerator)
    total=re.sub(r'^(?:import ImbalancedChen\.|  · exact )P2Saving16Cell03Row(\d\d)Arithmetic(?:\.simplex_valid)?\n',
                 lambda m:m[0] if int(m[1])<21 else "",total,flags=re.M)
    total=re.sub(r'\b81\b',"21",total)
    put(PREFIX+"AllRowsArithmetic",total)
    put(PREFIX+"OriginalArithmetic",template(ARITH,"OriginalArithmetic").replace("81 typed rows","21 typed rows").replace(OLD_SUM,numerator))
    for name in ("TypedSourceFacts","OriginalSourceFacts"):
        s=template(FACTS,name).replace("0 < 81","0 < 21").replace("twelve saved",str(len(doc["facet_original_indices"]))+" saved")
        put(PREFIX+name,s)
    return numerator


def selections(cache,doc):
    todo={Path(key).stem:content for key,content in outputs.items() if key.endswith(".lean")}
    ordered=[];done=set();old={}
    while todo:
        progress=False
        for name,content in list(todo.items()):
            imports=re.findall(r'^import ImbalancedChen\.(\w+)\s*$',content.decode(),re.M)
            if any(k in todo for k in imports):
                continue
            for dep in imports:
                if dep not in done:
                    m="ImbalancedChen."+dep
                    if m not in cache: raise ValueError("Unaccepted/nonlocal import "+m)
                    old[m]=cache[m]
            ordered.append({"module":"ImbalancedChen."+name,"path":"ImbalancedChen/"+name+".lean",
                            "bytes":len(content),"sha256":sha(content),"direct_project_imports":["ImbalancedChen."+k for k in imports]})
            done.add(name);del todo[name];progress=True
        if not progress: raise ValueError("Cyclic generated modules")
    assert len(ordered)==63
    return ordered,old


def generate(path):
    cache=json.loads(checked(CACHE))["project_objects"]
    assert len(cache)==246
    assert not any("P2Saving16Cell03" in n or "P2Saving16CanonicalCell03" in n for n in cache)
    data,tree,ns,doc,typed,spec,counts=read_original(path)
    parser_sources(data,tree,ns)
    reused=scalar_sources(spec,typed,cache);decode_sources(typed)
    numerator=arithmetic_sources(doc); order,old=selections(cache,doc)
    assert len(spec["rational_candidates"])==464 and len(spec["integer_candidates"])==42
    for k in range(21):
        r=doc["simplices"][k]
        assert r["simplex_id"]==k and len(r["vertex_ids"])==9 and len(r["factor_maxima"])==len(r["gap_weighted_means"])==10
    dump("LITERALS.json",spec)
    dump("MANIFEST.json",{
        "status":"SOURCE_ONLY_UNCOMPILED","new_accepted_owners":0,"P2_5_proved":False,
        "canonical_archive_index":3,"original_source_id":3,
        "original_file":{"name":"eighth-prefix-family-20261009-cell-03.witness.json","bytes":len(data),"sha256":sha(data),
                         "codepoints":len(data.decode("ascii")),"ascii":True,"multibyte_codepoints":0,"trailing_bytes":list(data[tree.end:])},
        "input_chain":["originalText (3 : Fin 14) loaded from the unchanged original input owner",
                       "canonicalSaving16Chars% (3 : Fin 14); String.ofList chars03 = originalText (3 : Fin 14)",
                       "original SourceJson.value on exactly chars03; successful original SourceJson.parse",
                       "rootValue = rawRoot; decodeCell rawRoot = .ok cell03Payload",
                       "parsedCell (3 : Fin 14) = .ok decodedCell03; archive (3 : Fin 14) = decodedCell03"],
        "source_json_fuel":tree.need,"value_end":tree.end,"original_length_plus_one_fuel":len(data)+1,
        "raw_field_count":len(spec["raw_fields"]),"simplex_raw_field_count":10,"simplex_lookup_count":210,
        "measured":{"vertex_count":23,"simplex_count":21,"active8_count":165,"facet_count":len(doc["facet_original_indices"]),**counts},
        "stored_individual_floors":[str(r["jensen_floor_Q96"]) for r in doc["simplices"]],"host_sum_of_individual_floors":numerator,
        "original_row_vertex_indices":[r["vertex_ids"] for r in doc["simplices"]],
        "manuscript":json.loads(checked(ARITH/"MANIFEST.json"))["manuscript_formula_provenance"],
        "simplex_valid_in_original_order":[
            ["row.simplexId = s.val","row_shape.1"],["row.vertexIds.size = 9","row_shape.2.1"],
            ["all nine vertex indices are in the payload vertex array","row_shape.2.2.1"],
            ["0 < physicalVolumeQ vertices","physical_volume_pos"],["0 < gapTotalQ vertices","gap_total_pos"],
            ["row.physicalVolume = physicalVolumeQ vertices","volume_eq"],["row.meanGap = gapTotalQ vertices / 9","mean_gap_eq"],
            ["row.gapWeightedMeans.size = 10","row_shape.2.2.2"],["all ten stored gap-weighted means = meansQ vertices","ten_means_eq"],
            ["row.jensenBound = jensenQ vertices","jensen_eq"],["row.jensenFloor = q96Floor (jensenQ vertices)","jensen_floor_eq"]],
        "existing_scalar_theorems_reused":reused,"new_scalar_reductions":506-len(reused),
        "full_existing_object_checkpoint":{"path":str(CACHE.relative_to(REPO)),"sha256":sha(checked(CACHE)),"objects":246},
        "direct_external_project_suppliers":old,"local_topological_order":order,
        "literal_index_sha256":sha(outputs["LITERALS.json"]),"generator_sha256":sha(Path(__file__).read_bytes()),
        "typed_literal_renderer_sha256":sha((HERE/"typed_literals.py").read_bytes()),"input_pin_file_sha256":sha((HERE/"INPUT_PINS.json").read_bytes()),
        "acceptance_gates":["strict NORMAL","stock leanchecker replay","complete owned-declaration audit"]})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input",type=Path,required=True)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    pins.update(json.loads((HERE/"INPUT_PINS.json").read_text()))
    for p in pins:
        checked(REPO/p)
    generate(args.input)
    # Check the whole write set before creating any missing outputs.
    for name,data in outputs.items():
        destination=HERE/name
        if destination.exists() and destination.read_bytes()!=data: raise ValueError("Output differs: "+name)
        if args.check and not destination.is_file(): raise ValueError("Missing output: "+name)
    if not args.check:
        for name,data in outputs.items():
            destination=HERE/name
            if not destination.exists():
                destination.parent.mkdir(parents=True,exist_ok=True)
                with destination.open("xb") as f:f.write(data)
    print(f"{len([n for n in outputs if n.endswith('.lean')])} Lean source candidates; no Lean executions")


if __name__=="__main__":
    main()
