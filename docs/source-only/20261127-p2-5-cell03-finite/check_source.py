"""Independent host-only checks on the quoted input, all 21 rows and the import selection."""
import argparse
import ast
import hashlib
import json
import math
import re
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
LEAN = ROOT / "ImbalancedChen"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical_node(obj):
    """Re-quote ordered json.loads output independently of the raw planner."""
    if isinstance(obj, dict):
        pairs = ["(String.ofList "+repr(list(k))+", "+canonical_node(v)+")" for k,v in obj.items()]
        return ".obj ["+", ".join(pairs)+"]"
    if isinstance(obj,list):
        return ".arr ["+", ".join(map(canonical_node,obj))+"]"
    if type(obj) is bool:
        return ".boolean "+str(obj).lower()
    if obj is None:
        return ".null"
    kind = "number" if type(obj) is int else "str"
    assert type(obj) in (int,str)
    return "."+kind+" (String.ofList "+repr(list(str(obj)))+")"


def determinants(points):
    edges=[[p[j]-points[0][j] for j in range(8)] for p in points[1:]]
    det=Q(1)
    for i in range(8):
        pivot=next(j for j in range(i,8) if edges[j][i])
        if pivot!=i:
            edges[i],edges[pivot]=edges[pivot],edges[i]
            det=-det
        d=edges[i][i];det*=d
        for j in range(i+1,8):
            r=edges[j][i]/d
            for k in range(i+1,8):
                edges[j][k]-=r*edges[i][k]
    return abs(det)/math.factorial(8)


def verify_rows(doc):
    vertices=[list(map(Q,v)) for v in doc["vertices"]]
    floors=[];jensens=[]
    for i,row in enumerate(doc["simplices"]):
        ids=row["vertex_ids"]
        assert row["simplex_id"]==i and len(ids)==9 and all(0<=k<len(vertices) for k in ids)
        pts=[vertices[k] for k in ids]
        volume=determinants(pts)
        gaps=[];factors=[]
        for p in pts:
            old=Q(57,64)-Q(3,2)*(p[1]+p[2])
            cap=(1+p[0]+p[7])/2-Q(1,1000000)
            gaps.append(cap-old)
            factors.append([old-sum(p),cap-sum(p),*p])
        total=sum(gaps)
        means=[(sum(f[j] for f in factors)+sum(g*f[j] for g,f in zip(gaps,factors,strict=True))/total)/10 for j in range(10)]
        jensen=4*volume*(total/9)/math.prod(means)
        floor=math.floor(jensen*2**96)
        assert volume>0 and total>0 and Q(row["physical_volume"])==volume and Q(row["mean_gap"])==total/9
        assert len(row["gap_weighted_means"])==10 and list(map(Q,row["gap_weighted_means"]))==means
        assert Q(row["jensen_bound"])==jensen and int(row["jensen_floor_Q96"])==floor
        floors.append(floor);jensens.append(jensen)
    return floors,math.floor(sum(jensens)*2**96)


def check(path):
    raw=path.read_bytes();doc=json.loads(raw)
    m=json.loads((ROOT/"MANIFEST.json").read_bytes())
    assert digest(raw)==m["original_file"]["sha256"] and len(raw)==m["original_file"]["bytes"]==125188
    text=(LEAN/"P2Saving16Cell03DirectParse.lean").read_text()
    expression=text.split("def rootValue : SourceJson :=\n  ",1)[1].split("\n\ntheorem ",1)[0]
    assert expression==canonical_node(doc)
    code=(LEAN/"P2Saving16Cell03TypedPayload.lean").read_text()
    typed=dict(re.findall(r'^def (\w+) : [^\n]+ :=\n  ([^\n]+)',code,re.M))
    for i,v in enumerate(doc["vertices"]):
        assert typed[f"rawVertex{i:02}"]==canonical_node(v)
    spec=json.loads((ROOT/"LITERALS.json").read_bytes())
    for r in spec["rational_candidates"]+spec["integer_candidates"]:
        for loc in r["locations"]:
            x=doc
            for p in loc.lstrip("/").split("/"):
                x=x[int(p)] if isinstance(x,list) else x[p]
            assert x==r["original_string"]
        assert "".join(ast.literal_eval(typed[r["chars_name"]]))==r["original_string"]
        assert typed[r["name"]]==r.get("lean_expression",r["original_string"])
    exprs = {m[1]:m[2].strip() for m in re.finditer(
        r'^def (\w+) : [^\n]+ :=\n  (.*?)(?=\n\ndef |\n\nend\b)',code,re.S|re.M)}
    scalars = {r["name"]:r["original_string"] for r in spec["rational_candidates"]+spec["integer_candidates"]}
    def project(expr):
        if expr.startswith("#["):
            return [project(x.strip()) for x in expr[2:-1].split(",")]
        return scalars[expr] if expr in scalars else int(expr)
    suffixes = ["Dimension","PhysicalJacobian","CellId","LeftMasks","RightMasks","FacetOriginalIndices",
                "PositiveNormalBalance","NormalRank","Active8","Vertices","VertexValues","AllOriginalMinima",
                "FacetVertices","FaceLedger","Simplices","PhysicalVolume","IntegralGap"]
    expected_fields=[]
    for (key,value),suffix in zip(doc.items(),suffixes,strict=True):
        real="raw"+suffix
        expected_fields.append("(String.ofList "+repr(list(key))+", "+real+")")
        if key in ("vertices","simplices"):
            child="rawVertex" if key=="vertices" else "rawSimplex"
            assert exprs[real+"Items"]=="["+", ".join(child+f"{k:02}" for k in range(len(value)))+"]"
            assert exprs[real]==".arr "+real+"Items"
        elif key in ("active8_enumeration","vertex_values","face_ledger"):
            assert exprs[real+"Items"]=="["+", ".join(map(canonical_node,value))+"]"
            assert exprs[real]==".arr "+real+"Items"
        else:
            assert exprs[real]==canonical_node(value)
    assert exprs["rawFields"]=="[\n    "+",\n    ".join(expected_fields)+"\n  ]" and exprs["rawRoot"]==".obj rawFields"
    assert exprs["vertices"]=="#["+", ".join(f"vertex{k:02}" for k in range(23))+"]"
    assert exprs["simplices"]=="#["+", ".join(f"simplex{k:02}" for k in range(21))+"]"
    for k,vertex in enumerate(doc["vertices"]):
        assert project(exprs[f"vertex{k:02}"])==vertex
    for k,row in enumerate(doc["simplices"]):
        fields=dict(re.findall(r"^    (\w+) := (.+)$",exprs[f"simplex{k:02}"],re.M))
        lean_keys=("simplexId","vertexIds","physicalVolume","meanGap","factorMaxima","gapWeightedMeans",
                   "maxBound","jensenBound","maxFloor","jensenFloor")
        assert [project(fields[name]) for name in lean_keys]==list(row.values())
    for key in ("cell_id","dimension","physical_jacobian","left_masks","right_masks","facet_original_indices",
                "positive_normal_balance","normal_rank","all_original_constraint_minima","physical_volume","integral_gap"):
        suffix=suffixes[list(doc).index(key)]
        name=suffix[0].lower()+suffix[1:]
        assert project(exprs[name])==doc[key]
    assert exprs["facetVertices"]==str(doc["facet_vertices"]).replace("[","#[")
    for name,raw_name in (("active8","rawActive8Items"),("faceLedger","rawFaceLedgerItems"),("vertexValues","rawVertexValuesItems")):
        assert exprs[name]==raw_name+".toArray"
    typed_fields=dict(re.findall(r"^    (\w+) := (\w+)$",exprs["cell03Payload"],re.M))
    assert len(typed_fields)==17 and all(expected==actual for expected,actual in typed_fields.items())
    for field in spec["raw_fields"]:
        assert json.loads(raw[field["start"]:field["end"]])==doc[field["key"]]
    for i,r in enumerate(doc["simplices"]):
        n=f"{i:02}";assert typed["rawSimplex"+n]==canonical_node(r)
        out=(LEAN/f"P2Saving16Cell03Simplex{n}Decode.lean").read_text()
        lookups=re.findall(r'^    rawSimplex(\d\d)\.getObjVal\? "([^"]+)" = \.ok \((.*)\) := by$',out,re.M)
        assert lookups==[(n,k,canonical_node(v)) for k,v in r.items()]
        src=(LEAN/f"P2Saving16Cell03Row{n}Arithmetic.lean").read_text()
        orig=REPO/f"docs/source-only/20261127-p2-5-cell01-arithmetic/ImbalancedChen/P2Saving16Cell01Row{n}Arithmetic.lean"
        assert src.replace("Cell03","Cell01").replace("cell03","cell01").replace(f"({i} : Fin 21)",f"({i} : Fin 81)")==orig.read_text()
    cache=json.loads((REPO/m["full_existing_object_checkpoint"]["path"]).read_bytes())["project_objects"]
    order=m["local_topological_order"];done=set(cache)
    for owner in order:
        p=ROOT/owner["path"]
        assert p.stat().st_size==owner["bytes"] and digest(p.read_bytes())==owner["sha256"]
        assert owner["module"] not in done and all(dep in done for dep in owner["direct_project_imports"])
        done.add(owner["module"])
    assert len(order)==len(list(LEAN.glob("*.lean")))==63
    floors,floor_after_sum=verify_rows(doc)
    assert sum(floors)==int(m["host_sum_of_individual_floors"]) and list(map(str,floors))==m["stored_individual_floors"]
    print(json.dumps({"status":"HOST_ONLY_NO_FORMAL_CREDIT","exact_complete_parser_ast":True,
        "typed_raw_and_typed_records_verified":True,"typed_raw_vertices_and_rows":[23,21],"ordered_row_lookups":210,"all_scalar_locations_matched":True,
        "eleven_conjuncts_checked_by_exact_host_arithmetic_for_rows":len(floors),"separate_floor_sum":str(sum(floors)),
        "floor_after_sum_for_contrast":str(floor_after_sum),"topological_new_owners":len(order),
        "external_project_imports_in_accepted_checkpoint":len(m["direct_external_project_suppliers"]),
        "lean_invocations":0},indent=2))
if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input",type=Path,required=True)
    check(parser.parse_args().input)
