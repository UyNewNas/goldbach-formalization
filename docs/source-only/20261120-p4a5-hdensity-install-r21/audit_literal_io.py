#!/usr/bin/env python3
"""Inventory selected textual IO indicators; this is not a Lean parser."""
import argparse,hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
R20=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r20';audit=json.loads((R20/'IMPORT_AUDIT.json').read_bytes());native=json.loads((R20/'NATIVE_SOURCE_VIEW.json').read_bytes())
ap=argparse.ArgumentParser();ap.add_argument('--lean',type=Path,required=True);ap.add_argument('--native-view',type=Path,required=True);args=ap.parse_args();lean=args.lean.resolve(strict=True);view=args.native_view.resolve(strict=True)
pat=re.compile(r'\b(?:readFile|readBinFile|readBin|readText|include_str|include_bytes|includeStr|includeBytes|openBinFile|openFile|IO\.Process|run_tac|include_original\w*)\b|\bIO\.FS\.')
rows=[]
def scan(kind,mod,path,sha):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,(mod,path);hits=[{'line':n,'text':line.strip()} for n,line in enumerate(b.decode('utf-8-sig').splitlines(),1) if pat.search(line)]
 if hits:rows.append({'kind':kind,'module':mod,'sha256':sha,'hits':hits})
for mod,x in sorted(audit['visited'].items()):scan('project',mod,lean/x['path'],x['sha256'])
for x in native['files']:scan('native_research_view',x['module'],view/x['view_path'],x['sha256'])
print(json.dumps({'scope':'literal keyword lines only; comments and strings not lexed, dynamic IO/other syntax may be missed; no execution','project_files':len(audit['visited']),'native_view_files':len(native['files']),'matched_modules':len(rows),'rows':rows},indent=2,ensure_ascii=False))
