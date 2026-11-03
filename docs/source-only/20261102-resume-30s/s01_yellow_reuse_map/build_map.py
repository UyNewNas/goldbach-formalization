import json, re, hashlib
from pathlib import Path
root = Path(r"E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation")
outdir = root / "docs/source-only/20261102-resume-30s/s01_yellow_reuse_map"
tracker = Path(r"E:\timot\Documents\FilesForGPT\Myath\1_+_1.748_lean_proofs\main.md")
text = tracker.read_text(encoding="utf-8-sig")
rows=[]
for ln,line in enumerate(text.splitlines(),1):
 m=re.match(r"^([\t ]*)(绿|蓝|黄)｜(.*)$",line)
 if m:
  indent=sum(4 if c=="\t" else 1 for c in m.group(1))
  rows.append({"line":ln,"indent":indent,"status":m.group(2),"text":m.group(3).strip()})
yellow=[]
for row in rows:
 if row["status"]=="黄": yellow.append({**row,"id":f"Y{len(yellow)+1:02d}"})
refs={
"Y01":["all22_actual_sources","fifth_old_defect","fifth_reserve64","full87_source_history","gamma_costs_units","gamma_grid_level","gamma_outer_theta","actual_causal_marks","actual_spectral_energy","actual_kuznetsov","oldform_continuous","uniform_seven32","actual_same_rho_pp","full_buffered_policy","catalog5_global_losses","actual_density_reserve","h430_full_member","h430_native_weights","h430_parent_theta_441","adopted_seed_count","full_modulus_test_support"],
"Y02":["fifth_old_defect","fifth_reserve64","full87_source_history"],"Y03":["full87_source_history","fifth_old_defect","fifth_reserve64"],"Y04":["full87_source_history"],"Y05":["full87_source_history"],"Y06":["fifth_old_defect","fifth_reserve64"],
"Y07":["all22_actual_sources","gamma_costs_units","gamma_grid_level","gamma_outer_theta","actual_causal_marks"],"Y08":["all22_actual_sources","full_buffered_policy"],"Y09":["all22_actual_sources"],"Y10":["all22_actual_sources"],"Y11":["full_buffered_policy"],"Y12":["all22_actual_sources"],"Y13":["all22_actual_sources"],
"Y14":["gamma_costs_units","gamma_grid_level","gamma_outer_theta"],"Y15":["gamma_costs_units","gamma_grid_level","gamma_outer_theta","actual_causal_marks","adopted_seed_count"],"Y16":["actual_causal_marks","adopted_seed_count","gamma_costs_units"],
"Y17":["actual_spectral_energy","actual_kuznetsov","oldform_continuous","uniform_seven32"],"Y18":["uniform_seven32"],"Y19":["actual_kuznetsov","oldform_continuous","actual_spectral_energy"],"Y20":["actual_same_rho_pp","gamma_outer_theta","gamma_grid_level","actual_kuznetsov"],"Y21":["actual_same_rho_pp","gamma_outer_theta","gamma_grid_level"],
"Y22":["full_buffered_policy","catalog5_global_losses","actual_density_reserve","all22_actual_sources","fifth_old_defect","fifth_reserve64"],"Y23":["all22_actual_sources","catalog5_global_losses","actual_density_reserve","full_buffered_policy"],"Y24":["all22_actual_sources","catalog5_global_losses","actual_density_reserve"],"Y25":["actual_density_reserve","actual_same_rho_pp","all22_actual_sources"],"Y26":["actual_same_rho_pp"],"Y27":["actual_same_rho_pp"],
"Y28":["h430_full_member","h430_native_weights","h430_parent_theta_441","adopted_seed_count"],"Y29":["h430_full_member","h430_native_weights","h430_parent_theta_441"],"Y30":["h430_full_member","h430_native_weights","h430_parent_theta_441"],"Y31":["h430_full_member","h430_native_weights","h430_parent_theta_441","adopted_seed_count"],"Y32":[],"Y33":[]}
parents={"Y01":None,"Y02":"Y01","Y03":"Y02","Y04":"Y03","Y05":"Y04","Y06":"Y03","Y07":"Y01","Y08":"Y07","Y09":"Y08","Y10":"Y08","Y11":"Y08","Y12":"Y07","Y13":"Y12","Y14":"Y07","Y15":"Y14","Y16":"Y15","Y17":"Y01","Y18":"Y17","Y19":"Y18","Y20":"Y17","Y21":"Y20","Y22":"Y01","Y23":"Y22","Y24":"Y23","Y25":"Y22","Y26":"Y01","Y27":"Y26","Y28":"Y01","Y29":"Y28","Y30":"Y29","Y31":"Y29","Y32":"Y01","Y33":"Y32"}
group_ids=sorted({g for gs in refs.values() for g in gs})
groups=[]
for gid in group_ids:
 base=Path("docs/source-only/20261102-resume-30r")/gid
 rp=root/base/"REGISTRY.json"; report=root/base/"REPORT.md"
 if not rp.exists(): continue
 reg=json.loads(rp.read_text(encoding="utf-8-sig"))
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 sources=[]
 for key in ("new_lean_sources","new_sources","source_repairs","reused_sources","new_files","new_actual_outputs","new_artifacts","new_lean_files","reused_and_inspected_sources"):
  for s in reg.get(key,[]) or []:
   if not isinstance(s,dict): continue
   sources.append({"registry_field":key,"path":s.get("path"),"sha256":s.get("raw_sha256") or s.get("sha256"),"module":s.get("intended_module"),"declarations":[{"kind":d.get("kind"),"name":d.get("name"),"line":d.get("line")} for d in s.get("declarations",[]) or [] if isinstance(d,dict)],"installed":s.get("installed"),"compiled":s.get("compiled",reg.get("compiled")),"kernel_verified":s.get("kernel_verified",reg.get("kernel_verified")),"formal_credit":s.get("formal_credit",reg.get("formal_credit")),"source_record":s})
 remaining={k:v for k,v in reg.items() if re.search(r"remaining|open_obligation|unresolved",k,re.I) and isinstance(v,(str,int,float,bool,list,dict))}
 groups.append({"id":gid,"registry_path":str(base/"REGISTRY.json"),"registry_sha256":sha(rp),"report_path":str(base/"REPORT.md") if report.exists() else None,"report_sha256":sha(report) if report.exists() else None,"task":reg.get("task"),"status":reg.get("status"),"compiled":reg.get("compiled"),"kernel_verified":reg.get("kernel_verified"),"formal_credit":reg.get("formal_credit"),"sources":sources,"registry_remaining_fields":remaining})
nodes=[]
for i,n in enumerate(yellow):
 stop=i+1
 while stop<len(yellow) and yellow[stop]["indent"]>n["indent"]: stop+=1
 descendants=[]
 for r in rows:
  if r["line"]<=n["line"] or r["indent"]<=n["indent"]: continue
  nxt=next((x for x in rows if x["line"]>n["line"] and x["indent"]<=n["indent"]),None)
  if nxt and r["line"]>=nxt["line"]: break
  descendants.append({"line":r["line"],"indent":r["indent"],"status":r["status"],"statement":r["text"]})
 nodes.append({"id":n["id"],"tracker_line":n["line"],"exact_tracker_terminal":n["text"],"yellow_parent":parents[n["id"]],"yellow_descendants":[yellow[j]["id"] for j in range(i+1,stop)],"listed_descendant_rows":descendants,"source_group_refs":refs[n["id"]],"closure_status":"OPEN_IN_AUTHORITATIVE_TRACKER","scope_complete":False,"mathematical_closure_judgment":"NOT_MADE"})
tracker_hash=hashlib.sha256(tracker.read_bytes()).hexdigest()
assert tracker_hash=="eda2afd45edaa3d00072bb677dd5eb3c9937c40d63ac23149ebbe3581cbeaca9",tracker_hash
obj={"schema_version":1,"task":"S/s01_yellow_reuse_map","tracker":{"path":str(tracker),"sha256":tracker_hash,"yellow_count":len(yellow)},"frozen_R":{"path":"docs/source-only/20261102-resume-30r","manifest_path":"E:/timot/Documents/FilesForGPT/Myath/output/r-batch-20261102/publication/payload/docs/source-only/20261102-resume-30r/SOURCE_MANIFEST.json","manifest_sha256":"cdfc42fe572d5ef5c006b6885f02a3960f3eb88433c032d3d136982744b37ab7"},"proof_evidence_search":{"searched":["production sources","all docs/source-only, including ignored files","hidden .lake/proof-continuation/source-reviews/drafts","local proof-continuation and workflow metadata"],"hidden_ignored_lean_file_count":114554,"hosted_query":{"repository":"subfish-zhou/goldbach-lean","commit":"e2a05f73d5f169fff847d72dcfcc66ec54ad4f87","workflow_runs":[],"combined_statuses":[]},"same_source_toolchain_kernel_artifact_found_for_new_R_sources":False,"qualification":"R registries mark their new source uncompiled/kernel_verified=false/formal_credit=0. Empty GitHub results are limited to the queried parent commit; no universal absence claim is made."},"source_groups":groups,"yellow_nodes":nodes}
out=outdir/"MAP.json"
out.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"yellow_count":len(yellow),"source_group_count":len(groups),"map_bytes":out.stat().st_size,"map_sha256":hashlib.sha256(out.read_bytes()).hexdigest()},ensure_ascii=False))





