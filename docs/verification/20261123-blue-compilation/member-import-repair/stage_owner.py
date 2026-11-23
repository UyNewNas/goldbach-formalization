from pathlib import Path
import hashlib,json,difflib,re,subprocess
R=Path('/workspace/blue-member-import-repair');M=Path('/workspace/blue-member-build');MAIN=Path('/workspace/goldbach-formalization');rows={}
configs=[('RenewalFiniteErrorPropagationP5','804709bc71b85ce677a585c1dbe6e9d90527eb40befad03f99214e7b6a0eeadd','import Mathlib.Data.Matrix.Notation','import Mathlib.Data.Fin.VecNotation','ba1b4b49b4c144003a37478880a0b4f0d8ac9bab','Source-only, uncompiled.'),('P2BuchstabRationalSemantics','9e8e3c73165fe0e0277201def97249b4ab229dfcf33aa834d2ee49a6f1cad95f','import Mathlib.Tactic.Omega','import Lean.Elab.Tactic.Omega',None,'SOURCE ONLY / UNCOMPILED / no Lean, lake, evaluator, or numerical replay.')]
def sha(b):return hashlib.sha256(b).hexdigest()
for short,pre,oldimport,newimport,published,label in configs:
 mod='ImbalancedChen.'+short;rel=mod.replace('.','/')+'.lean';p=M/rel;b=p.read_bytes();old=b.decode();assert sha(b)==pre and (MAIN/rel).read_bytes()==b;assert old.count(oldimport)==1;new=old.replace(oldimport,newimport);importonly=new
 if published:
  pb=subprocess.check_output(['git','show',published+':'+rel],cwd=MAIN);assert new.encode()==pb;published_info={'commit':published,'source_path':rel,'source_sha256':sha(pb),'git_blob':subprocess.check_output(['git','rev-parse',published+':'+rel],cwd=MAIN,text=True).strip(),'adopted_import_only_bytes_identical_to_published_source_before_neutral_status':True}
 else:published_info={'classification':'actual_pinned_builtin_supplier_import','builtin_source':'/workspace/toolchains/lean-4.33.0-rc1-linux/src/lean/Lean/Elab/Tactic/Omega.lean','builtin_olean':'/workspace/toolchains/lean-4.33.0-rc1-linux/lib/lean/Lean/Elab/Tactic/Omega.olean','builtin_source_sha256':sha(Path('/workspace/toolchains/lean-4.33.0-rc1-linux/src/lean/Lean/Elab/Tactic/Omega.lean').read_bytes()),'known_path_history_search':'git log --all -S import Lean.Elab.Tactic.Omega found no published same-file replacement'}
 new=new.replace(label,'Verification records: docs/verification/20261123-blue-compilation.')
 # The original distinction between semantic recurrence and absent concrete table remains untouched.
 if short=='P2BuchstabRationalSemantics':new=new.replace('The\nfinite checker and the proofs below have not been run.','Verification records for these proofs are listed in\ndocs/verification/20261123-blue-compilation.')
 prefix=old.index('namespace ');newprefix=new.index('namespace ');assert old[prefix:]==new[newprefix:]
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by)\b',new)
 for proc in Path('/proc').iterdir():
  if not proc.name.isdigit():continue
  try:a=[x for x in (proc/'cmdline').read_bytes().decode().split('\0') if x]
  except Exception:continue
  assert str(p) not in a,('active',proc.name)
 d=R/short;d.mkdir();(d/'baseline.lean').write_bytes(b);(d/'candidate.lean').write_bytes(new.encode());(d/'candidate.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='baseline/'+rel,tofile='candidate/'+rel)));post=sha(new.encode());record={'module':mod,'preimage_sha256':pre,'postimage_sha256':post,'old_import':oldimport,'new_import':newimport,'supplier_origin':published_info,'all_original_namespace_bytes_identical_including_every_header_definition_proof_numeric_constant_hypothesis':True,'root_authorized_scope':'two exact obsolete supplier imports plus neutral historical verification comments before canonical compile','main_Member_same_baseline_synced':True,'P6_frozen_archives_modified':False,'compiler_invoked':False};(d/'SOURCE_COMPARISON.json').write_text(json.dumps(record,indent=2)+'\n');p.write_bytes(new.encode());(MAIN/rel).write_bytes(new.encode());rows[mod]=record;print(mod,post)
(R/'SOURCE_SELECTION.json').write_text(json.dumps(rows,indent=2)+'\n');(R/'EXPECTED_SOURCES.json').write_text(json.dumps({m:v['postimage_sha256'] for m,v in rows.items()},indent=2)+'\n')
s=Path('/workspace/blue-member-repair-batch3/run_validation.py').read_text().replace('/workspace/blue-member-repair-batch3',str(R));(R/'run_validation.py').write_text(s)
audit=Path('/workspace/blue-member-repair-batch3/PublicAudit.lean').read_text();body=audit[audit.index('  let selected :='):];prefix='\n'.join('import '+m for m in rows)+'\nimport Lean\nset_option pp.all true\nset_option pp.universes true\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let moduleNames := env.header.moduleNames\n  let targets : Array Name := #['+', '.join('`'+m for m in rows)+']\n';(R/'PublicAudit.lean').write_text(prefix+body)
