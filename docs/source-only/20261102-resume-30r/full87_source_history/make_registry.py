"""Write metadata only. No proof, finite guard, or numerical evaluator runs."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parent
R=H.parents[3]
def pin(p):
    p=Path(p)
    return dict(path=str(p.relative_to(R)).replace('\\','/') if p.is_relative_to(R) else str(p).replace('\\','/'),
      bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
audit=json.loads((H/'SOURCE_TEXT_AUDIT.json').read_text())
receipt=json.loads((H/'SOURCE_RECEIPT.json').read_text())
reuseNames={'P4AOriginalAscendingFourteenAffineSource','P4AOriginalFirstFailureH5H7Literal','P4AOriginalSeed7Unequal15Literal'}
for f in audit['files']:
    f['kind']='exact-source-materialization-reuse' if f['module'].split('.')[-1] in reuseNames else 'new-source-deduction'
    f['intended_install_path']=f['module'].replace('.','/')+'.lean'
reused=[
 ('ImbalancedChen/OriginalDescendingFifteenExportOwnershipJoin.lean',['strictExportedRows_iff_StrictRows']),
 ('ImbalancedChen/OriginalDescendingFifteenLiteralAffineRows.lean',['StrictExportedRows','exportedCoefficients']),
 ('ImbalancedChen/OriginalDescendingFifteenCellOwnership.lean',['StrictRows','leftMasks','maskSlots','subsetSum','branchPlane']),
 ('ImbalancedChen/OriginalAscendingThirteenExportOwnershipJoin.lean',['strictExportedRows_iff_StrictRows']),
 ('ImbalancedChen/OriginalAscendingThirteenLiteralAffineRows.lean',['StrictExportedRows','exportedCoefficients']),
 ('ImbalancedChen/OriginalAscendingThirteenCellOwnership.lean',['StrictRows','rows_physical','maskSlots','subsetSum','branchPlane']),
 ('ImbalancedChen/P2OriginalDescendingEighthLogSemantics.lean',['selected129_license','oldRaw','newCap']),
 ('ImbalancedChen/P2OriginalThirdMinorantLogDictionary.lean',['thirdMinorant_le_actual_cap']),
 ('docs/source-only/20261102-resume-30p/adopted87_policy/P4AOriginalFirstFailureH3SourceSemantics.lean',
  ['sourceAffineGuard_iff_StrictH3','source_selected_license','source_full_and_selected_squares']),
 ('docs/source-only/20261102-resume-30p/adopted87_policy/P4AOriginalFirstFailureH3Literal.lean',['sourceAffineGuard','StrictH3','oldSubsetSum','oldPlane','W']),
 ('ImbalancedChen/ActualExtendedThirdIdealCap.lean',['actualExtendedThirdIdealCap','actualExtendedThirdIdealCap_eq']),
 ('ImbalancedChen/VariableEnvelope.lean',['original_eq_six','v_eq_min','v_eq_A','v_eq_C','v_le_cap']),
 ('ImbalancedChen/SelectedPrefixBoxCap.lean',['prefixSquareExpr_actual_gate','selectedSquareExpr_actual_gate']),
 ('ImbalancedChen/FinitePrimeGeometryCore.lean',['primeHistoryLogCoordinates_ancestor','rosserAncestor']),
 ('ImbalancedChen/PrimeHistoryLogCoordinates.lean',['primeHistoryLogCoordinates_frontier']),
 ('docs/source-only/20261102-resume-30p/adopted87_policy/REPORT.md',[]),
 ('docs/source-only/20261102-resume-30p/adopted87_policy/REGISTRY.json',[]),
 ('docs/source-only/20261102-resume-30q/reviews/q23_review_data_trace.md',[]),
 ('docs/source-only/20261102-resume-30q/reviews/q24_review_saving_geometry.md',[]),
 ('docs/source-only/20261102-resume-30q/reviews/q30_review_history_final.md',[])]
rs=[]
for name,decls in reused:
    p=R/name;t=p.read_text(encoding='utf-8-sig')
    out=pin(p);out['used_declarations']=[]
    for d in decls:
        m=re.search(r'^(?:private\s+)?(?:theorem|def|abbrev|structure)\s+'+re.escape(d)+r'\b',t,re.M)
        out['used_declarations'].append(dict(name=d,line=t.count('\n',0,m.start())+1 if m else None))
    rs.append(out)
obj=dict(task='R03',plan_item='D01',status='SOURCE_ONLY_NARROW_SUPPLIERS_COMPLETE_FULL_ACTUAL_PARENT_OPEN',
  compiled=False,kernel_verified=False,formal_credit=0,finite_proofs='UNEVALUATED',
  source_scope=dict(newly_bridged_cells=47,reused_non_H3_cells=28,reused_H3_cells=12,total_cells=87,
    remaining75='47 new + existing descending15 + existing ascending13',
    actual_current_parent_supplied=False,final_physical_rho_supplied=False),
  files=audit['files'],reused_sources=rs,original_provenance=receipt['sources'],
  manuscript_sources=[pin(R.parent/'chen-imbalanced-semiprimes/paper/source/manuscript-body.tex'),
    pin(R.parent/'chen-imbalanced-semiprimes/paper/source/modules/global-positive-upper-completion-20261010.txt')],
  manuscript_lines=['280-297','371-375','435-449','453-509'],
  eliminated_premises=[
    'Independent selected licence/full-square/selected-complement/physical-ceiling inputs on the 47 original source cells.',
    'Independent ideal-third minorant, four odd-history and ideal-third conservative-upper inputs on those 47 cells.',
    'Redundant H5/H7 priority, H7<B3 and R6<M conjuncts of the original literal guards.',
    'Caller coordinate-domination premise for source squares on an actual prime frontier.',
    'Independent 87-domain source-to-square and source-to-ideal-history assembly (the 40 existing dictionaries are reused).',
    'Independent all87 old-tent upper bounds and gated/clipped ideal-third upper comparison; the own-third ancestor binding holds for both upper and history bounds.'],
  remaining_premises=[
    'Membership in the entire exact original strict affine source domain.',
    'For own-prefix conversion: original reverse history has length8.',
    'For arithmetic-frontier conversion: N>1 and membership in the existing actual rough-prime frontier.',
    'For the unchanged H5/H7 actual guards: rank8, H7<lambda6(ancestor6), lambda6(ancestor6)<=R6.'],
  remaining_open=[
    'Complete original fourth/fifth/sixth/current-parent construction and all87 real parent bounds.',
    'All87 source-owner/stage identification with the actual common policy and necessary semantic separations.',
    'Inherited, short-word, and full descendant support for every nonzero term of the final physical rho.',
    'Full buffered realization, All22 source integration, two independent reserves, density and same-rho PP.'],
  difficulty=dict(class1='Uncompiled Lean/API and finite symbolic proof resource uncertainty.',
    class2='Actual omitted source-row/ideal-prefix deductions supplied as proof source.',
    class3='No substantive manuscript contradiction or counterexample established.'),
  validation=dict(mode='source text and metadata only',source_row_string_checks=audit['source_string_checks'],
    lean_run=False,lake_run=False,compiler_run=False,finite_guard_evaluated=False,numerical_replay=False,
    producer_run=False,git_operation=False,child_agents=False,production_or_old_source_modified=False),
  broad_nodes={k:'OPEN' for k in ['P1.4.history','P1.4.gates','P1.4.integral','P3.6.same_rho_PP','P4A.4.actual_all22','D01.actual_current_parent']},
  artifacts=[pin(H/n) for n in ['REPORT.md','SOURCE_RECEIPT.json','SOURCE_TEXT_AUDIT.json','ROW_SELECTORS.txt',
    'materialize_source.py','write_semantics.py','audit_source_text.py','make_registry.py']],
  install_note='No install performed. Use listed literal-source materializations before the new semantic modules; use the pinned P H3 modules. External Mathlib source/API and all elaboration remain unchecked.')
(H/'REGISTRY.json').write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(obj['files']),report_sha256=pin(H/'REPORT.md')['sha256'],registry_sha256=pin(H/'REGISTRY.json')['sha256'])))
