#!/usr/bin/env python3
"""Owned static/source/artifact/log gates. Never fetch or execute Lean or foreign code."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PLAN = json.loads((HERE / 'owned-closure.json').read_text())
OLD_HERE = HERE.parent / 'chen_quotient_bv'
if hashlib.sha256((OLD_HERE / 'owned-closure.json').read_bytes()).hexdigest() != PLAN['inheritedManifestSha256']:
    raise SystemExit('Inherited manifest changed before loading its audit gate')
if hashlib.sha256((OLD_HERE / 'consumer_audit.py').read_bytes()).hexdigest() != PLAN['inheritedAuditGateSha256']:
    raise SystemExit('Inherited gate changed before loading it')
spec = importlib.util.spec_from_file_location('reviewed_quotient_gate', OLD_HERE / 'consumer_audit.py')
OLD = importlib.util.module_from_spec(spec)
spec.loader.exec_module(OLD)
FOREIGN = OLD.FOREIGN
need, sha256, blob, write = OLD.need, OLD.sha256, OLD.blob, OLD.write
regular, imports, scrub, compiled_set = OLD.regular, OLD.imports, OLD.scrub, OLD.compiled_set
ALLOWED_AXIOMS, TRUSTED_PREFIXES = OLD.ALLOWED_AXIOMS, OLD.TRUSTED_PREFIXES


def targets():
    result = OLD.replay_targets() + PLAN['newBuildOrder']
    need(len(result) == len(set(result)) == PLAN['replayModuleCount'] == 333, 'Wrong full replay target count')
    need(result[:327] == PLAN['baselineReplayTargets'] == OLD.PLAN['replayTargets'], 'Original 327-target prefix changed')
    need(result == PLAN['replayTargets'], 'Full replay target list differs')
    return result


def source_gate(consumer):
    need(sha256(OLD_HERE / 'owned-closure.json') == PLAN['inheritedManifestSha256'], 'Inherited manifest changed')
    need(sha256(OLD_HERE / 'consumer_audit.py') == PLAN['inheritedAuditGateSha256'], 'Inherited gate changed')
    OLD.validate_sources(consumer)
    need(PLAN['sources'][:47] == OLD.PLAN['sources'], 'Inherited 47-source plan changed')
    need(PLAN['topologicalOrder'][:47] == OLD.PLAN['topologicalOrder'], 'Inherited compile order changed')
    need(len(PLAN['sources']) == PLAN['ownedBuildModuleCount'] == 53, 'Wrong owned compile count')
    need(len(PLAN['newBuildOrder']) == PLAN['newBuildModuleCount'] == 6, 'Wrong appended compile count')
    need(len(PLAN['auditedModules']) == len(set(PLAN['auditedModules'])) == 51, 'Wrong proof-origin count')
    license = consumer / PLAN['license']['source']; regular(license, consumer)
    need(sha256(license) == PLAN['license']['sha256'] and blob(license) == PLAN['license']['gitBlob'], 'Adjacent mass license changed')
    known = {r['module'] for r in PLAN['sources']}
    need(len(known) == len(PLAN['sources']), 'Duplicate source module')
    edges = {}
    for r in PLAN['sources']:
        for key in ['source', 'destination']:
            p = Path(r[key]); need(not p.is_absolute() and '..' not in p.parts, 'Unsafe source/destination path')
        p = consumer / r['source']; regular(p, consumer)
        need(sha256(p) == r['sha256'] and blob(p) == r['gitBlob'], 'Pinned source changed: '+r['module'])
        need(imports(p.read_text()) == r['imports'], 'Import edges changed: '+r['module'])
        if r['kind'] != 'audit-tool':
            need(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|debug\.skipKernelTC|#eval|\brun_cmd\b|\brun_elab\b|\binitialize\b|IO\.(?:Process|FS)', scrub(p.read_text())), 'Unreviewed proof escape/runtime token')
        edges[r['module']] = r['imports']
    proof = {r['module'] for r in PLAN['sources'] if r['kind'] != 'audit-tool'}
    need(proof == set(PLAN['auditedModules']), 'Incomplete proof-origin selection')
    need(set(OLD.PLAN['auditedModules']) <= proof, 'Dropped baseline proof origin')
    order = PLAN['topologicalOrder']; positions = {m:i for i,m in enumerate(order)}
    need(len(order) == len(set(order)) and set(order) == known, 'Invalid full build order')
    need(order[47:] == PLAN['newBuildOrder'], 'Appended order changed')
    visited, active, foreign_roots, boundary = set(), set(), set(), set()
    def visit(m):
        need(m not in active, 'Owned import cycle')
        if m in visited: return
        active.add(m)
        for dep in edges[m]:
            if dep in known:
                need(positions[dep] < positions[m], 'Build order violates import dependency')
                visit(dep)
            elif dep in FOREIGN['modules']: foreign_roots.add(dep)
            else:
                need(dep.startswith(('Mathlib.', 'Lean.', 'Init.', 'Std.')), 'Unapproved additional import: '+dep)
                boundary.add(dep)
        active.remove(m); visited.add(m)
    visit(PLAN['probeModule'])
    need(visited == known, 'Unused/missing selected source')
    need(foreign_roots == {FOREIGN['supplierModule']}, 'Changed foreign entry root')
    need(sorted(boundary) == PLAN['boundaryImports'], 'Changed trusted boundary')
    need(order[-2] == PLAN['rootModule'] and order[-1] == PLAN['probeModule'], 'Wrong actual mass root/probe order')
    need(PLAN['auditInstrumentationImports'] == ['ChenQuotientBVProbe'], 'Unexpected imported audit instrumentation')
    targets()


def stage(consumer, root, out):
    source_gate(consumer)
    for r in PLAN['sources'][:47]:
        p = root / r['destination']; regular(p, root)
        need(sha256(p) == r['sha256'], 'Missing/changed inherited staged source')
    for r in PLAN['sources'][47:]:
        p = root / r['destination']
        need(not p.exists() and not p.is_symlink(), 'Mass source stage collision')
        need(not any(q.is_symlink() for q in p.parents if q == root or root in q.parents), 'Symlink stage parent')
    for r in PLAN['sources'][47:]:
        p = root / r['destination']; p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(consumer / r['source'], p)
    out.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(HERE / 'owned-closure.json', out / 'mass-owned-closure.json')
    (out / 'mass-build-modules.txt').write_text('\n'.join(PLAN['newBuildOrder'])+'\n')
    print('STAGED_MASS_EXTENSION=6 ORIGINAL_OWNED=47 TOTAL_OWNED=53')


def axiom_gate(out):
    # Retain original 46-origin/named evidence in addition to the complete new 51-origin check.
    OLD.axiom_gate(out)
    log = (out / 'chen-quotient-mass-bv-build.log').read_text()
    need('sorryAx' not in log, 'sorryAx in mass audit output')
    loaded = re.findall(r'^MASS_BV_IMPORTED_MODULE (\S+)$', log, re.M)
    need(len(loaded) == len(set(loaded)), 'Duplicate loaded module')
    proof = set(PLAN['auditedModules'])
    foreign = set(FOREIGN['modules']) | {r['module'] for r in FOREIGN['architectModules']}
    custom = {m for m in loaded if m.split('.')[0] not in TRUSTED_PREFIXES}
    need(custom == proof | foreign | set(PLAN['auditInstrumentationImports']), 'Loaded custom graph not exactly 51 proof + old probe + 270+9 foreign')
    need(set(PLAN['requiredActualRoots']) <= set(loaded), 'Actual quotient/mass root missing from loaded environment')
    rows = re.findall(r'^MASS_BV_OWNED_MODULE_AUDIT (\S+) declarations=([1-9][0-9]*)$', log, re.M)
    need(len(rows) == len(proof) and {m for m,_ in rows} == proof, 'Missing/duplicate proof-origin coverage')
    counts = {m:int(n) for m,n in rows}
    passes = re.findall(r'^MASS_BV_OWNED_AXIOM_AUDIT_PASS declarations=([1-9][0-9]*) modules=51$', log, re.M)
    need(len(passes) == 1 and int(passes[0]) == sum(counts.values()), 'Missing/inconsistent full mass axiom success')
    named = {}
    for name in PLAN['namedAxiomReports']:
        hits = re.findall(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",log)
        empty = re.findall(r"'"+re.escape(name)+r"' does not depend on any axioms",log)
        need(len(hits)+len(empty) == 1, 'Missing/duplicate named mass axiom report: '+name)
        axioms = {v.strip() for v in hits[0].split(',') if v.strip()} if hits else set()
        need(axioms <= ALLOWED_AXIOMS, 'Forbidden named mass axiom: '+name)
        named[name] = sorted(axioms)
    write(out,'mass-loaded-imports.json',sorted(loaded))
    write(out,'mass-module-origin-axiom-audit.json',{'counts':counts,'total':sum(counts.values()),'named':named})


def after(consumer, root, out):
    source_gate(consumer)
    gate = json.loads((out / 'cold-gate.json').read_text())
    architect = {r['module'] for r in FOREIGN['architectModules']}
    main = root / '.lake/build/lib/lean'
    arch = root / '.lake/packages/LeanArchitect/.lake/build/lib/lean'
    expected = targets()
    need(compiled_set(main) == set(expected)-architect, 'Unexpected/missing root-project compiled module')
    need(compiled_set(arch) == architect, 'Unexpected/missing Architect compiled module')
    for r in PLAN['sources']:
        p = root / r['destination']; regular(p,root)
        need(sha256(p) == r['sha256'], 'Staged proof/instrumentation changed')
    artifacts = []
    for m in expected:
        directory = arch if m in architect else main
        p = directory / (m.replace('.','/')+'.olean'); regular(p,directory)
        need(p.stat().st_mtime_ns >= gate['time_ns'], 'Artifact predates cold gate: '+m)
        artifacts.append({'module':m,'sha256':sha256(p),'bytes':p.stat().st_size,'mtime_ns':p.stat().st_mtime_ns})
    axiom_gate(out)
    (out / 'replay-modules.txt').write_text('\n'.join(expected)+'\n')
    write(out,'mass-all-built-artifacts.json',artifacts)
    print('PASS: original 46-origin audit retained; all 51 proof origins; 333 exact fresh replay targets')


def replay_gate(out):
    expected = targets()
    need((out/'replay-modules.txt').read_text().splitlines() == expected, 'Changed exact target file')
    batches = [expected[i:i+12] for i in range(0,len(expected),12)]
    need((out/'replay-batches.txt').read_text().splitlines() == [' '.join(b) for b in batches], 'Missing/reordered/duplicate batch input')
    log=(out/'kernel-replay.log').read_text()
    starts=list(re.finditer(r'^MASS_REPLAY_BEGIN ([1-9][0-9]*) (.+)$',log,re.M))
    ends=list(re.finditer(r'^MASS_REPLAY_END ([1-9][0-9]*) exit=([0-9]+)$',log,re.M))
    need(len(starts)==len(ends)==len(batches)==28,'Incomplete/duplicate batch framing')
    explicit_all=set();records=[]
    for i,(start,end,batch) in enumerate(zip(starts,ends,batches),1):
        need(int(start[1])==int(end[1])==i and end[2]=='0','Bad batch number/exit')
        need(start[2].split()==batch,'Requested ordered batch differs')
        need(start.end()<end.start(),'Reversed markers')
        need(i==len(batches) or end.end()<starts[i].start(),'Overlapping batches')
        chunk=log[start.end():end.start()]
        need(re.findall(r'^\s*Command being timed: "(.+)"$',chunk,re.M)==['lake env leanchecker --verbose '+' '.join(batch)],'Changed/missing checker command')
        need(re.findall(r'^\s*Exit status: ([0-9]+)$',chunk,re.M)==['0'],'Changed/missing checker status')
        explicit=re.findall(r'^replaying (\S+)$',chunk,re.M)
        need(set(batch)<=set(explicit),'Requested root/module not explicitly replayed')
        need(set(explicit)<=set(expected),'Unexpected explicit replay')
        explicit_all.update(explicit);records.append({'index':i,'requested':batch,'explicit':explicit,'exit':0})
    need(explicit_all==set(expected),'Missing baseline or new replay target')
    outside=log
    for start,end in reversed(list(zip(starts,ends))):outside=outside[:start.start()]+outside[end.end():]
    need(not re.search(r'^replaying |Command being timed:|Exit status:|MASS_REPLAY_',outside,re.M),'Unframed replay evidence')
    write(out,'mass-verified-replay-batches.json',records)
    write(out,'mass-replay-verification.json',{'targets':333,'batches':28,'baseline327PrefixPreserved':True,'everyBatchExit0':True,'everyBatchCommandMatches':True,'allTargetsExplicitlyReplayed':True,'requiredActualRoots':PLAN['requiredActualRoots'],'fullLogSha256':sha256(out/'kernel-replay.log')})
    print('PASS: 333 exact ordered targets, original 327 retained, 28 complete successful replay batches')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('mode',choices=['sources','stage','after','replay'])
    p.add_argument('consumer',type=Path);p.add_argument('root',type=Path);p.add_argument('out',type=Path);a=p.parse_args()
    if a.mode=='sources':source_gate(a.consumer)
    elif a.mode=='replay':replay_gate(a.out)
    else:{'stage':stage,'after':after}[a.mode](a.consumer,a.root,a.out)
