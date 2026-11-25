"""Check transferred archive bytes and archived P1.5 receipt links offline."""
import argparse, hashlib, io, json, lzma, re, subprocess, tarfile
from pathlib import Path, PurePosixPath as P

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def check(archive, summary, repo=None):
    compressed = archive.read_bytes()
    assert (len(compressed), digest(compressed)) == (summary['bytes'], summary['sha256'])
    raw = lzma.decompress(compressed)
    assert digest(raw) == summary['uncompressed_tar_sha256']
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:') as tar:
        members = tar.getmembers()
        names = {m.name for m in members}
        assert len(names) == len(members) and all(m.isfile() for m in members)
        assert all(not P(n).is_absolute() and '..' not in P(n).parts and str(P(n)) == n for n in names)
        read = lambda n: tar.extractfile(str(n)).read()
        js = lambda n: json.loads(read(n))
        index_bytes = read('ARCHIVE_FILES.json')
        assert digest(index_bytes) == summary['index_sha256']
        index = json.loads(index_bytes); actual = index['actual_result']
        assert actual == summary['actual_result']
        rows = {r['path']:r for r in index['files']}
        assert len(rows) == len(index['files']) == summary['payload_files']
        assert set(rows) | {'ARCHIVE_FILES.json'} == names and 'ARCHIVE_FILES.json' not in rows
        for path, row in rows.items():
            payload=read(path)
            assert (len(payload),digest(payload)) == (row['bytes'],row['sha256']),path
        result = {'archive_sha256':summary['sha256'],'tar_sha256':digest(raw),'index_sha256':digest(index_bytes),
                  'all_indexed_payloads_verified':len(rows)}
        if repo is None:
            return result
        import sys
        sys.dont_write_bytecode = True
        sys.path.insert(0,str(repo / 'docs/p1/20261125/p15-actual-means'))
        import run_selected as runner
        def member(path): return P(path).relative_to('/workspace')
        def bound(ref):
            key=str(member(ref['path']))
            assert (rows[key]['bytes'],rows[key]['sha256']) == (ref['bytes'],ref['sha256'])
            return js(key)
        report=js(actual['review_path']); after=report['context_after']
        assert digest(read(actual['review_path'])) == actual['review_sha256']
        assert report['all_23_accepted'] is True and report['context_and_inventory_stable']
        assert len(report['owners']) == actual['accepted_owners'] == 23
        assert set(report['owners']) == set(actual['accepted_modules']) == set(runner.TARGETS)
        assert actual['source_commit'] == report['current_source_commit'] and not report['failures']
        assert report['context_before'] == after and report['git_before'] == report['git_after']
        assert not report['whole_P1_complete'] and not report['compilation_performed']
        for m, sha in {**after['project_sources'], **after['protected_roots']}.items():
            path=m.replace('.','/') + '.lean'
            assert rows['blue-member-build/'+path]['sha256'] == sha
            assert digest(subprocess.check_output(['git','show',actual['source_commit']+':'+path],cwd=repo)) == sha
        assert len(after['project_sources']) == 304
        for p,b in [*((P('blue-member-build')/k,v) for k,v in after['configuration'].items()),
                    *((member(k),v) for k,v in after['runtime'].items())]:
            assert {k:rows[str(p)][k] for k in ('bytes','sha256')} == b
        owned, public = 0, 0
        for m, row in report['owners'].items():
            refs=row['receipts']; normal=bound(refs['normal']); plan=bound(refs['audit_plan']); audit=bound(refs['audit_result'])
            receipt_root=member(str(runner.ROOT)) / row['original_source_commit'] / m
            assert all(member(ref['path']).is_relative_to(receipt_root) for ref in refs.values())
            assert normal['module'] == m and normal['source_commit'] == plan['source_review_head'] == row['original_source_commit']
            assert normal['status'] == 'NORMAL_PASS_AUDIT_PENDING' and audit['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
            assert audit['modules'] == {m:after['project_sources'][m]} and row['source_sha256'] == after['project_sources'][m]
            assert normal['dependency_context']['project_sources'] == audit['project_dependency_sources'] == plan['expected_project_sources']
            assert all(after['project_sources'][n] == h for n,h in audit['project_dependency_sources'].items())
            assert normal['source_plus_five_outputs'] == audit['source_plus_five_outputs'][m]
            assert audit['plan_sha256'] == refs['audit_plan']['sha256']
            cmd=normal['normal_command']; command_file=member(cmd['command_receipt'])
            assert digest(read(command_file)) == cmd['command_sha256'] and cmd['exit_code']==0
            assert all(cmd[k] == v for k,v in js(command_file).items())
            assert digest(read(member(cmd['log']))) == cmd['log_sha256'] and cmd['actual_built_modules'] == [m]
            lane=member(refs['audit_result']['path']).parent
            for command in [audit['stock_readiness_before'],audit['kernel_commands'][m],audit['audit_command'],audit['stock_readiness_after']]:
                path=lane/command['log']
                assert command['exit_code'] == 0 and digest(read(path)) == command['log_sha256']
                assert js(path.with_name(path.stem+'-command.json')) == command
            assert audit['kernel_commands'][m]['argv'][-3:] == ['leanchecker','--verbose',m]
            exports=js(lane/'OWNED_EXPORTS.json')
            log=read(lane/'all-owned-types-axioms.log').decode()
            inventory=[json.loads(x)['names'] for x in re.findall(r'MEMBER_OWNED_NAMES (\{[^\n]+\})',log)]
            records=[json.loads(x) for x in re.findall(r'AUDIT_RECORD (\{[^\n]+\})',log)]
            assert records == exports and len(inventory)==1 and sorted(inventory[0]) == sorted(x['name'] for x in exports)
            assert len(exports) == len(set(inventory[0])) == row['total_owned_exports'] == audit['total_owned_exports']
            assert all(x['module']==m and x['type'] and x['type_expression'] and x['kind']!='axiom' and
                       set(x['axioms']) <= {'propext','Classical.choice','Quot.sound'} for x in exports)
            assert not any(x in log for x in ['sorryAx','…','⋯','...'])
            count=sum(not x['is_private'] for x in exports)
            assert count == row['total_public_exports'] == audit['total_public_exports']
            owned+=len(exports);public+=count
        assert (owned, public) == (actual['owned_declarations'],actual['public_declarations'])
        root=member(str(runner.ROOT))
        assert sum(P(n).is_relative_to(root) for n in rows) == actual['retained_files']
        installs=[P(n) for n in rows if P(n).is_relative_to(root/'source-installs') and P(n).name=='SOURCE_INSTALL.json']
        assert installs
        for path in installs:
            for repair in js(path)['sources']:
                if repair['mutated']:
                    assert rows[str(path.parent/'source-backups'/repair['path'])]['sha256'] == repair['before_sha256']
                assert repair['actual_after_sha256'] == repair['after_sha256']
        return {**result,'source_commit':actual['source_commit'],'accepted_owners':23,'owned_declarations':owned,
                'public_declarations':public,'private_declarations':owned-public,'sources':304,'source_installs':len(installs),
                'original_receipt_hashes_and_counts_verified':True,'whole_P1_complete':False}

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('verification requires enabled Python assertions')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('archive',type=Path);p.add_argument('summary',type=Path)
    p.add_argument('--repo',type=Path,help='verify P1.5 ownership and source bindings in this repository')
    a=p.parse_args();print(json.dumps(check(a.archive,json.loads(a.summary.read_bytes()),a.repo),indent=2))
