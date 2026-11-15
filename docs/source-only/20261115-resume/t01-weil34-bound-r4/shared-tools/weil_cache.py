"""Original stock/ABI/preexec engine with only the independent34 caller adapter."""
import hashlib
import json
import os
from pathlib import Path
import re
import sys

from coherent_cache import (BASELINE_GUARD, HERE, WEIL, CacheSession, checked,
                            git, read, require, sha, write)
from weil_scope import BUNDLE, bind, data, installed, roots
from weil_inputs import header, source_closure


def normalized_argv(name, project):
    stem = project/'.lake/build/lib/lean'/Path(*name.split('.'))
    setup = project/'.lake/build/ir'/Path(*name.split('.')).with_suffix('.setup.json')
    source = project/Path(*name.split('.')).with_suffix('.lean')
    args = ['-t0', '-j2', '-M12288', '-D', 'maxRecDepth=100000', '-D', 'maxHeartbeats=4000000']
    if name == 'T01Audit':
        return [*args, '-D', 'warningAsError=true', str(source), '--setup', str(setup), '--json']
    # Fixed Lake's modern postponeCompile path: Lean emits real IR; C/native
    # compilation is unnecessary for proof qualification and is not admitted.
    return [*args, str(source), '-o', str(stem)+'.olean', '-i', str(stem)+'.ilean', '--setup', str(setup), '--json']


def policy(project, logs, binding):
    shadow = Path(os.environ['RUNNER_TEMP']).resolve()/'p0-ci-shadow-toolchain'
    realroot = Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.0-rc1'
    commands = []
    for row in [*data()['source_rows'], dict(module='T01Audit', installation_path='T01Audit.lean')]:
        source = dict(path=str(project/row['installation_path']))
        source.update({k:row[k] for k in ['bytes', 'sha256'] if k in row})
        if row['module'] == 'T01Audit':
            source.update(bytes=(BUNDLE/'WeilAudit.lean').stat().st_size, sha256=sha(BUNDLE/'WeilAudit.lean'))
        commands.append(dict(tool='lean', argv=normalized_argv(row['module'], project), phase='qualified-project',
            classification='EXACT_CURRENT_WEIL34_SOURCE' if row['module'] != 'T01Audit' else 'EXACT_WEIL34_AUDIT',
            source=source, input_binding=str(logs/'direct-inputs'/(row['module']+'.json'))))
    denial, events = logs/'CACHE_COMPILER_DENIALS.jsonl', logs/'CACHE_PREEXEC_EVENTS.jsonl'
    require(not denial.exists() and not events.exists(), 'Admission journals already exist')
    denial.touch(); events.touch()
    value = dict(scope=WEIL, context=binding, project=str(project),
        deny_roots=[str(project/'.lake/packages')], deny_exact_paths=[],
        denial_log=str(denial), event_log=str(events), metadata_cwds=[str(project), str(shadow.parent)],
        admitted_commands=commands, qualification=str(logs/'CACHE_QUALIFICATION.json'),
        caller_inputs=str(logs/'CACHE_CALLER_INPUTS.json'),
        cache_link_output=str(project/'.lake/packages/mathlib/.lake/build/bin/cache'),
        cache_link_response=str(project/'.lake/packages/mathlib/.lake/build/bin/cache.rsp'),
        historical_cache_rsp=read(HERE/'COMPILER_PROTOCOL.json')['historical_cache_rsp'], bootstrap_native_objects=[],
        toolchain_library_roots=[str(realroot/'lib'), str(shadow/'lib')],
        toolchain_roots=dict(realroot=str(realroot), shadow=str(shadow)), bootstrap_cache_reuse_only=True,
        unknown_tools_modes_flags_and_response_files='DENY_BEFORE_COMPILER_EXEC', no_cold_rebuild_fallback=True)
    from qualified_direct import protect_policy
    return protect_policy(value,project)


def physical(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Missing/nonregular physical input: '+str(path))
    return dict(path=str(path), bytes=path.stat().st_size, sha256=sha(path))


def process_receipt(session, p, label, argv):
    require(p['argv'] == argv and p['cwd'] == str(session.project) and p['exit_code'] == 0
            and p['stdout'] == str(session.logs/'cache-processes'/(label+'.stdout'))
            and p['stderr'] == str(session.logs/'cache-processes'/(label+'.stderr'))
            and read(session.logs/'cache-processes'/(label+'.json')) == dict(binding=session.binding, **p)
            and sha(p['stdout']) == p['stdout_sha256'] and sha(p['stderr']) == p['stderr_sha256'],
            'Actual process argv/cwd/exit/raw-output receipt differs: '+label)


class WeilSession(CacheSession):
    def require_fixtures(self):
        super().require_fixtures()
        require(self.receipt('CACHE_FIXTURE_EXECUTION.json')['cwd'] == str(self.project),
                'R3 fixture process cwd differs from the actual canonical project')
        value = self.receipt('CACHE_FIXTURE_RESULT.json')
        expected = {name:sha(HERE/name) for name in [
            'r3_negative_fixtures.py','qualified_algebra.py','weil_cache.py','weil_retention.py','cache_preexec_policy.py']}
        require(value['r3_gate_sources'] == expected, 'R3 fixture or tested live gate source changed after actual fixture process')
        r4 = {name:sha(HERE/name) for name in [
            'qualified_direct.py','r4_negative_fixtures.py','weil_proof.py','weil_scope.py','carrier_originals.py','r4_bound_negative_fixtures.py','r4_donor_ledger_fixtures.py']}
        require(value['r4_gate_sources'] == r4, 'R4 fixture or tested live gate source changed after actual fixture process')

    def __init__(self):
        _, self.binding = bind(); self.scope = WEIL
        self.project, self.logs = roots()
        self.inputs = Path(os.environ['CACHE_INPUTS']).resolve()
        require(not self.inputs.is_relative_to(self.project) and not self.inputs.is_relative_to(self.logs), 'Disjoint cache inputs required')
        self.selection = dict(candidateFullInputProfileSHA256=data()['profile']['sha256'])
        self.index = read(HERE/'inputs/P2_CACHE_BOOTSTRAP_11_PAYLOAD_INDEX.json')
        checkpoint = read(HERE/'inputs/BOOTSTRAP_CHECKPOINT_PAYLOAD.json')
        self.index['objects']['CHECKPOINT.json'] = checkpoint
        self.anchor = self.index['whole_artifact']
        self._part_cache = {}; self._historical_cache = {}; self._raw = None; self.prerequisites = None
        self._source_trees = {}
        self.state = read(self.logs/'runtime/state.json')
        require(self.state['guard_sha256'] == BASELINE_GUARD and Path(self.state['root']).resolve() == self.project,
                'Original guard/root changed')
        self.policy_audit()

    def rows(self):
        return []  # No original167/root object is required or rebuilt for Weil34.

    def root_for(self, name=None):
        if name is None: return self.project
        if name.startswith('Cache.'): return self.project/'.lake/packages/mathlib'
        if name.startswith('Batteries.'): return self.project/'.lake/packages/batteries'
        if name.startswith('LeanPool.'): return self.project
        relative = Path(*name.split('.')).with_suffix('.lean')
        found = [p for p in (self.project/'.lake/packages').iterdir() if (p/relative).is_file()]
        require(len(found) == 1, 'Missing/ambiguous package owner: '+name)
        return found[0]

    def validate_environment(self, raw):
        super().validate_environment(raw)
        installed()
        require(len(raw['native_and_toolchain_library_ABI_receipts']) == 8, 'Original ABI census changed')
        for package in raw['packages']:
            require(not git('-C', self.project/'.lake/packages'/package['name'],
                            'ls-files', '--others', '--exclude-standard', '--', '*.lean', '*.toml'),
                    'Untracked standard package source/config is not an exact-pin input')

    def locate(self, name):
        relative = Path(*name.split('.'))
        if name.startswith(('Init.', 'Lean.', 'Std.', 'Lake.')) or name in {'Init', 'Lean', 'Std', 'Lake'}:
            root = Path(self.state['realbin']).parent
            candidates = [root/'src/lean'/relative.with_suffix('.lean')]
            if name == 'Lake' or name.startswith('Lake.'):
                candidates.append(root/'src/lean/lake'/relative.with_suffix('.lean'))
            candidates = [path for path in candidates if path.is_file()]
            require(len(candidates) == 1, 'Missing/ambiguous official source in the actual pinned distribution: '+name)
            source = candidates[0]
            stem = root/'lib/lean'/relative
            owner = 'official_lean_toolchain'
        else:
            root = self.root_for(name); source = root/relative.with_suffix('.lean')
            stem = root/'.lake/build/lib/lean'/relative
            owner = 'root' if root == self.project else root.name
        require(source.is_file(), 'Actual pinned source absent: '+name)
        modern = header(source.read_text(encoding='utf-8'))['is_module']
        suffixes = ['.olean', '.olean.server', '.olean.private', '.ir.sig', '.ir'] if modern else ['.olean']
        if owner == 'root': suffixes.append('.ilean')
        records = [physical(str(stem)+suffix) for suffix in suffixes]
        source_record = physical(source)
        source_bytes = source.read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(source_bytes)).encode()+b'\0'+source_bytes).hexdigest()
        if owner == 'root':
            expected = next(row for row in data()['source_rows'] if row['module'] == name)
            require(blob == expected['git_blob'], 'Exact vendored source blob changed')
            provenance = dict(commit=expected['source_commit'], git_blob=blob, identity_kind='EXACT_PUBLISHED_VENDOR_SOURCE')
        elif owner == 'official_lean_toolchain':
            provenance = dict(commit=data()['lean_commit'], git_blob=blob,
                identity_kind='CURRENT_EXACT_OFFICIAL_DISTRIBUTION_SOURCE_SNAPSHOT_NOT_HISTORICAL_CORE_OLEAN_RECEIPT')
        else:
            package = next(row for row in self.original()['packages'] if row['name'] == owner)
            if owner not in self._source_trees:
                tree = {}
                for entry in git('-C', root, 'ls-tree', '-r', '-z', package['rev']).split(b'\0'):
                    if not entry: continue
                    metadata, path = entry.split(b'\t', 1)
                    mode, kind, object_id = metadata.decode().split()
                    if kind == 'blob': tree[path.decode()] = object_id
                self._source_trees[owner] = tree
            require(self._source_trees[owner].get(source.relative_to(root).as_posix()) == blob,
                    'Current standard source is not the exact immutable package-tree blob')
            provenance = dict(commit=package['rev'], git_blob=blob, identity_kind='EXACT_PINNED_PACKAGE_SOURCE_BLOB')
        return dict(module=name, owner=owner, source=source_record, source_provenance=provenance, modern=modern, facets=records)

    def artifacts(self, name, all_private=False):
        row = self.locate(name); paths = {Path(r['path']).suffix:r['path'] for r in row['facets']}
        stem = row['facets'][0]['path'][:-len('.olean')]
        if row['modern']:
            return [[stem+'.olean', stem+'.olean.server', *([stem+'.olean.private'] if all_private else [])],
                    [stem+'.ir.sig', stem+'.ir']]
        return [[stem+'.olean']]

    def standard(self):
        from cache_bootstrap import validate
        validate(self)
        names = data()['direct_standard_imports']
        stock = self.run('weil-standard-stock', ['lake', '--no-build', 'build', *['@mathlib/+'+n+':leanArts' for n in names]])
        setups, table, queries = {}, {}, []
        for offset in range(0, len(names), 8):
            batch = names[offset:offset+8]
            result = self.run('weil-standard-setup-'+str(offset),
                ['lake', '--no-build', '--json', 'query', *['@mathlib/+'+n+':setup' for n in batch]])
            lines = [(number, line) for number, line in enumerate(Path(result['stdout']).read_text(encoding='utf-8').splitlines(), 1) if line.strip()]
            values = [json.loads(line) for _, line in lines]
            require(len(values) == len(batch), 'Official stock setup query count differs')
            queries.append(dict(offset=offset, names=batch, process=result, stdout_lines=[number for number, _ in lines], values=values))
            for name, setup in zip(batch, values):
                require(setup['name'] == name and isinstance(setup['importArts'], dict), 'Unexpected official full ModuleSetup')
                setups[name] = setup
                for imported, groups in setup['importArts'].items():
                    require(imported not in table or table[imported] == groups, 'Conflicting stock resolved import artifacts')
                    table[imported] = groups
                table[name] = self.artifacts(name)
        # The exporter uses FoldConsts directly. Its official source/serialized
        # identity is current-distribution evidence, never a historical olean claim.
        closure = source_closure(self, [*names, 'Lean.Util.FoldConsts'])
        require(set(table) <= set(closure), 'Official setup import escaped the complete real source header closure')
        for module in closure:
            if module not in table: table[module] = self.artifacts(module)
        files, identities = {}, {}
        for name, groups in table.items():
            require(groups and groups[0] and groups[0][0].endswith('.olean'), 'IR-only stock import is not data')
            identities[name] = closure[name]['identity']
            for part in [identities[name]['source'], *identities[name]['facets']]:
                files[part['path']] = part
            for group in groups:
                for value in group:
                    p = Path(value)
                    if not p.is_absolute(): p = self.project/p
                    require(p.resolve().is_relative_to(self.project.resolve())
                            or p.resolve().is_relative_to(Path(self.state['realbin']).parent.resolve()),
                            'Stock import path escaped fixed package/official roots')
                    files[str(p)] = physical(p)
        search = self.run('weil-actual-search-path', ['lake', '--no-build', 'env', sys.executable, '-c',
            "import os,json;print(json.dumps({k:os.environ.get(k,'') for k in ['LEAN_PATH','LEAN_SYSROOT']}))"])
        search_value = read(search['stdout']); self.validate_search(search_value)
        self.emit('WEIL_STANDARD_INPUTS.json', dict(stock_process=stock, setups=setups, setup_queries=queries, importArts=table,
            source_private_closure=closure, identities=identities, physical_files=files,
            search_path_process=search, search_path_value=search_value,
            official_current_distribution_not_historical_core_receipts=True))
        self.emit('CACHE_QUALIFICATION.json', dict(status='PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY',
            stock_process=stock, standard_inputs_sha256=sha(self.logs/'WEIL_STANDARD_INPUTS.json'),
            bootstrap_qualification_sha256=sha(self.logs/'CACHE_BOOTSTRAP_QUALIFICATION.json'),
            protected_source_compiler_events=0, proof_or_full_kernel_acceptance=False))
        sources = {str(self.project/r['installation_path']):physical(self.project/r['installation_path']) for r in data()['source_rows']}
        sources[str(self.project/'T01Audit.lean')] = physical(self.project/'T01Audit.lean')
        self.emit('CACHE_CALLER_INPUTS.json', dict(qualification_sha256=sha(self.logs/'CACHE_QUALIFICATION.json'), sources=sources))

    def validate_search(self, search):
        require(search['LEAN_SYSROOT'] == self.state['shadow'], 'Actual sysroot changed')
        official = {Path(self.state['shadow']).joinpath('lib/lean').resolve(),
                    Path(self.state['realbin']).parent.joinpath('lib/lean').resolve()}
        roots = [self.project/'.lake/build/lib/lean'] + [self.project/'.lake/packages'/p['name']/'.lake/build/lib/lean'
                 for p in self.original()['packages']]
        actual = {Path(p).resolve() for p in search['LEAN_PATH'].split(os.pathsep) if p}
        require(actual <= {p.resolve() for p in roots} | official
                and (self.project/'.lake/build/lib/lean').resolve() in actual, 'Unbound actual Lean search root')
        for root in actual | {p.resolve() for p in roots}:
            if root in official: continue
            for core in ['Lean', 'Init', 'Std', 'Lake']:
                require(not (root/core).exists() and not list(root.glob(core+'.*')), 'Package/project shadows official core')

    def stock_qualification_inputs(self):
        from cache_bootstrap import validate
        validate(self); self.validate_environment(self.original())
        q = self.receipt('CACHE_QUALIFICATION.json'); standard = self.receipt('WEIL_STANDARD_INPUTS.json')
        require(q['standard_inputs_sha256'] == sha(self.logs/'WEIL_STANDARD_INPUTS.json')
                and q['bootstrap_qualification_sha256'] == sha(self.logs/'CACHE_BOOTSTRAP_QUALIFICATION.json')
                and q['status'] == 'PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY'
                and q['stock_process'] == standard['stock_process']
                and q['protected_source_compiler_events'] == 0 and q['proof_or_full_kernel_acceptance'] is False,
                'Stock qualification receipt changed')
        names = data()['direct_standard_imports']
        process_receipt(self, standard['stock_process'], 'weil-standard-stock',
                        ['lake', '--no-build', 'build', *['@mathlib/+'+n+':leanArts' for n in names]])
        expected_setups = {}; original_table = {}
        require(len(standard['setup_queries']) == (len(names)+7)//8, 'Missing original setup query batch')
        for offset, query in zip(range(0, len(names), 8), standard['setup_queries']):
            batch = names[offset:offset+8]
            require(query['offset'] == offset and query['names'] == batch, 'Original setup batch/order differs')
            process_receipt(self, query['process'], 'weil-standard-setup-'+str(offset),
                            ['lake', '--no-build', '--json', 'query', *['@mathlib/+'+n+':setup' for n in batch]])
            lines = [(number, line) for number, line in enumerate(Path(query['process']['stdout']).read_text(encoding='utf-8').splitlines(), 1) if line.strip()]
            values = [json.loads(line) for _, line in lines]
            require(values == query['values'] and len(values) == len(batch)
                    and query['stdout_lines'] == [number for number, _ in lines], 'Original setup stdout/ordered parsed line positions changed')
            for line, (name, setup) in enumerate(zip(batch, values), 1):
                require(setup['name'] == name and isinstance(setup['importArts'], dict), 'Wrong ordered source setup name')
                expected_setups[name] = setup
                for imported, groups in setup['importArts'].items():
                    require(imported not in original_table or original_table[imported] == groups, 'Changed stock setup merge')
                    original_table[imported] = groups
                original_table[name] = self.artifacts(name)
        require(standard['setups'] == expected_setups, 'Source setup values no longer equal authenticated raw output')
        closure = source_closure(self, [*names, 'Lean.Util.FoldConsts'])
        require(standard['source_private_closure'] == closure and set(original_table) <= set(closure),
                'Complete current pinned source/private-artifact closure changed')
        for module in closure:
            if module not in original_table: original_table[module] = self.artifacts(module)
        require(standard['importArts'] == original_table
                and standard['identities'] == {name:row['identity'] for name, row in closure.items()}, 'Prepared complete artifact map changed')
        argv = ['lake', '--no-build', 'env', sys.executable, '-c',
                "import os,json;print(json.dumps({k:os.environ.get(k,'') for k in ['LEAN_PATH','LEAN_SYSROOT']}))"]
        process_receipt(self, standard['search_path_process'], 'weil-actual-search-path', argv)
        require(read(standard['search_path_process']['stdout']) == standard['search_path_value'], 'Actual authenticated search value changed')
        self.validate_search(standard['search_path_value'])
        expected_files = {}
        for groups in original_table.values():
            for group in groups:
                for value in group:
                    p = Path(value)
                    if not p.is_absolute(): p = self.project/p
                    expected_files[str(p)] = physical(p)
        for row in closure.values():
            for part in [row['identity']['source'], *row['identity']['facets']]: expected_files[part['path']] = part
        require(standard['physical_files'] == expected_files, 'Complete original resolved input/source/facet inventory changed')
        for row in standard['physical_files'].values(): checked(row['path'], row)
        for row in standard['identities'].values():
            checked(row['source']['path'], row['source'])
            for facet in row['facets']: checked(facet['path'], facet)
        caller = self.receipt('CACHE_CALLER_INPUTS.json')
        expected_sources = {str(self.project/r['installation_path']):physical(self.project/r['installation_path']) for r in data()['source_rows']}
        expected_sources[str(self.project/'T01Audit.lean')] = physical(self.project/'T01Audit.lean')
        require(caller['qualification_sha256'] == sha(self.logs/'CACHE_QUALIFICATION.json')
                and caller['sources'] == expected_sources, 'Original exact source/frozen auditor admission changed')
        return standard

    def qualification_inputs(self):
        standard = self.stock_qualification_inputs()
        from qualified_direct import validate
        validate(self,standard)
        return standard

    def compile_census(self, complete):
        self.policy_audit()
        events = [json.loads(x) for x in (self.logs/'CACHE_PREEXEC_EVENTS.jsonl').read_text().splitlines() if x.strip()]
        counts = {r['module']:0 for r in data()['source_rows']}
        expected = {str(self.project/r['installation_path']):r['module'] for r in data()['source_rows']}
        for event in events:
            if event['classification'] == 'EXACT_CURRENT_WEIL34_SOURCE':
                require(len(event['physical_inputs']) == 2, 'Direct source/setup input binding absent')
                counts[expected[event['physical_inputs'][0]['path']]] += 1
        from qualified_direct import validate_census
        validate_census(counts,complete)
        return counts


if __name__ == '__main__':
    session = WeilSession(); phase = sys.argv[1]
    if phase == 'bootstrap':
        from cache_bootstrap import bootstrap
        bootstrap(session)
    elif phase == 'prior_direct_acquire':
        from qualified_direct import acquire
        acquire(session)
    elif phase == 'prior_direct_admit':
        from qualified_direct import admit
        admit(session)
    elif phase in {'fixtures', 'acquire', 'standard'}:
        getattr(session, phase)()
    else:
        raise ValueError('Unknown stock/cache phase')
