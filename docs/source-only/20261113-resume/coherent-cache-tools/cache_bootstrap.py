"""Explicitly adopted P2/Stored reuse of the authentic T01 Cache executable; no compiler fallback.

Range acquisition, facet copying, trace descriptors, setup/import comparison,
runtime/ABI and official-install identity use the existing shared implementation.
This adapter never edits a trace, setup, response file or historical classifier.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import sys

from coherent_cache import HERE, NATIVE, PARENT, checked, read, require, sha, write

SELECTION = '2e7bb18d35a8de3db8f5acf2139747175430dad91359631d3f04b1eaff6c1010'
INDEX = '92bd3af256690b9c4fb7f9c3b819649ec892d9bba20a2497a46e2ef6da5a511d'
LEAVES = '58bca62be1e3ed2595e1ade5c6a99615c3de8476c5abe298e3e1d2937090789c'
ADOPTION = {'selection_sha256':SELECTION,'payload_index_sha256':INDEX,'leaf_rule_sha256':LEAVES,
            'modules':11,'module_facets':129,'binary_facets':4,'selected_payloads':144,
            'stock_target':'@mathlib/cache','zero_source_C_and_link_compiler_events':True,
            'no_cold_fallback':True,'trace_setup_response_bytes_unmodified':True}


def load_inputs():
    names = ['P2_CACHE_BOOTSTRAP_11_SELECTION.json', 'P2_CACHE_BOOTSTRAP_11_PAYLOAD_INDEX.json',
             'P2_CACHE_BOOTSTRAP_LEAF_RULE.json']
    for name, expected in zip(names, [SELECTION, INDEX, LEAVES]):
        require(sha(HERE/'inputs'/name) == expected, 'Wrong independently selected Cache bootstrap input')
    return tuple(read(HERE/'inputs'/name) for name in names)


def binary_trace(session, raw, selected):
    binary = session.project/'.lake/packages/mathlib/.lake/build/bin/cache'
    trace = read(str(binary)+'.trace')
    require(trace['schemaVersion'] == '2025-09-10' and trace['synthetic'] is False
            and trace['depHash'] == selected['executable_link_trace_depHash']
            and trace['outputs'] == selected['executable_link_trace_output']
            and trace['outputs'] == Path(str(binary)+'.hash').read_text().strip(), 'Original Cache executable trace/sidecar differs')
    link_inputs = trace['inputs'][0][1][0][1]
    require(link_inputs == selected['link_inputs_ordered'] and len(link_inputs) == 11, 'Original Cache native link input order differs')
    for old_path, old_hash in link_inputs:
        session.historical_file(raw, old_path)
        sidecar = Path(session.mapping(raw, old_path)+'.hash')
        session.historical_file(raw, old_path+'.hash')
        native = read(str(sidecar).removesuffix('.hash')+'.trace')
        require(native['schemaVersion'] == '2025-09-10' and native['synthetic'] is False
                and native['outputs'] == old_hash+'.o' and sidecar.read_text().strip() == old_hash,
                'Original Cache native input hash/trace differs')
    return binary


def glibc_identity(session, raw, rule, binary):
    # Full authentic executable SHA is checked by the shared facet verifier
    # BEFORE any loader or executable process sees it. readelf does not run it.
    with binary.open('rb') as source: header = source.read(64)
    require(header[:6] == b'\x7fELF\x02\x01' and struct.unpack_from('<HH',header,16) ==
            (rule['ELF']['elf_type'],rule['ELF']['machine']), 'Cache ELF ABI differs')
    dynamic = session.run('bootstrap-elf-dynamic', ['readelf','-dW',binary])
    program = session.run('bootstrap-elf-program', ['readelf','-lW',binary])
    text = Path(dynamic['stdout']).read_text()
    needed = re.findall(r'\(NEEDED\).*Shared library: \[([^\]]+)\]',text)
    interp = re.findall(r'Requesting program interpreter: ([^\]]+)',Path(program['stdout']).read_text())
    require(needed == rule['ELF']['DT_NEEDED'] and interp == [rule['ELF']['interpreter']]
            and not re.search(r'\((?:RPATH|RUNPATH)\)',text), 'Cache full authenticated ELF dynamic identity differs')
    require(raw['platform'] == rule['historical_platform'] and rule['glibc']['historical_other_five_individual_sha256_available'] is False,
            'Historical limited glibc provenance changed')
    current_os = Path('/etc/os-release').read_text()
    require('ID=ubuntu\n' in current_os and 'VERSION_ID="24.04"' in current_os, 'Cache finite Ubuntu distribution origin changed')
    package = rule['glibc']['current_required_package']
    require(package == 'libc6:amd64' and len(needed) == 6, 'Unexpected dynamic package scope')
    info = session.run('bootstrap-glibc-package', ['dpkg-query','-W','-f','${Package}|${Architecture}|${Version}|${Status}\n',package])
    fields = Path(info['stdout']).read_text().strip().split('|')
    require(len(fields) == 4 and fields[0] == 'libc6' and fields[1] == 'amd64' and fields[3] == 'install ok installed', 'glibc package is not installed')
    listing = session.run('bootstrap-glibc-owned-files', ['dpkg-query','-L',package])
    owned = {Path(x).resolve() for x in Path(listing['stdout']).read_text().splitlines() if x.startswith('/')}
    md5_path = Path('/var/lib/dpkg/info/libc6:amd64.md5sums')
    manifest = []
    for line in md5_path.read_text().splitlines():
        digest, relative = line.split(None,1)
        manifest.append((Path('/'+relative).resolve(),digest))
    official = {};receipts = []
    for name in needed:
        logical = Path(rule['ELF']['interpreter']) if name == 'ld-linux-x86-64.so.2' else Path('/lib/x86_64-linux-gnu')/name
        physical = logical.resolve(strict=True)
        require(physical.is_relative_to('/usr/lib/x86_64-linux-gnu') and physical in owned, 'Cache library is not an official glibc package file')
        expected = [digest for path,digest in manifest if path == physical]
        require(len(expected) == 1, 'Cache library lacks one exact glibc md5 manifest entry')
        with physical.open('rb') as source: actual_md5 = hashlib.file_digest(source,'md5').hexdigest()
        require(actual_md5 == expected[0], 'Current installed glibc package file changed')
        value = {'name':name,'logical_path':str(logical),'path':str(physical),'bytes':physical.stat().st_size,
                 'sha256':sha(physical),'current_package':package,'current_package_md5':actual_md5}
        if name == 'libc.so.6': require(value['sha256'] == rule['glibc']['pinned_old_libc_sha256'], 'Historical libc ABI bytes changed')
        receipts.append(value);official[name] = physical
    env_script = "import json,os;print(json.dumps({k:os.environ.get(k,'') for k in ['LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT']}))"
    environment = session.run('bootstrap-loader-environment', ['lake','--no-build','env',sys.executable,'-c',env_script])
    current_env = read(environment['stdout'])
    require(not current_env['LD_PRELOAD'] and not current_env['LD_AUDIT'], 'Cache loader injection is forbidden')
    # Stock Lake's actual environment, interpreted by the validated official
    # loader, must select those SAME six physical files. The main does not run.
    loader = session.run('bootstrap-loader-map', ['lake','--no-build','env',rule['ELF']['interpreter'],'--list',binary])
    resolved = {}
    for line in Path(loader['stdout']).read_text().splitlines():
        match = re.match(r'\s*(\S+) => (\S+) \(',line)
        if match: name,path = match.groups()
        else:
            match = re.match(r'\s*(/\S+) \(',line)
            if match: path = match.group(1);name = Path(path).name
            elif 'linux-vdso.so.1' in line: continue
            else: raise ValueError('Unexpected Cache loader-map row: '+line)
        require(name in official and name not in resolved and Path(path).resolve(strict=True) == official[name], 'Cache actual loader resolution escapes the official package')
        resolved[name] = str(official[name])
    require(set(resolved) == set(needed), 'Cache loader resolution omitted a needed library')
    return {'ELF':rule['ELF'],'dynamic_process':dynamic,'program_process':program,'package_process':info,
            'owned_files_process':listing,'md5_manifest_path':str(md5_path),'md5_manifest_sha256':sha(md5_path),
            'package_version':fields[2],'actual_libraries':receipts,'loader_environment_process':environment,
            'loader_environment':current_env,'loader_map_process':loader,'resolved_libraries':resolved,
            'historical_platform':rule['historical_platform'],'current_image_os':os.environ.get('ImageOS'),
            'current_image_version':os.environ.get('ImageVersion'),'current_os_release':current_os,
            'historical_non_libc_five_individual_hashes_available':False,'historical_non_libc_five_bytes_verified':False}


def verify(session):
    selected,_,_ = load_inputs()
    restored = session.verify_restored('CACHE_BOOTSTRAP_RESTORE.json')
    expected = []
    for row in selected['rows']:
        root = session.root_for(row['module'])
        expected.append({'module':row['module'],'source':{'path':str(root/row['source']['path']),
            'bytes':row['source']['bytes'],'sha256':row['source']['sha256']},
            'facets':[dict(path=str(root/f['path']),bytes=f['bytes'],sha256=f['sha256'],object=f['object']) for f in row['facets']]})
    binaries = [dict(path=str(session.project/'.lake/packages/mathlib'/f['path']),bytes=f['bytes'],sha256=f['sha256'],object=f['object'])
                for f in selected['binaryFacets']]
    require(restored['modules'] == expected and restored['binary_facets'] == binaries
            and restored['selection_sha256'] == SELECTION and restored['leaf_rule_sha256'] == LEAVES,
            'Bootstrap restore receipt is not the full exact selected graph')
    for facet in restored['binary_facets']: checked(facet['path'],facet)
    binary = session.project/'.lake/packages/mathlib/.lake/build/bin/cache'
    require({str(p) for p in binary.parent.glob('cache*') if p.is_file()} == {r['path'] for r in restored['binary_facets']},
            'Cache executable facets added/removed, including possible no-build marker')
    return restored


def bootstrap(session):
    require(session.scope in {NATIVE,PARENT}, 'Explicit bootstrap scope required')
    selected,index,rule = load_inputs();raw = session.original();session.require_fixtures()
    require(selected['oldRoot'] == raw['runtime_state']['root'] and selected['source_files'] == 11
            and selected['module_facets'] == 129 and len(selected['binaryFacets']) == 4
            and selected['leaf_rule_sha256'] == LEAVES and selected['coldFallback'] is False, 'Bootstrap graph changed')
    checkout = session.run('bootstrap-resolve-pinned-dependencies', ['lake','--no-build','env','printenv','LEAN_PATH'])
    session.validate_environment(raw)
    current_profile=selected['newProjectProfileSHA256'] if session.scope==NATIVE else session.selection['candidateFullInputProfileSHA256']
    require(raw['runtime_state']['input_sha256'][selected['oldRoot']+'/lakefile.toml'] == selected['oldProjectProfileSHA256']
            and (session.scope!=PARENT or current_profile==selected['oldProjectProfileSHA256'])
            and sha(session.project/'lakefile.toml') == current_profile, 'Old/root project profiles were mixed')
    origin = HERE/'inputs/ARCHITECT_COMMAND_LEAF_RULE.json'
    require(sha(origin) == rule['shared_architect_toolchain_origin_rule_sha256']
            and rule['historical_per_core_olean_hashes_available'] is False and rule['historical_core_bytes_verified'] is False,
            'Four-leaf official provenance boundary changed')
    identity = session.leaf_runtime_identity(raw,rule,'bootstrap-four-leaves')
    prior_rows = {r['module']:r for r in raw['all_guarded_package_compilations'] if 'module' in r}
    leaves = {r['module']:r for r in rule['leaves']};require(len(leaves) == 4, 'Four-leaf census differs')
    restored = []
    for row in selected['rows']:
        prior = prior_rows[row['module']]
        require(prior['package'] == row['package'] and prior['classification'] == row['originalClassification']
                and prior['lake_completed_trace'] and prior['output_bound_command'] and not prior['missing_actual_import_artifacts']
                and prior['actual_import_count'] == row['priorActualImportCount']
                and prior['actual_import_map_sha256'] == row['priorActualImportMapSHA256']
                and [x.replace(selected['oldRoot'],'{root}') for x in prior['command']['command']] == row['guardedCommandNormalized'],
                'Historical bootstrap source/command/import classification changed')
        if row['module'] in leaves:
            leaf = leaves[row['module']]
            require(prior['classification'] == leaf['original_classification'] == 'PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED'
                    and prior['actual_import_count'] == 0 and prior['command'] == leaf['original_guarded_command']
                    and read(session.inputs/prior['setup']['payload']) == leaf['old_setup'], 'Quarantined leaf was not independently rebound')
        else: require(prior['classification'] == 'PACKAGE_COMPILE_CHECKPOINT_REQUIRES_VERIFIED_REBIND', 'Unexpected bootstrap quarantine')
        restored.append(session.restore_module(raw,row))
        root = session.root_for(row['module']);relative = Path(*row['module'].split('.'))
        trace = read(root/'.lake/build/lib/lean'/relative.with_suffix('.trace'))
        require(trace['depHash'] == row['lean_trace_depHash'], 'Bootstrap Lean trace differs')
        native = read(root/'.lake/build/ir'/Path(str(relative)+'.c.o.export.trace'))
        require(native['depHash'] == row['native_trace_depHash'] and native['outputs'] == row['native_trace_output']+'.o', 'Bootstrap native trace differs')
    binaries = session.restore_facets(raw,selected['binaryFacets'],session.project/'.lake/packages/mathlib','mathlib')
    session.emit('CACHE_BOOTSTRAP_RESTORE.json', {'modules':restored,'binary_facets':binaries,
                 'selection_sha256':SELECTION,'leaf_rule_sha256':LEAVES,'old_project_profile_adopted':session.scope==PARENT})
    verify(session);binary = binary_trace(session,raw,selected)
    glibc = glibc_identity(session,raw,rule,binary)
    process = session.run('bootstrap-stock-cache-executable', ['lake','--no-build','build','@mathlib/cache'])
    verify(session)
    target = lambda name:'@'+('mathlib' if name.startswith('Cache.') else 'batteries')+'/+'+name+':setup'
    setups,parts = session.qualify_setups(raw,[r['module'] for r in selected['rows']],selected['rows'],target,'bootstrap-stock-setup')
    session.emit('CACHE_BOOTSTRAP_IMPORT_PARTS.json', {'parts':parts})
    verify(session);session.validate_environment(raw)
    get = session.run('bootstrap-stock-cache-get', ['lake','--no-build','exe','@mathlib/cache','get'])
    verify(session);session.validate_environment(raw)
    session.emit('CACHE_BOOTSTRAP_QUALIFICATION.json', {'status':'PASS_AUTHENTIC_CACHE_BOOTSTRAP_STOCK_NO_BUILD_INPUT_ONLY',
        'selection_sha256':SELECTION,'leaf_rule_sha256':LEAVES,'dependency_checkout_process':checkout,
        'leaf_identity':identity,'glibc_identity':glibc,'stock_binary_process':process,'stock_cache_get_process':get,
        'setups':setups,'physical_parts_sha256':sha(session.logs/'CACHE_BOOTSTRAP_IMPORT_PARTS.json'),
        'bootstrap_source_C_and_link_compiler_events':0,'original_classifications_preserved':True,
        'historical_core_olean_bytes_verified':False,'proof_acceptance':False,'cold_fallback':False})


def validate(session):
    if session.scope not in {NATIVE,PARENT}: return
    selected,index,rule = load_inputs();verify(session);session.policy_audit()
    value = session.receipt('CACHE_BOOTSTRAP_QUALIFICATION.json')
    require(value['status'] == 'PASS_AUTHENTIC_CACHE_BOOTSTRAP_STOCK_NO_BUILD_INPUT_ONLY'
            and value['selection_sha256'] == SELECTION and value['leaf_rule_sha256'] == LEAVES
            and value['bootstrap_source_C_and_link_compiler_events'] == 0 and value['cold_fallback'] is False,
            'Bootstrap qualification belongs to a different input graph')
    names = [r['module'] for r in selected['rows']]
    require([r['module'] for r in value['setups']] == names
            and value['stock_binary_process']['argv'] == ['lake','--no-build','build','@mathlib/cache']
            and value['stock_cache_get_process']['argv'] == ['lake','--no-build','exe','@mathlib/cache','get']
            and value['dependency_checkout_process']['argv'] == ['lake','--no-build','env','printenv','LEAN_PATH'],
            'Bootstrap stock command or exact eleven-module census differs')
    query = ['lake','--no-build','--json','query',*['@'+r['package']+'/+'+r['module']+':setup' for r in selected['rows']]]
    first = value['setups'][0]['official_current_setup_process']
    for number,(record,row) in enumerate(zip(value['setups'],selected['rows']),1):
        require(record['official_current_setup_process'] == first and first['argv'] == query
                and record['official_current_setup_stdout_line'] == number
                and record['physical_import_count'] == row['priorActualImportCount']
                and record['original_import_map_sha256'] == row['priorActualImportMapSHA256']
                and record['current_all_fields_equal_after_explicit_root_mapping'] is True,
                'Bootstrap ordered stock setup/query receipt differs')
    identity = value['leaf_identity']
    runtime = {session.mapping(session.original(),path):digest for path,digest in rule['historical_matched_runtime_payloads'].items()}
    require(len(identity['runtime_payloads']) == 11 and {r['path']:r['sha256'] for r in identity['runtime_payloads']} == runtime
            and identity['abi_receipts'] == rule['abi_receipts'] and len(identity['abi_receipts']) == 8
            and identity['current_install_log_sha256'] == sha(session.logs/'install-toolchain.log'),
            'Bootstrap full historical runtime/ABI census differs')
    glibc = value['glibc_identity']
    require(glibc['ELF'] == rule['ELF'] and [r['name'] for r in glibc['actual_libraries']] == rule['ELF']['DT_NEEDED']
            and len(glibc['actual_libraries']) == 6
            and glibc['resolved_libraries'] == {r['name']:r['path'] for r in glibc['actual_libraries']}
            and glibc['loader_map_process']['argv'] == ['lake','--no-build','env',rule['ELF']['interpreter'],'--list',
                str(session.project/'.lake/packages/mathlib/.lake/build/bin/cache')], 'Bootstrap six-library/loader census differs')
    for library in glibc['actual_libraries']:
        logical = rule['ELF']['interpreter'] if library['name'] == 'ld-linux-x86-64.so.2' else '/lib/x86_64-linux-gnu/'+library['name']
        require(library['logical_path'] == logical and str(Path(logical).resolve(strict=True)) == library['path']
                and library['current_package'] == 'libc6:amd64', 'Bootstrap library physical identity changed')
    parts = session.receipt('CACHE_BOOTSTRAP_IMPORT_PARTS.json')
    require(sha(session.logs/'CACHE_BOOTSTRAP_IMPORT_PARTS.json') == value['physical_parts_sha256'], 'Bootstrap import receipt changed')
    for part in parts['parts'].values(): checked(part['path'],part)
    for part in value['glibc_identity']['actual_libraries']: checked(part['path'],part)
    require(sha(value['glibc_identity']['md5_manifest_path']) == value['glibc_identity']['md5_manifest_sha256'], 'glibc package manifest changed')
    for part in value['leaf_identity']['runtime_payloads']: require(sha(part['path']) == part['sha256'], 'Bootstrap runtime changed')
    for part in value['leaf_identity']['abi_receipts']: checked(Path(session.mapping(session.original(),part['original_path'])).resolve(strict=True),part)
    processes = [value['dependency_checkout_process'],value['stock_binary_process'],value['stock_cache_get_process'],
                 value['leaf_identity']['search_path_process']]
    processes += [r['official_current_setup_process'] for r in value['setups']]
    processes += [v for k,v in value['glibc_identity'].items() if k.endswith('_process')]
    for row in processes:
        require(row['cwd'] == str(session.project) and row['exit_code'] == 0 and sha(row['stdout']) == row['stdout_sha256'] and sha(row['stderr']) == row['stderr_sha256']
                and read(Path(row['stdout']).with_suffix('.json')) == {'binding':session.binding,**row}, 'Bootstrap stock/process evidence changed')
