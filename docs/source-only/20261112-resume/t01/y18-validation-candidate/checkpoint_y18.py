"""Remote hash/copy checkpoint only; never invokes Lean, Lake or proof evaluation.

Preserves completed and partial build bytes separately from mathematical acceptance.
Restoration requires this receipt plus a new exact-source/import/ABI comparison.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys


def sha(path: Path) -> str:
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def json_file(path: Path):
    return json.loads(path.read_text(encoding='utf-8'))


def main() -> None:
    if os.getenv('GITHUB_ACTIONS') != 'true':
        raise SystemExit('Root-authorized remote GitHub Actions only')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', required=True, type=Path)
    p.add_argument('--manifest', required=True, type=Path)
    p.add_argument('--logs', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    args = p.parse_args()
    project = args.project.resolve()
    logs = args.logs.resolve()
    if args.output.exists():
        raise ValueError('Refuse an existing checkpoint destination')
    args.output.mkdir(parents=True)
    objects = args.output / 'objects'
    objects.mkdir()
    manifest = json_file(args.manifest)
    files: dict[str, dict] = {}
    issues: list[str] = []
    hash_cache: dict[Path, str] = {}

    def digest(path: Path) -> str:
        path = path.resolve()
        if path not in hash_cache:
            hash_cache[path] = sha(path)
        return hash_cache[path]

    def store_file(path: Path, role: str, copy_bytes: bool = True) -> dict:
        previous = files.get(str(path))
        if previous and (not copy_bytes or 'payload' in previous):
            if role not in previous['roles']:
                previous['roles'].append(role)
            return previous
        # Resolve a link only for a separately validated reference; never archive a link.
        resolved = path.resolve(strict=True)
        if not resolved.is_file():
            raise ValueError(f'Not a regular file: {path}')
        h = digest(resolved)
        r = {'original_path': str(path), 'resolved_path': str(resolved),
             'bytes': resolved.stat().st_size, 'sha256': h, 'role': role,
             'roles': list(dict.fromkeys((previous['roles'] if previous else []) + [role])),
             'mode': resolved.stat().st_mode & 0o777}
        if copy_bytes:
            target = objects / h
            if not target.exists():
                shutil.copyfile(resolved, target)
                if sha(target) != h:
                    raise ValueError(f'Checkpoint copy differs: {path}')
            r['payload'] = 'objects/' + h
        if previous and previous['sha256'] != h:
            raise ValueError(f'Checkpoint input/output mutated during collection: {path}')
        if previous and 'payload' in previous:
            r['payload'] = previous['payload']
        files[str(path)] = r
        # Journal path-to-content identity immediately. Even an interrupted early
        # collector leaves identified quarantined facets, not anonymous hash blobs.
        with (args.output / 'RAW_FILES.jsonl').open('a', encoding='utf-8') as journal:
            journal.write(json.dumps(r, sort_keys=True) + '\n')
        return r

    def checked_source(path: Path, expected: dict) -> dict:
        r = store_file(path, 'exact-source-or-data-receipt', copy_bytes=path.suffix == '.lean')
        if r['sha256'] != expected['sha256'] or r['bytes'] != expected['bytes']:
            raise ValueError(f'Staged source/data changed: {path}')
        return r

    # Save available raw bytes/logs before any provenance validation can fail. These
    # remain unclassified/quarantined until the later receipt binds their inputs.
    raw_roots = [project / '.lake/build']
    for directory in (project / '.lake/packages').glob('*'):
        if directory.is_dir() and directory.name != 'mathlib':
            raw_roots.append(directory / '.lake/build')
    mathlib_build = project / '.lake/packages/mathlib/.lake/build'
    raw_roots += [mathlib_build / 'lib/lean/Cache', mathlib_build / 'ir/Cache', mathlib_build / 'bin']
    for directory in raw_roots:
        if directory.is_dir():
            for path in sorted(directory.rglob('*')):
                if path.is_file() and not path.is_symlink():
                    store_file(path, 'raw-partial-build-bytes-unclassified')
    for path in sorted(logs.rglob('*')):
        if path.is_file() and not path.is_symlink():
            store_file(path, 'raw-run-log-unclassified')
    (args.output / 'SNAPSHOT_ACQUISITION.json').write_text(json.dumps({
        'status': 'RAW_SNAPSHOT_IDENTIFIED_BEFORE_PROVENANCE_VALIDATION',
        'raw_index': 'RAW_FILES.jsonl', 'identified_paths': len(files),
        'acquisition_phase_complete': True, 'quarantined_until_verified': True,
        'kernel_verified': False}, indent=2) + '\n')

    sources = {}
    for f in manifest['files'] + manifest['data_inputs']:
        sources[f['install_path']] = checked_source(project / f['install_path'], f)
    for f in manifest['audit_sources']:
        sources[f['install_path']] = checked_source(project / f['install_path'], f)
    for f in manifest['all_native_sources']:
        checked_source(project / '.lake/packages/goldbach' / f['install_path'], f)
    for path in [args.manifest, project / 'Y18_PROVENANCE.json',
                 project / 'lean-toolchain', project / 'lake-manifest.json', project / 'lakefile.toml']:
        store_file(path, 'configuration-and-source-provenance')

    state_path = Path(os.environ['P0_CI_GUARD_STATE']).resolve()
    state = json_file(state_path)
    audit_path = state_path.parent / 'audit.json'
    runtime_ok = audit_path.is_file() and json_file(audit_path).get('status') == 'PASS_RUNTIME_GUARD_ONLY'
    if runtime_ok and json_file(audit_path).get('state_sha256') != digest(state_path):
        runtime_ok = False
        issues.append('runtime audit does not bind the captured guard state')
    for mapping in ['runtime_sha256', 'input_sha256', 'action_script_sha256']:
        for name, expected in state[mapping].items():
            path = Path(name)
            if not path.is_file() or digest(path) != expected:
                runtime_ok = False
                issues.append('runtime/input pin mismatch: ' + name)
    command_path = Path(state['log'])
    commands = [json.loads(line) for line in command_path.read_text().splitlines() if line.strip()]
    if runtime_ok and json_file(audit_path).get('command_log_sha256') != digest(command_path):
        runtime_ok = False
        issues.append('runtime audit does not bind the final compiler command log')
    for path in sorted(logs.rglob('*')):
        if path.is_file() and not path.is_symlink():
            store_file(path, 'run-log-and-runtime-receipt')

    lock = json_file(project / 'lake-manifest.json')
    packages = []
    package_roots = []
    package_ok = True
    for pkg in lock['packages']:
        directory = (project / lock['packagesDir'] / pkg['name']).resolve()
        try:
            head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True, stderr=subprocess.STDOUT).strip()
            dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True, stderr=subprocess.STDOUT)
        except (OSError, subprocess.CalledProcessError) as e:
            head, dirty = None, 'CHECKOUT_METADATA_UNAVAILABLE'
            issues.append(f'Package {pkg["name"]} metadata unavailable: {e}')
        allowed_native_configuration = False
        if pkg['name'] == 'goldbach' and head == pkg['rev']:
            selected_config = manifest['native_configuration']['selected']
            changed = subprocess.check_output(['git', '-C', str(directory), 'diff', '--name-only', 'HEAD', '--'], text=True).splitlines()
            allowed_native_configuration = (changed == ['lakefile.toml']
                and (directory / 'lakefile.toml').is_file()
                and digest(directory / 'lakefile.toml') == selected_config['sha256'])
        good = head == pkg['rev'] and (not dirty or allowed_native_configuration)
        package_ok = package_ok and good
        packages.append({'name': pkg['name'], 'url': pkg['url'], 'rev': head,
                         'expected_rev': pkg['rev'], 'tracked_sources_clean': not bool(dirty), 'exact_reviewed_native_configuration_only': allowed_native_configuration,
                         'pin_matches': good, 'root': str(directory)})
        package_roots.append((pkg['name'], directory))
    realroot = Path(state['realbin']).resolve().parent
    shadow = Path(state['shadow']).resolve()
    cache_root = (Path.home() / '.cache/lake').resolve()
    allowed_roots = [project, realroot, shadow, cache_root]
    abi_receipts = []
    for path in sorted((realroot / 'lib/lean').glob('*.so*')):
        if path.is_file():
            abi_receipts.append(store_file(path, 'pinned-toolchain-shared-library-ABI', False))
    triplet = {'x86_64': 'x86_64-linux-gnu', 'aarch64': 'aarch64-linux-gnu'}.get(platform.machine())
    if triplet:
        for name in ['libc.so.6', 'libstdc++.so.6', 'libgcc_s.so.1']:
            for base in [Path('/lib') / triplet, Path('/usr/lib') / triplet]:
                path = base / name
                if path.is_file():
                    abi_receipts.append(store_file(path, 'native-system-library-ABI', False))
                    break
    import_sources: dict[str, dict] = {}
    source_commands: dict[str, list] = {}
    for c in commands:
        if c.get('tool') == 'lean':
            for a in c.get('input_args', []):
                if a.endswith('.lean'):
                    path = Path(a)
                    absolute = str((Path(c['cwd']) / path).resolve()) if not path.is_absolute() else str(path.resolve())
                    source_commands.setdefault(absolute, []).append(c)

    def allowed_file(path: Path) -> bool:
        try:
            resolved = path.resolve(strict=True)
            return resolved.is_file() and any(resolved.is_relative_to(base) for base in allowed_roots)
        except (FileNotFoundError, ValueError):
            return False

    def source_for(module: str) -> dict:
        if module in import_sources:
            return import_sources[module]
        relative = Path(*module.split('.')).with_suffix('.lean')
        matches = []
        if relative.as_posix() in sources:
            matches.append(('project', project / relative))
        for name, directory in package_roots:
            if (directory / relative).is_file():
                matches.append((name, directory / relative))
        core = realroot / 'src/lean' / relative
        if core.is_file():
            matches.append(('pinned-lean-toolchain', core))
        if len(matches) != 1:
            r = {'module': module, 'source_resolution_error': len(matches)}
            import_sources[module] = r
            return r
        name, path = matches[0]
        r = {'module': module, 'package': name,
             'source': store_file(path, 'actual-imported-module-source', copy_bytes=name == 'project')}
        if name not in ['project', 'pinned-lean-toolchain']:
            r['guarded_source_commands'] = source_commands.get(str(path.resolve()), [])
            if r['guarded_source_commands']:
                # Preserve coherent facets for package modules actually compiled in this run.
                directory = next(d for n, d in package_roots if n == name)
                r['built_package_facets'] = []
                for subdir in ['lib/lean', 'ir']:
                    stem = directory / '.lake/build' / subdir / relative.with_suffix('')
                    for facet in sorted(stem.parent.glob(stem.name + '.*')):
                        if facet.is_file() and not facet.is_symlink():
                            r['built_package_facets'].append(store_file(facet, 'guarded-built-package-facet'))
            else:
                r['origin'] = 'PINNED_EXISTING_DEPENDENCY_CACHE_REVERIFY_ON_RESTORE'
        import_sources[module] = r
        return r

    import_part_cache = {}
    native_library_captured = set()

    def references(setup: dict, context_root: Path = project) -> tuple[dict, list]:
        result = {}
        missing = []
        # Lean.Setup.ModuleSetup.importArts serializes a name map of nested path arrays.
        arts = setup.get('importArts', {})
        items = arts.items() if isinstance(arts, dict) else arts
        for name, arrays in items:
            flat = tuple(tuple(array) for array in arrays)
            context_key = str(context_root.resolve()) if any(not Path(p).is_absolute() for a in flat for p in a) else ''
            key = (str(name), context_key, flat)
            if key in import_part_cache:
                part_receipts, cached_missing = import_part_cache[key]
                result[str(name)] = part_receipts
                missing.extend(cached_missing)
                continue
            local_missing = []
            origin = source_for(str(name))
            part_receipts = []
            for array in arrays:
                for name_path in array:
                    path = Path(name_path)
                    if not path.is_absolute():
                        path = context_root / path
                    if not allowed_file(path):
                        local_missing.append(str(path))
                        continue
                    # Standard pinned cached dependency outputs are hash-bound and restored by
                    # their existing cache. All newly compiled/project and native import parts
                    # are copied, including cache-resolved IR outside the project directory.
                    is_core = path.resolve().is_relative_to(realroot) or path.resolve().is_relative_to(shadow)
                    is_existing_cache = origin.get('origin', '').startswith('PINNED_EXISTING_DEPENDENCY_CACHE')
                    receipt = store_file(path, 'actual-consumed-import-artifact', not (is_core or is_existing_cache))
                    part_receipts.append([str(path), receipt['sha256']])
            result[str(name)] = part_receipts
            if not part_receipts or not any(p[0].endswith('.olean') for p in part_receipts):
                local_missing.append('missing nonempty public olean for setup import ' + str(name))
            import_part_cache[key] = (part_receipts, local_missing)
            missing.extend(local_missing)
        for entry in setup.get('dynlibs', []) + setup.get('plugins', []):
            name = entry.get('path') if isinstance(entry, dict) else entry
            path = Path(name)
            if not path.is_absolute():
                path = context_root / path
            if str(path) in native_library_captured:
                continue
            if not allowed_file(path):
                missing.append(str(path))
            else:
                store_file(path, 'actual-consumed-dynlib-or-plugin', True)
                native_library_captured.add(str(path))
                # Retain the library's neighboring static/trace/hash facets when present.
                for facet in sorted(path.parent.glob(path.stem + '.*')):
                    if facet.is_file() and not facet.is_symlink() and allowed_file(facet):
                        store_file(facet, 'actual-native-library-coherent-facet', True)
        return result, missing

    def option_path(command: dict, option: str):
        values = []
        argv = command.get('input_args', [])
        for i, token in enumerate(argv):
            if token == option and i + 1 < len(argv):
                values.append(argv[i + 1])
            elif option.startswith('--') and token.startswith(option + '='):
                values.append(token[len(option) + 1:])
        if len(values) != 1:
            return None
        path = Path(values[0])
        return (Path(command['cwd']) / path).resolve() if not path.is_absolute() else path.resolve()

    def output_bound_commands(commands_for_source: list, stem: Path, ir_stem: Path,
                              setup_path: Path, is_module: bool) -> list:
        result = []
        for command in commands_for_source:
            if (option_path(command, '-o') != stem.with_suffix('.olean').resolve()
                    or option_path(command, '-i') != stem.with_suffix('.ilean').resolve()
                    or option_path(command, '--setup') != setup_path.resolve()):
                continue
            c_path = option_path(command, '-c')
            # Module-system compilation may defer C generation to guarded leanir.
            if c_path != ir_stem.with_suffix('.c').resolve() and not (is_module and c_path is None):
                continue
            result.append(command)
        return result

    def lake_descriptor_binding(output_descrs: dict, stem: Path, ir_stem: Path) -> list:
        # Lake's own sidecar hashes supplement the independent SHA256 receipt.
        # Missing sidecars are explicit; they never become fabricated hash matches.
        rows = []
        mapping = {'i': stem.with_suffix('.ilean'), 'rs': stem.with_suffix('.ir.sig'),
                   'r': stem.with_suffix('.ir'), 'c': ir_stem.with_suffix('.c'),
                   'b': ir_stem.with_suffix('.bc')}
        for key, path in mapping.items():
            if key in output_descrs:
                sidecar = Path(str(path) + '.hash')
                value = sidecar.read_text().strip() if sidecar.is_file() else None
                descriptor = output_descrs[key]
                rows.append({'part': key, 'path': str(path), 'descriptor': descriptor,
                             'sidecar_hash': value,
                             'matched': isinstance(descriptor, str) and value is not None
                             and descriptor.split('.', 1)[0] == value})
        for i, descriptor in enumerate(output_descrs.get('o', [])):
            if i >= 3:
                rows.append({'part': 'o', 'matched': False, 'unexpected_olean_part': i})
                continue
            path = stem.with_suffix(['.olean', '.olean.server', '.olean.private'][i])
            sidecar = Path(str(path) + '.hash')
            value = sidecar.read_text().strip() if sidecar.is_file() else None
            rows.append({'part': 'o', 'path': str(path), 'descriptor': descriptor,
                         'sidecar_hash': value,
                         'matched': isinstance(descriptor, str) and value is not None
                         and descriptor.split('.', 1)[0] == value})
        return rows

    # Capture root facets in full; unsuccessful/partial files are retained but never eligible.
    # Package outputs are reached through actual setup import/plugin references below.
    build_root = project / '.lake/build'
    if build_root.exists():
        for path in sorted(build_root.rglob('*')):
            if path.is_file() and not path.is_symlink():
                store_file(path, 'root-build-output-unclassified')

    module_records = []
    for name in manifest['targets'][0]['closure_modules']:
        rel = Path(*name.split('.'))
        lean_dir = build_root / 'lib/lean'
        stem = lean_dir / rel
        trace_path = stem.with_suffix('.trace')
        setup_path = (build_root / 'ir' / rel).with_suffix('.setup.json')
        r = {'module': name, 'source': sources[name.replace('.', '/') + '.lean'],
             'completed_guarded_compile_candidate': False, 'kernel_verified': False,
             'restore_requires_new_exact_import_and_ABI_validation': True}
        if not trace_path.is_file() or not setup_path.is_file():
            r['classification'] = 'MISSING_COMPLETED_TRACE_OR_SETUP_NOT_REUSABLE'
            module_records.append(r)
            continue
        try:
            trace = json_file(trace_path)
            setup = json_file(setup_path)
            if not isinstance(trace, dict) or not isinstance(setup, dict):
                raise ValueError('Unexpected trace/setup JSON schema')
        except (ValueError, OSError) as e:
            r['classification'] = 'INVALID_OR_PARTIAL_TRACE_NOT_REUSABLE'
            r['diagnostic'] = str(e)
            module_records.append(r)
            continue
        r['trace'] = store_file(trace_path, 'completed-or-partial-Lake-trace')
        r['setup'] = store_file(setup_path, 'compiler-module-setup')
        r['lake_depHash'] = trace.get('depHash')
        r['lake_input_count'] = len(trace.get('inputs', []))
        r['lake_outputs'] = trace.get('outputs')
        source_abs = str((project / (name.replace('.', '/') + '.lean')).resolve())
        ir_stem = build_root / 'ir' / rel
        matching_commands = output_bound_commands(source_commands.get(source_abs, []),
                                                  stem, ir_stem, setup_path, setup.get('isModule', False))
        r['guarded_source_commands'] = matching_commands
        try:
            actual_imports, missing = references(setup, Path(matching_commands[0]['cwd']) if matching_commands else project)
        except (ValueError, TypeError, KeyError, OSError) as e:
            r['classification'] = 'UNRECOGNIZED_SETUP_ARTIFACT_SCHEMA_NOT_REUSABLE'
            r['diagnostic'] = str(e)
            module_records.append(r)
            continue
        r['actual_import_count'] = len(actual_imports)
        r['actual_import_map_sha256'] = hashlib.sha256(json.dumps(actual_imports, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        # The copied raw setup contains the exact map. File/source receipts are normalized
        # globally to avoid repeating the full Mathlib import closure hundreds of times.
        r['missing_actual_import_artifacts'] = missing
        expected = (next(f['imports'] for f in manifest['files'] if f['module'] == name)
                    if name != 'T01Audit' else
                    ['ImbalancedChen.P5OriginalFullFifthFloorIntegral', 'Lean.Util.CollectAxioms'])
        expected_noncore = [n for n in expected if n.split('.')[0] not in ['Lean', 'Init', 'Std']]
        r['missing_expected_direct_imports'] = [n for n in expected_noncore if n not in actual_imports]
        required = [stem.with_suffix('.olean'), stem.with_suffix('.ilean'),
                    (build_root / 'ir' / rel).with_suffix('.c')]
        if setup.get('isModule'):
            required += [stem.with_suffix(x) for x in ['.olean.server', '.olean.private', '.ir.sig', '.ir']]
        output_descrs = trace.get('outputs')
        r['trace_output_descriptor_sidecar_checks'] = lake_descriptor_binding(output_descrs, stem, ir_stem) if isinstance(output_descrs, dict) else []
        descriptor_contradiction = any(row.get('sidecar_hash') is not None and not row['matched']
                                       for row in r['trace_output_descriptor_sidecar_checks'])
        r['observed_output_descriptor_contradiction'] = descriptor_contradiction
        r['trace_outputs_require_verified_cryptographic_rebind_before_restore'] = True
        if isinstance(output_descrs, dict) and output_descrs.get('b') is not None:
            required.append((build_root / 'ir' / rel).with_suffix('.bc'))
        r['required_output_parts'] = [str(path) for path in required]
        completed_trace = (trace.get('schemaVersion') == '2025-09-10'
                           and trace.get('synthetic') is False
                           and isinstance(output_descrs, dict)
                           and all(k in output_descrs for k in ['o', 'i', 'c'])
                           and bool(trace.get('depHash')))
        source_resolution_ok = all('source_resolution_error' not in import_sources[n] for n in actual_imports)
        good = (runtime_ok and package_ok and completed_trace and bool(matching_commands)
                and setup.get('name') == name and not missing and not r['missing_expected_direct_imports'] and source_resolution_ok
                and not descriptor_contradiction
                and all(path.is_file() and path.stat().st_size > 0 for path in required))
        r['completed_guarded_compile_candidate'] = good
        r['classification'] = 'COMPILED_CHECKPOINT_ONLY_NOT_KERNEL_ACCEPTANCE' if good else 'QUARANTINED_PARTIAL_OR_UNBOUND_OUTPUTS'
        module_records.append(r)

    # Preserve all package modules actually compiled under the guard, including Cache.*
    # modules built during cache acquisition that no completed root setup imports.
    package_compilations = []
    package_bin_roots = set()
    for source_name, source_runs in source_commands.items():
        source_path = Path(source_name)
        matches = [(n, d) for n, d in package_roots if source_path.is_relative_to(d)]
        if len(matches) != 1:
            continue
        package_name, directory = matches[0]
        package_bin_roots.add(directory / '.lake/build/bin')
        for command in source_runs:
            setup_path = option_path(command, '--setup')
            entry = {'package': package_name,
                     'source': store_file(source_path, 'guarded-built-package-source'),
                     'command': command, 'kernel_verified': False,
                     'restore_requires_new_exact_import_and_ABI_validation': True}
            if setup_path is None or not setup_path.is_file():
                entry['classification'] = 'PACKAGE_COMMAND_WITHOUT_SETUP_NOT_REUSABLE'
                package_compilations.append(entry)
                continue
            try:
                setup = json_file(setup_path)
                name = setup['name']
                rel = Path(*name.split('.'))
                stem = directory / '.lake/build/lib/lean' / rel
                ir_stem = directory / '.lake/build/ir' / rel
                entry['module'] = name
                entry['setup'] = store_file(setup_path, 'guarded-built-package-setup')
                entry['facet_files'] = []
                for prefix in [stem, ir_stem]:
                    for facet in sorted(prefix.parent.glob(prefix.name + '.*')):
                        if facet.is_file() and not facet.is_symlink():
                            entry['facet_files'].append(store_file(facet, 'guarded-built-package-coherent-facet'))
                imports, missing = references(setup, Path(command['cwd']))
                entry['actual_import_count'] = len(imports)
                entry['actual_import_map_sha256'] = hashlib.sha256(json.dumps(imports, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
                entry['missing_actual_import_artifacts'] = missing
                entry['output_bound_command'] = bool(output_bound_commands([command], stem, ir_stem, setup_path, setup.get('isModule', False)))
                trace_path = stem.with_suffix('.trace')
                trace = json_file(trace_path) if trace_path.is_file() else {}
                entry['lake_completed_trace'] = (isinstance(trace, dict) and trace.get('schemaVersion') == '2025-09-10'
                                                  and trace.get('synthetic') is False and isinstance(trace.get('outputs'), dict))
                checks = lake_descriptor_binding(trace.get('outputs', {}), stem, ir_stem) if entry['lake_completed_trace'] else []
                entry['trace_output_descriptor_sidecar_checks'] = checks
                contradiction = any(row.get('sidecar_hash') is not None and not row['matched'] for row in checks)
                required = [stem.with_suffix('.olean'), stem.with_suffix('.ilean'), ir_stem.with_suffix('.c')]
                if setup.get('isModule'):
                    required += [stem.with_suffix(x) for x in ['.olean.server', '.olean.private', '.ir.sig', '.ir']]
                descriptors = trace.get('outputs', {}) if isinstance(trace, dict) else {}
                if isinstance(descriptors, dict) and descriptors.get('b') is not None:
                    required.append(ir_stem.with_suffix('.bc'))
                entry['required_output_parts'] = [str(path) for path in required]
                import_sources_bound = all('source_resolution_error' not in import_sources[n] for n in imports)
                completed = (runtime_ok and package_ok and entry['lake_completed_trace']
                             and entry['output_bound_command'] and bool(imports) and import_sources_bound
                             and not missing and not contradiction
                             and all(path.is_file() and path.stat().st_size > 0 for path in required))
                entry['classification'] = ('PACKAGE_COMPILE_CHECKPOINT_REQUIRES_VERIFIED_REBIND'
                                           if completed else 'PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED')
            except (ValueError, KeyError, TypeError, OSError) as e:
                entry['classification'] = 'PACKAGE_PARTIAL_OUTPUTS_QUARANTINED'
                entry['diagnostic'] = str(e)
            package_compilations.append(entry)
    for directory in sorted(package_bin_roots):
        if directory.is_dir():
            for path in sorted(directory.rglob('*')):
                if path.is_file() and not path.is_symlink():
                    store_file(path, 'guarded-built-package-binary-or-link-facet')

    # One final uncached rehash checks that the after-build snapshot stayed stable.
    # No repeated per-import filesystem/journal work is needed for identical maps.
    changed = []
    for path, receipt in files.items():
        if Path(path) == logs / 'checkpoint-collection.log':
            continue  # Collection's own tee log is intentionally still being written.
        try:
            resolved = Path(path).resolve(strict=True)
            if (str(resolved) != receipt['resolved_path'] or resolved.stat().st_size != receipt['bytes']
                    or sha(resolved) != receipt['sha256']):
                changed.append(path)
        except OSError:
            changed.append(path)
    if changed:
        issues.extend('file changed during checkpoint collection: ' + path for path in changed)
        for r in module_records:
            r['completed_guarded_compile_candidate'] = False
            r['classification'] = 'QUARANTINED_SNAPSHOT_MUTATION'
        for r in package_compilations:
            r['classification'] = 'PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED'

    result = {
        'schema': 't01-coherent-build-checkpoint-v3',
        'status': 'PRESERVED_BYTES_WITH_PER_MODULE_CLASSIFICATION',
        'source_commit': os.environ['SOURCE_COMMIT'],
        'run_id': os.environ['GITHUB_RUN_ID'], 'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'],
        'manifest_sha256': digest(args.manifest), 'source_identity_sha256': manifest['targets'][0]['source_identity_sha256'],
        'runtime_audit_valid': runtime_ok, 'all_dependency_source_pins_valid': package_ok,
        'runtime_state': state, 'packages': packages,
        'platform': {'machine': platform.machine(), 'system': platform.system(),
                     'image_os': os.getenv('ImageOS'), 'image_version': os.getenv('ImageVersion'),
                     'os_release': Path('/etc/os-release').read_text() if Path('/etc/os-release').is_file() else None},
        'native_and_toolchain_library_ABI_receipts': abi_receipts,
        'sources_and_data': sources, 'modules': module_records, 'files': files,
        'actual_import_sources': import_sources,
        'all_guarded_package_compilations': package_compilations,
        'completed_compile_candidates': sum(r['completed_guarded_compile_candidate'] for r in module_records),
        'saved_unique_payload_blobs': len(list(objects.iterdir())),
        'issues': issues, 'green': False,
        'restore_policy': 'Never restore quarantine entries; independently compare exact source/data/runtime/flags/import-artifact/ABI identities and all outputs before loading any object. Rerun exact798 kernel modules (797 mathematical suppliers plus1 actually built audit wrapper) and complete strict Y18 serialized/types/axioms/17-dual-report gates. Canonical888 are source/object bound dependencies, not individually declaration-audited.'}
    destination = args.output / 'CHECKPOINT.json'
    destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    summary = {'status': result['status'], 'completed_compile_candidates': result['completed_compile_candidates'],
               'module_count': len(module_records), 'payload_blobs': result['saved_unique_payload_blobs'],
               'checkpoint_sha256': sha(destination), 'green': False}
    (logs / 'CHECKPOINT_SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        # The always-upload step still receives the raw files already copied above,
        # plus an explicit failure receipt. No such artifact is accepted for reuse.
        try:
            destination = Path(sys.argv[sys.argv.index('--output') + 1])
            destination.mkdir(parents=True, exist_ok=True)
            receipt = {'status': 'CHECKPOINT_COLLECTION_FAILED_RAW_BYTES_QUARANTINED',
                       'error_type': type(exc).__name__, 'error': str(exc),
                       'source_commit': os.getenv('SOURCE_COMMIT'), 'run_id': os.getenv('GITHUB_RUN_ID'),
                       'run_attempt': os.getenv('GITHUB_RUN_ATTEMPT'), 'kernel_verified': False,
                       'restore_accepted': False, 'raw_path_index': 'RAW_FILES.jsonl',
                       'raw_snapshot_acquisition_complete': (destination / 'SNAPSHOT_ACQUISITION.json').is_file(),
                       'interrupted_journal_last_line_may_be_partial': True}
            (destination / 'CHECKPOINT_FAILURE.json').write_text(json.dumps(receipt, indent=2) + '\n')
        except Exception:
            pass
        raise
