#!/usr/bin/env python3
"""Extract public, previously accepted proof blocks; never write live sources."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
MEMBER = Path('/workspace/blue-member-build')
NATIVE = MEMBER / '.lake/packages/goldbach'
PRIOR = Path('/workspace/blue-member-static-omega')
COMMIT = '9d4c3a4010d42aedd9e7231bf94386019cfffccc'
EXT_MODULE = 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformFixedCompat'
EXT_PATH = EXT_MODULE.replace('.', '/') + '.lean'
CONSUMER = 'MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabUniform'
CONSUMER_PATH = CONSUMER.replace('.', '/') + '.lean'
EXPECTED = {
    'LiLiuPrereqBuchstabUniformAbel': (
        '51a5ac728e115811f9abffb02e15df8db8fcf0fc0da1124fdf4d61f12c240563',
        '5f0e6fee5e31a2b0b5abf46c279985753b98e7820a22e0318387c392aaa1ec35'),
    'LiLiuPrereqBuchstabBands': (
        'bfc465b9e55d597afeac1e2485dad992c591a30d2089ddc9ac7b738d63930350',
        'd49e99a507bf9b1ac228b2809d8e70682467a54447701859cf8a1e48e964be62'),
    'LiLiuPrereqBuchstabUniform': (
        '9b8f109fc3f3ac21cb20db707f1e19e68ba86ad5568f547a72c3189ec18c242e',
        'd3653d3586d0f4130b14a2fbfb4370eb92666240f66e987b864e8ac5af2c7ec2'),
}
PLAN = [
    ('LiLiuPrereqBuchstabUniformAbel', 'kernel_range', 'existing_private_helper'),
    ('LiLiuPrereqBuchstabUniformAbel', 'kernel_hasDerivAt_on_band', 'existing_private_helper'),
    ('LiLiuPrereqBuchstabUniformAbel', 'kernel_endpoint_le', 'existing_private_helper'),
    ('LiLiuPrereqBuchstabUniformAbel', 'abs_shift_mul_buchstabSlope_le_two', 'published_new_public'),
    ('LiLiuPrereqBuchstabUniformAbel', 'abs_buchstabPrimeKernelSlope_le_unrestricted', 'published_new_public'),
    ('LiLiuPrereqBuchstabUniformAbel', 'abs_buchstabPrimeKernelSlope_le_coarse', 'published_new_private'),
    ('LiLiuPrereqBuchstabUniformAbel', 'integrableOn_buchstabPrimeKernelSlope_unrestricted', 'published_new_public'),
    ('LiLiuPrereqBuchstabUniformAbel', 'buchstabPrimeKernel_sum_Ioc_error_le_unrestricted', 'published_new_public'),
    ('LiLiuPrereqBuchstabUniformAbel', 'buchstabPrimeKernel_sum_Ico_error_le_unrestricted', 'published_new_public'),
    ('LiLiuPrereqBuchstabBands', 'bands_pos', 'existing_private_helper'),
    ('LiLiuPrereqBuchstabBands', 'buchstab_main_decomposition', 'existing_private_helper'),
    ('LiLiuPrereqBuchstabBands', 'roughCount_base_band_error', 'existing_private_helper'),
    ('LiLiuPrereqBuchstabBands', 'roughCount_buchstab_band_error_unrestricted', 'published_new_public'),
    ('LiLiuPrereqBuchstabUniform', 'rpow_cutoff_bounds_fixed', 'published_new_public'),
    ('LiLiuPrereqBuchstabUniform', 'roughCount_relative_band_error_fixed', 'published_new_public'),
    ('LiLiuPrereqBuchstabUniform', 'roughCount_uniform_error_bound_fixed', 'published_new_public'),
    ('LiLiuPrereqBuchstabUniform', 'tendsto_uniform_buchstab_majorant_fixed', 'published_new_public'),
    ('LiLiuPrereqBuchstabUniform', 'roughCount_uniform_buchstab_fixed', 'published_new_public'),
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_bytes(path):
    return subprocess.check_output(['git', '-C', str(NATIVE), 'show', COMMIT + ':' + path])


def blob(path):
    return subprocess.check_output(['git', '-C', str(NATIVE), 'rev-parse',
                                    COMMIT + ':' + path], text=True).strip()


def put(relative, data):
    """Idempotently write only this candidate artifact directory."""
    path = ROOT / relative
    assert path.resolve().is_relative_to(ROOT)
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == data, 'refuse to replace differing candidate: ' + str(path)
    else:
        path.write_bytes(data)


def declaration(data, name):
    lines = data.splitlines(keepends=True)
    starts = [i for i, row in enumerate(lines) if re.match(
        rb'^(?:private )?theorem ' + name.encode() + rb'(?:\s|\{)', row)]
    assert len(starts) == 1, name
    first = starts[0]
    end = first + 1
    # Every selected declaration has its signature/proof indented after line 1.
    # Stop at the next top-level comment, declaration, or namespace command.
    while end < len(lines):
        row = lines[end]
        if row.strip() and row[:1] not in (b' ', b'\t'):
            break
        end += 1
    while end > first and not lines[end - 1].strip():
        end -= 1
    start_byte = sum(map(len, lines[:first]))
    end_byte = sum(map(len, lines[:end]))
    block = data[start_byte:end_byte]
    assert block.endswith(b'\n') and b':= by\n' in block
    assert len(re.findall(rb'(?m)^(?:private )?theorem ', block)) == 1
    return block, start_byte, end_byte, first + 1, end


def main():
    sources = {}
    boundaries = []
    legacy_names = set()
    for stem, (published_sha, old_sha) in EXPECTED.items():
        rel = 'MathlibNt/SieveTheory/' + stem + '.lean'
        public_path = 'research/wu2008/src/' + rel
        published = git_bytes(public_path)
        old = (NATIVE / rel).read_bytes()
        assert sha(published) == published_sha and sha(old) == old_sha
        snapshot = 'upstream/' + public_path
        put(snapshot, published)
        old_snapshot = 'baseline/' + rel
        put(old_snapshot, old)
        boundaries.append({'label': 'legacy_cap100_provider:' + stem,
                           'live_path': str(NATIVE / rel), 'snapshot': old_snapshot,
                           'sha256': old_sha, 'must_remain_byte_exact': True})
        sources[stem] = {'data': published, 'old': old, 'path': public_path,
                         'snapshot': snapshot, 'blob_sha1': blob(public_path),
                         'sha256': published_sha}
        legacy_names.update(re.findall(rb'(?m)^theorem\s+(\w+)', old))
    for stem in ['LiLiuPrereqBuchstabPrimeSums', 'LiLiuPrereqBuchstabBounds',
                 'LiLiuPrereqBuchstabIntegral', 'LiLiuPrereqBuchstabBaseEstimate']:
        rel = 'MathlibNt/SieveTheory/' + stem + '.lean'
        old = (NATIVE / rel).read_bytes()
        public_path = 'research/wu2008/src/' + rel
        assert git_bytes(public_path) == old
        snapshot = 'baseline/' + rel
        put(snapshot, old)
        boundaries.append({'label': 'external_supplier:' + stem,
                           'live_path': str(NATIVE / rel), 'snapshot': snapshot,
                           'sha256': sha(old), 'published_source_path': public_path,
                           'published_blob_sha1': blob(public_path),
                           'must_remain_byte_exact': True})
    for label, path in [('member_toolchain', MEMBER / 'lean-toolchain'),
                        ('member_lake_manifest', MEMBER / 'lake-manifest.json'),
                        ('native_toolchain', NATIVE / 'lean-toolchain'),
                        ('native_lake_manifest', NATIVE / 'lake-manifest.json')]:
        data = path.read_bytes()
        snapshot = 'baseline/pins/' + label + path.suffix
        put(snapshot, data)
        boundaries.append({'label': label, 'live_path': str(path),
                           'snapshot': snapshot, 'sha256': sha(data),
                           'must_remain_byte_exact': True})
    header = (
        'import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform\n\n'
        '/-!\n'
        'Fixed-cap compatibility extension, extracted from published research\n'
        'proofs at subfish-zhou/goldbach-lean commit\n' + COMMIT + '.\n'
        'The existing cap-100 providers remain unchanged. Exact source ranges\n'
        'and proof hashes are recorded in the accompanying overlay manifest.\n'
        '-/\n\n'
        'set_option autoImplicit false\n\n'
        'open Set MeasureTheory Filter\n'
        'open scoped BigOperators Topology\n\n'
        'namespace LiLiuPrereqBuchstab\n\n'
    ).encode()
    extension = bytearray(header)
    rows = []
    for stem, name, role in PLAN:
        source = sources[stem]
        block, first, last, first_line, last_line = declaration(source['data'], name)
        if role == 'existing_private_helper':
            assert declaration(source['old'], name)[0] == block
        else:
            assert not re.search(rb'(?m)^(?:private )?theorem ' + name.encode() +
                                 rb'(?:\s|\{)', source['old'])
        comment = ('-- Published source: ' + source['path'] + ':' + str(first_line) +
                   '-' + str(last_line) + '\n').encode()
        extension.extend(comment)
        candidate_start = len(extension)
        extension.extend(block)
        candidate_end = len(extension)
        extension.extend(b'\n')
        split = block.index(b':=') + 2
        visibility = 'private' if block.startswith(b'private ') else 'public'
        rows.append({'name': name, 'qualified_public_name':
                     'LiLiuPrereqBuchstab.' + name if visibility == 'public' else None,
                     'visibility': visibility, 'role': role,
                     'source_repository': 'https://github.com/subfish-zhou/goldbach-lean',
                     'source_public_commit': COMMIT, 'source_path': source['path'],
                     'source_blob_sha1': source['blob_sha1'],
                     'source_file_sha256': source['sha256'],
                     'source_snapshot': source['snapshot'],
                     'source_byte_range_half_open': [first, last],
                     'source_lines_inclusive': [first_line, last_line],
                     'declaration_sha256': sha(block),
                     'header_sha256': sha(block[:split]),
                     'proof_body_sha256': sha(block[split:]),
                     'candidate_byte_range_half_open': [candidate_start, candidate_end],
                     'declaration_and_proof_body_byte_exact': True,
                     'old_private_helper_also_byte_exact_to_current_provider':
                     role == 'existing_private_helper'})
    extension.extend(b'end LiLiuPrereqBuchstab\n')
    ext_bytes = bytes(extension)
    ext_candidate = 'overlay/' + EXT_PATH
    put(ext_candidate, ext_bytes)
    assert not (NATIVE / EXT_PATH).exists(), 'proposed new module already exists live'
    baseline = (NATIVE / CONSUMER_PATH).read_bytes()
    assert len(baseline) == 4333 and sha(baseline) == (
        '29294b01f78b188a399877d30b1329a85c2f3fa3442efa5cb1111552258e97cf')
    public_consumer = git_bytes('research/wu2008/src/' + CONSUMER_PATH)
    assert public_consumer == baseline
    prefix = ('import ' + EXT_MODULE + '\n').encode()
    consumer = prefix + baseline
    consumer_baseline = 'baseline/' + CONSUMER_PATH
    consumer_candidate = 'overlay/' + CONSUMER_PATH
    put(consumer_baseline, baseline)
    put(consumer_candidate, consumer)
    provenance = (PRIOR / 'NATIVE_SUPPLIER_PROVENANCE.json').read_bytes()
    put('evidence/PRIOR_PUBLISHED_SUPPLIER_PROVENANCE.json', provenance)
    focus = (PRIOR / 'remote-main-supplier/FOCUSED_PRODUCTION_BINDINGS.json').read_bytes()
    put('evidence/PUBLISHED_FOCUSED_PRODUCTION_BINDINGS.json', focus)
    evidence_files = []
    for file in ['validation.json', 'classical-acceptance.json',
                 'literal_and_five_axiom_reports.log',
                 'fresh_production_final_kernel.log',
                 'full_cached_receipt_verification.log']:
        data = (PRIOR / 'remote-main-supplier/research/wu-structural-compression-audit' / file).read_bytes()
        target = 'evidence/published-acceptance/' + file
        put(target, data)
        evidence_files.append({'path': target, 'sha256': sha(data)})
    fixed = next(r for r in rows if r['name'] == 'roughCount_uniform_buchstab_fixed')
    sf = ROOT / fixed['source_snapshot']
    a, b = fixed['source_byte_range_half_open']
    interface = sf.read_bytes()[a:b].split(b':=', 1)[0].decode().rstrip()
    manifest = {
        'schema': 'published-generic-M-independent-extension-overlay-v1',
        'status': 'UNCOMPILED_STATIC_CANDIDATE',
        'scope': 'Only new native compat extension and one import prefix on native Omega consumer; no project/main/P6/pin/provider edits',
        'published_repository': 'https://github.com/subfish-zhou/goldbach-lean',
        'published_commit': COMMIT,
        'native_base_commit_retained': '09b97db5764ade1246bfb77206baa1b124760958',
        'lean_toolchain_retained': 'leanprover/lean4:v4.33.0-rc1',
        'mathlib_revision_retained': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
        'extension': {'module': EXT_MODULE, 'candidate_path': ext_candidate,
                      'sha256': sha(ext_bytes), 'bytes': len(ext_bytes),
                      'lines': ext_bytes.count(b'\n'),
                      'imports': ['MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform'],
                      'public_declarations': 11, 'private_declarations': 7,
                      'existing_private_helpers_included_in_private_count': 6},
        'consumer': {'module': CONSUMER, 'baseline_snapshot': consumer_baseline,
                     'candidate_path': consumer_candidate,
                     'baseline_sha256': sha(baseline), 'candidate_sha256': sha(consumer),
                     'baseline_bytes': len(baseline), 'candidate_bytes': len(consumer),
                     'new_import_prefix': prefix.decode(),
                     'original_bytes_preserved_as_exact_suffix': True},
        'overlay': [
            {'module': EXT_MODULE, 'candidate_path': ext_candidate,
             'destination': str(NATIVE / EXT_PATH), 'repository_relative_path': EXT_PATH,
             'operation': 'create_missing_only', 'expected_existing': 'absent',
             'candidate_sha256': sha(ext_bytes)},
            {'module': CONSUMER, 'candidate_path': consumer_candidate,
             'destination': str(NATIVE / CONSUMER_PATH),
             'repository_relative_path': CONSUMER_PATH,
             'operation': 'replace_exact_baseline_only',
             'expected_existing_sha256': sha(baseline),
             'candidate_sha256': sha(consumer)},
        ],
        'declarations': rows,
        'legacy_provider_public_names': sorted(n.decode() for n in legacy_names),
        'unchanged_boundaries': boundaries,
        'actual_published_interface': interface,
        'quantifier_order': 'M>=2,u0>1,epsilon>0 precede X; X precedes x>=X and all u in [u0,M]; consumer k,delta choose u0,M before N/source boxes/prime labels',
        'copied_proof_identity': 'Each declaration header and body is a byte-exact contiguous slice of one of three published research files. Six old private slices also match the existing old provider bytes.',
        'new_mathematical_definitions': [],
        'no_live_source_or_output_mutations_performed': True,
        'compiler_kernel_or_axiom_audits_run_here': False,
        'existing_acceptance_evidence': evidence_files,
        'prior_provenance_path': 'evidence/PRIOR_PUBLISHED_SUPPLIER_PROVENANCE.json',
        'prior_provenance_sha256': sha(provenance),
        'prior_focused_production_bindings_path': 'evidence/PUBLISHED_FOCUSED_PRODUCTION_BINDINGS.json',
        'prior_focused_production_bindings_sha256': sha(focus),
        'acceptance_limit': 'Published records bind full original research sources and individual receipt hashes; individual receipt payloads/objects are not published. The new extension composition needs fresh guarded local compilation/kernel/all-public-type+axiom validation by its owner.',
    }
    put('OVERLAY_MANIFEST.json', (json.dumps(manifest, indent=2) + '\n').encode())
    with (ROOT / 'PROGRESS.md').open('a') as f:
        f.write('\nStatic verifier RED: exit 1, missing candidate manifest (expected).\n')
        f.write('Extraction complete: 18 contiguous published slices, no proof edits; '
                'all six old private helper slices also match current old providers.\n')
    print(json.dumps({'status': manifest['status'], 'extension_sha256': sha(ext_bytes),
                      'extension_lines': ext_bytes.count(b'\n'), 'extension_bytes': len(ext_bytes),
                      'consumer_sha256': sha(consumer), 'declarations': len(rows)}, indent=2))


if __name__ == '__main__':
    main()
