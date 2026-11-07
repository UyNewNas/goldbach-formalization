#!/usr/bin/env python3
"""Check frozen Part 2 source identities, exact decoding and adopted ledgers.

Usage:
  python verification/part2/audit_adopted_catalog.py --source-root PATH

PATH is a checkout or exact file snapshot of chen-imbalanced-semiprimes at
ba6ec11d800eccc54406490631895e174de85766. No network, external Python
packages, Lean execution, source edits, or historical quadratures are used.
This audit does not prove an integral inequality. If a .git entry exists,
its HEAD must also equal the frozen SHA; all listed file bytes are checked.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess

FROZEN_SHA = 'ba6ec11d800eccc54406490631895e174de85766'
BASE_SHA = '1a80c1bcce67886f699d097fc37fd245cd3620bf'
ROW_COLUMNS = ['group', 't_index', 'u_index', 'exact_Z',
               'discarded_floor_Q80', 'extra_lower_Q160', 'extra_upper_Q160']


def require(test, message):
    if not test:
        raise ValueError(message)


def digest(content):
    return hashlib.sha256(content).hexdigest()


def git_blob(content):
    header = b'blob ' + str(len(content)).encode() + b'\0'
    return hashlib.sha1(header + content).hexdigest()


def rational_field(value, path):
    for key in path.split('.'):
        value = value[key]
    return F(value)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--catalog', type=Path,
                        default=Path(__file__).resolve().parents[2] /
                        'docs/part2/adopted-evidence-catalog.json')
    parser.add_argument('--output', type=Path,
                        help='Optional exact-audit report; never writes source files.')
    args = parser.parse_args()
    root = args.source_root.resolve()
    catalog = json.loads(args.catalog.read_text(encoding='utf-8'))
    require(catalog['manuscript_frozen_sha'] == FROZEN_SHA, 'catalog manuscript SHA')
    require(catalog['formalization_base_sha'] == BASE_SHA, 'catalog formalization SHA')
    head_checked = False
    if (root / '.git').exists():
        head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
        require(head == FROZEN_SHA, 'source checkout is not at the frozen commit')
        head_checked = True

    hashes = {}
    for item in catalog['downloaded_sources']:
        path = root / item['path']
        content = path.read_bytes()
        require(len(content) == item['size'], f'source byte size: {item["path"]}')
        require(digest(content) == item['sha256'], f'source SHA256: {item["path"]}')
        require(git_blob(content) == item['git_blob_sha1'], f'source Git blob: {item["path"]}')
        hashes[item['path']] = item

    def read(name):
        return json.loads((root / name).read_text(encoding='utf-8-sig'))

    def data(name):
        return read('verification/data/' + name)

    checked_manifest = 0
    for item in read('verification/manifest.json')['files']:
        key = 'verification/' + item['name']
        if key in hashes:
            require(hashes[key]['sha256'] == item['sha256'], f'compact manifest: {key}')
            require(hashes[key]['size'] == item['size'], f'compact manifest size: {key}')
            checked_manifest += 1

    baseline = data('global-selected-numeric-completion-20261010.json')
    assembly = data('corpus-renewal-improvement-assembly-20261010.json')
    current = assembly['selected_result']
    paired = data('corpus-renewal-paired-certificate-v2-20261010.json')
    old = data('positive-pair-deletion-certificate-20261010.json')
    zero = data('paired-y6-y11-zero-strip-certificate-20261010.json')
    K, c = F(current['safe_K']), F(current['safe_c'])
    require(K == F(8452171, 1250000) and c == F(49044063, 25000000), 'selected constants')
    require(assembly['selected_version'] == '7/3 v2 replaces12/5 candidate; gains not added together', 'selected version')
    require(not assembly['external_Li19728_restored'], 'withdrawn branch must remain excluded')

    savings = baseline['selected_upper_direct_savings']
    require(len(savings) == 22, 'upper saving count')
    for row in savings:
        require(rational_field(data(row['source']), row['field']) == F(row['value']),
                'adopted upper source field: ' + row['id'])
    coarse = savings[4]
    require(coarse['id'] == 'above_mu_second_coarse_only' and
            coarse['field'] == 'no_grid_coarse_lower', 'A5 selected coarse policy')
    require(F(coarse['value']) == F(3, 95000) + F(32, 3042147), 'A5 rational addition')
    upper_parts = baseline['selected_upper_direct_base']
    ext = data('certify_extended_prefix.json')
    require(F(upper_parts['ordinary_root']) == 4 / F(ext['theta']), 'ordinary root')
    require(F(upper_parts['first_integral']) == F(ext['first_integral_upper_exact']), 'first integral source')
    require(F(upper_parts['compact_third']) == F(ext['third_integral_upper_exact']), 'compact third source')
    require(F(upper_parts['complete_small_third_tail']) ==
            F(data('numerical-primitive-adversarial-20261009.json')['independent_tail_upper_Q112']), 'full replacement tail source')
    E = sum(map(F, upper_parts.values()), F(0)) - sum((F(r['value']) for r in savings), F(0))
    U = F(baseline['upper_budget_each'])
    require(E == F(current['new_upper_raw_endpoint']), 'upper raw endpoint')
    require(U == F(current['upper_density_approximation_budget']) == F(current['upper_compiler_budget']), 'two upper reserves')
    require(U == F(current['retained_upper_density_budget']) + F(current['additional_upper_budget_each']), 'upper density reserve components')
    require(U == F(current['retained_upper_compiler_budget']) + F(current['additional_upper_budget_each']), 'upper compiler reserve components')
    require(E + 2 * U == F(current['upper_after_all_budgets']), 'upper after reserves')
    require(K - E - 2 * U == F(current['remaining_upper_slack']) > 0, 'upper slack')

    Q = 2**80
    source_terms = data('sharp-248-baseline-128.json')['terms']
    pair_terms = data('independent-sharp-248-pair512-replay-20261008.json')['selected_lower']
    switch_terms = data('sharp-switch-midpoint-1024.json')['terms']
    direct_terms = baseline['direct_lower_terms']
    for name, term in direct_terms.items():
        if name in ['L1', 'L2', 'U3', 'U4']:
            side = 'lower' if name.startswith('L') else 'upper'
            s = source_terms[name]
            value = F(int(s[side + '_numerator']), int(s['denominator']))
        elif name in ['L5', 'L6']:
            value = F(pair_terms[name])
        elif name in ['U7', 'U8', 'U9']:
            s = switch_terms[name]
            value = F(int(s['upper_numerator']), int(s['denominator']))
        else:
            require(name == 'U10_plus_U11', 'unrecognized lower term')
            value = F(data('sharp-248-four-min-48.json')['U10_U11_cost_upper'])
        require(F(term['endpoint']) == value, 'signed root source field: ' + name)
    eleven = sum((F(t['endpoint']) * t['weight'] for t in direct_terms.values()), F(0)) / 4
    require(eleven == F(baseline['direct_lower_initial_eleven']), 'eleven-term root')
    priority = data('four-min-priority40000-independent-20261009.json')
    require((priority['all_parents'], priority['all_children']) == (40000, 516779), 'priority coverage counts')
    anchor = data('lower-start-convex-corner-transfer-independent-review.json')
    ordinary, removed = F(anchor['independent_ordinary_interval'][0]), F(anchor['independent_removed_H248_interval'][1])
    require(ordinary == F(baseline['ordinary_start_change_lower']), 'ordinary start change')
    require(removed == F(baseline['removed_H248_upper']), 'full obsolete correction')
    lower_selected = data('lower-start-method-coverage-20261009.json')['selected_result']
    weighted_I = F(0)
    for name, value in baseline['lower_selected_integrals'].items():
        require(F(value) == F(lower_selected[name]), 'selected lower integral: ' + name)
        weighted_I += F(value) * (3 if name.endswith('_a') else 1)
    restoration = F(data('lower-fourth-restoration-slanted-independent-20261009.json')['author_lower_covered'])
    require(restoration == F(baseline['restoration_L2_lower']), 'selected restoration')
    base = eleven + F(priority['coefficient_gain_lower']) + (ordinary - removed + weighted_I + restoration) / 4
    require(base == F(baseline['direct_raw_at_K0']), 'lower base direct reconstruction')
    base_selected = F(data('slanted-restoration-assembly-20261009.json')['selected_result']['raw_c_lower'])
    require(base_selected == F(baseline['conservative_raw_at_K0']) <= base, 'conservative base')
    A = F(data('selected-sieve-budget-feedback-audit-20261010.json')['slope']['total'])
    require(A == F(baseline['feedback_original_slope']), 'feedback slope')
    gain312 = F(data('table-k-feedback-transfer-assembly-20261009.json')['selected_result']['U3_U4_table_gain'])
    gain430 = F(data('fixed-action-current-k-two-cost-20261009.json')['gain_in_c_lower'])
    require(gain312 == F(baseline['table_gain248_to312']) and gain430 == F(baseline['table_gain312_to430']), 'selected table differences')
    old_gross = F(2095161, 10**9) + F(3799514, 10**9)
    old_loss = F(old['adoptable_loss_upper'])
    direct = base + A * (F('6.7619') - K) + gain312 + gain430 + old_gross - old_loss
    Rbase, Bbase = F(baseline['selected_current_raw']), F(baseline['lower_budget_each'])
    require(direct == F(baseline['direct_current_raw']), 'baseline lower ledger')
    require(direct - Rbase == base - base_selected, 'retained unselected rounding surplus')

    a, h, d, mu = [F(zero['parameters'][k]) for k in ['a', 'h', 'd', 'mu']]
    dt, du = (d - mu) / 512, (h - a) / 512
    E0 = sorted((s['t_index'], j) for s in zero['strips'] for j in range(s['first_u_index'], 512))
    E1 = [tuple(pair) for pair in old['selected_pairs']]
    require((len(E0), len(E1), len(set(E0 + E1))) == (6091, 11481, 17572), 'exact mask counts')
    rows = paired['rows']
    require(paired['row_columns'] == ROW_COLUMNS and len(rows) == 17572, 'v2 columns and row count')
    require([(r[0], r[1], r[2]) for r in rows] ==
            [('E0', i, j) for i, j in E0] + [('E1', i, j) for i, j in E1], 'full stored row order')
    stream = ''.join(','.join(map(str, r)) + '\n' for r in rows).encode()
    require(digest(stream) == paired['row_stream_sha256'], 'exact row stream')
    sums = defaultdict(lambda: [0, 0])
    saved_total, crossing = 0, 0
    for label, i, j, ztext, saved, lo, hi in rows:
        require(type(i) is int and type(j) is int and 0 <= i < 512 and 0 <= j < 512, 'grid indices')
        tl, tr = mu + i * dt, mu + (i + 1) * dt
        ul, ur = a + j * du, a + (j + 1) * du
        Z = F(ztext)
        require(0 < tl < tr and 0 < a <= ul < ur <= h < tl, 'positive ordered outer cell')
        require(Z == min(ul, F(3, 13) * (1 - tr - ur)) and a < Z <= ul, 'exact inner cutoff')
        require(1 - tr - ur - F(13, 3) * Z >= 0, 'inner Buchstab gate')
        rmin = F(57, 64) - F(5, 2) * tr - ur
        rmax = F(57, 64) - F(5, 2) * tl - ul
        require((rmax / a <= 2) if label == 'E0' else (2 < rmax / a <= F(9, 4)), 'old residual range')
        if label == 'E0':
            require(int(saved) == 0, 'E0 saved floor zero')
        if rmin / a < 2:
            require(int(saved) == 0, 'crossing saved floor zero')
            crossing += (label == 'E1')
        require(0 <= int(saved) and 0 < int(lo) <= int(hi), 'stored integer signs')
        saved_total += int(saved)
        sums[label][0] += int(lo)
        sums[label][1] += int(hi)
    for label, mask in [('E0', E0), ('E1', E1)]:
        group = paired['groups'][label]
        mask_stream = ''.join(f'{i},{j}\n' for i, j in mask).encode()
        require(digest(mask_stream) == group['mask_sha256'], 'mask stream: ' + label)
        require(F(sums[label][0], 2**160) == F(group['extra_gross_interval']['lower']), 'stored lower sum: ' + label)
        require(F(sums[label][1], 2**160) == F(group['extra_gross_interval']['upper']), 'stored upper sum: ' + label)
    require(saved_total == 11290806845175652020270 and crossing == 227, 'saved-floor exact sum')
    require(F(saved_total, 4 * Q) == F(paired['exact_discarded_E1_floor_in_c_units']), 'saved-floor units')
    gross, loss = F(paired['extra_gross_lower_adoptable']), F(paired['replacement_loss_upper'])
    require(gross == F(558583, 10**9) and loss == F(466977, 200000000), 'selected v2 scalars')
    delta = gross + old_loss - loss
    R, B = Rbase + delta, Bbase + delta / 8
    require(delta == F(current['raw_c_increment']) == F(37237, 62500000), 'replacement increment')
    require(R == F(current['raw_c_lower']), 'current raw lower')
    require(B == F(current['finite_approximation_loss_budget_in_c_units']) == F(current['compiler_loss_budget_in_c_units']), 'two lower reserves')
    require(Bbase == F(current['retained_lower_density_budget']) == F(current['retained_lower_compiler_budget']), 'retained lower reserves')
    require(delta / 8 == F(current['additional_lower_budget_each']), 'additional lower reserves')
    require(R - 2 * B == F(current['raw_after_two_error_budgets']), 'after lower reserves')
    require(R - 2 * B - c == F(current['remaining_lower_slack']) > 0, 'lower slack')
    require(R - 2 * B - (Rbase - 2 * Bbase) == 3 * delta / 4, 'net increment paid once')
    require(F(pair_terms['L6']) - 4 * loss == F(current['retained_L6_lower']), 'actual saved L6 deduction')
    require(gross / K == F(current['additional_paired_refinement_linear_coefficient']), 'extra gross feedback only')
    require(A - old_gross / K == F(current['feedback_slope_before_refinement']), 'baseline feedback slope')
    require(A - (old_gross + gross) / K == F(current['feedback_slope']), 'current feedback slope')

    result = {
        'status': 'PASS_FROZEN_BYTES_DECODING_AND_EXACT_ADOPTED_LEDGERS',
        'frozen_manuscript_sha': FROZEN_SHA, 'source_git_HEAD_checked': head_checked,
        'downloaded_source_files_verified': len(hashes),
        'compact_manifest_entries_verified': checked_manifest,
        'upper_selected_source_fields_verified': len(savings),
        'same_mask_rows_verified': len(rows), 'E1_crossing_zero_floors': crossing,
        'exact_saved_Q80_sum': str(saved_total),
        'upper_E': str(E), 'upper_reserve_each': str(U), 'upper_slack': str(K-E-2*U),
        'lower_R': str(R), 'lower_reserve_each': str(B), 'lower_slack': str(R-2*B-c),
        'raw_v2_increment': str(delta), 'net_v2_increment': str(3*delta/4),
        'integral_semantics_proved_here': False,
        'historical_quadratures_rerun': False,
        'source_interval_endpoints_kernel_checked': False,
        'source_files_modified': False,
    }
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding='utf-8')
    print(rendered, end='')


if __name__ == '__main__':
    main()
