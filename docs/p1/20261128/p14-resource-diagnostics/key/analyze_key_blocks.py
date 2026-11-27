from pathlib import Path
import collections, hashlib, json, re
REPO = Path('/workspace/scratch/adad8d3ee47c/goldbach-p14')
OUT = Path(__file__).resolve().parent
hub = REPO / 'ImbalancedChen/Data/P1HistoricalFifthSavedTableData.lean'
hub_bytes = hub.read_bytes()
assert hashlib.sha256(hub_bytes).hexdigest() == '4590eb2a2bbca87b2ae373401cfa408172e93fd87c51623ef9eed114130fc274'
body = hub_bytes.decode().split('def blocks :', 1)[1].split('def rows :', 1)[0]
block_names = re.findall(r'ImbalancedChen\.Data\.P1HistoricalFifthSavedDataBlock(\d{3})\.rows', body)
assert block_names == [f'{i:03d}' for i in range(143)]
row_pattern = re.compile(r'\s*⟨(-?\d+),\s*!\[(-?\d+),\s*(-?\d+),\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)\],\s*(-?\d+),\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)⟩,?\s*')
all_codes, all_keys, per_block = [], [], []
source_pins = []
first_bucket = collections.Counter()
second_bucket = collections.Counter()
first_to_blocks = collections.defaultdict(set)
second_to_blocks = collections.defaultdict(set)
unsorted_witnesses = []
for tag in block_names:
    path = REPO / f'ImbalancedChen/Data/P1HistoricalFifthSavedDataBlock{tag}.lean'
    data = path.read_bytes()
    text = data.decode()
    start = text.index('def rows : Array FifthWireRow := #[')
    payload = text[start:].split('#[', 1)[1].rsplit(']', 1)[0]
    rows = []
    for line in payload.splitlines():
        if not line.strip(): continue
        m = row_pattern.fullmatch(line)
        assert m is not None, (tag, line)
        rows.append(tuple(map(int, m.groups())))
    assert len(rows) == (2048 if int(tag) < 142 else 1817)
    codes = []
    for local_index, row in enumerate(rows):
        key = row[1:6]
        assert row[0] == 400
        code = 0
        for v in key: code = code * 400 + max(v, 0)
        codes.append(code)
        all_keys.append(key)
        first_bucket[code // 400**4] += 1
        second_bucket[code // 400**3] += 1
        first_to_blocks[code // 400**4].add(int(tag))
        second_to_blocks[code // 400**3].add(int(tag))
    nonincreasing = [(i, codes[i], codes[i+1]) for i in range(len(codes)-1) if codes[i] >= codes[i+1]]
    if nonincreasing and len(unsorted_witnesses) < 5:
        i,a,b = nonincreasing[0]
        unsorted_witnesses.append({'block':tag,'local_indices':[i,i+1],'keys':[list(rows[i][1:6]),list(rows[i+1][1:6])],'codes':[a,b]})
    per_block.append({'block':tag,'count':len(codes),'source_offset':len(all_codes),'min':min(codes),'max':max(codes),'first':codes[0],'last':codes[-1],'distinct':len(set(codes)),'nonincreasing_adjacent_count':len(nonincreasing),'first_buckets':len(set(c // 400**4 for c in codes)),'second_buckets':len(set(c // 400**3 for c in codes))})
    all_codes.extend(codes)
    source_pins.append({'path':str(path.relative_to(REPO)),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'rows':len(rows)})
assert len(all_codes) == 292633
interval_overlaps = [(a['block'],b['block']) for i,a in enumerate(per_block) for b in per_block[i+1:] if max(a['min'],b['min']) <= min(a['max'],b['max'])]
first_max = max(first_bucket.values()); second_max = max(second_bucket.values())
report = {
 'status':'PURE_PYTHON_STATIC_DATA_ANALYSIS_NOT_LEAN_PROOF_OR_ACCEPTANCE',
 'source_hub':{'path':str(hub.relative_to(REPO)),'bytes':len(hub_bytes),'sha256':hashlib.sha256(hub_bytes).hexdigest()},
 'schema':'exact ten signed integer literal fields, all143 published blocks in hub order, no ignored payload lines',
 'code_formula':'left fold of max(key coordinate,0) with base400, exactly Core codeOfKey and rowKey=raw.lo',
 'block_count':143,'row_count':len(all_codes),'block_sizes':{'2048':142,'1817':1},
 'distinct_codes':len(set(all_codes)),'distinct_geometry_keys':len(set(all_keys)),
 'coordinate_minima':[min(k[i] for k in all_keys) for i in range(5)],
 'coordinate_maxima':[max(k[i] for k in all_keys) for i in range(5)],
 'code_min':min(all_codes),'code_max':max(all_codes),
 'original_list_strict_increasing':all(a<b for a,b in zip(all_codes,all_codes[1:])),
 'original_blocks_all_locally_strict':all(x['nonincreasing_adjacent_count']==0 for x in per_block),
 'non_strict_block_count':sum(x['nonincreasing_adjacent_count']>0 for x in per_block),
 'original_order_witnesses':unsorted_witnesses,
 'overlapping_original_block_code_interval_pairs':len(interval_overlaps),
 'total_original_block_pairs':143*142//2,
 'overlap_first_ten':interval_overlaps[:10],
 'first_digit_buckets':{'definition':'code // 400^4','count':len(first_bucket),'max_rows':first_max,'max_buckets':[{'bucket':k,'rows':v,'original_blocks':len(first_to_blocks[k])} for k,v in sorted(first_bucket.items()) if v==first_max],'rows_by_bucket':[{ 'bucket':k,'rows':v,'original_blocks':len(first_to_blocks[k])} for k,v in sorted(first_bucket.items())]},
 'two_digit_buckets':{'definition':'code // 400^3','count':len(second_bucket),'max_rows':second_max,'max_buckets':[{'bucket':k,'rows':v,'original_blocks':len(second_to_blocks[k])} for k,v in sorted(second_bucket.items()) if v==second_max],'occupancy_histogram':dict(sorted(collections.Counter(second_bucket.values()).items()))},
 'per_block':per_block,
 'source_pins':source_pins,
 'not_claimed':['Lean uniqueness proof','archived NPY byte authenticity','kernel resource improvement','new normal/kernel/full-owned acceptance'],
 'run_kind':'offline Python only; no Lean invocation, source edits or network'
}
review_path = REPO.parent / 'p14-key-deployment-static-review.json'
review_bytes = review_path.read_bytes()
review = json.loads(review_bytes)
assert review['static_review_passed'] and review['source_closure_modules'] == 404
for pin in source_pins + [report['source_hub']]:
    module = pin['path'][:-5].replace('/', '.')
    expected = review['source_identity'][module]
    assert pin['bytes'] == expected['bytes'] and pin['sha256'] == expected['sha256'], module
report['source_binding_to_reused_d14_static_review'] = {
    'path': str(review_path), 'sha256': hashlib.sha256(review_bytes).hexdigest(),
    'matched_literal_blocks': 143, 'matched_hub': True,
    'certificate_sha256': review['source_identity']['ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate']['sha256']}
report['bucket_width_candidates'] = []
for width in [1, 2, 4, 8, 16, 400]:
    counts = collections.Counter()
    for bucket, count in second_bucket.items(): counts[bucket // width] += count
    report['bucket_width_candidates'].append({'definition':f'code // ({width} * 400^3)', 'nonempty':len(counts), 'max_rows':max(counts.values())})
separated = sum(a['max'] < b['min'] for a,b in zip(per_block,per_block[1:]))
report['adjacent_original_block_range_separation'] = {'forward_strictly_separated_pairs':separated, 'not_forward_strictly_separated_pairs':142-separated, 'total_pairs':142}
components = []
for block in sorted(per_block,key=lambda b:b['min']):
    if not components or block['min'] > components[-1]['max']:
        components.append({'blocks':[block['block']], 'min':block['min'], 'max':block['max'], 'rows':block['count']})
    else:
        components[-1]['blocks'].append(block['block'])
        components[-1]['max'] = max(components[-1]['max'], block['max'])
        components[-1]['rows'] += block['count']
report['block_interval_components'] = {'count':len(components), 'max_blocks':max(len(c['blocks']) for c in components), 'max_rows':max(c['rows'] for c in components),'components':components}
sorted_code_keys = sorted(all_codes)
rank_of_code = {code:rank for rank,code in enumerate(sorted_code_keys)}
shard_counts = []
for block in per_block:
    begin = block['source_offset']; codes = all_codes[begin:begin+block['count']]
    shard_counts.append({'source_block':block['block'], 'distinct_sorted_key_shards_2048':len({rank_of_code[code] // 2048 for code in codes})})
report['inverse_lookup_candidate_structure_only'] = {
    'not_generated_as_Lean':True, 'entries':len(sorted_code_keys),
    'median_tree_max_levels_theoretical':len(sorted_code_keys).bit_length(),
    'candidate_dictionary_sorted_shards_2048':(len(sorted_code_keys)+2047)//2048,
    'source_block_shard_count_min':min(x['distinct_sorted_key_shards_2048'] for x in shard_counts),
    'source_block_shard_count_max':max(x['distinct_sorted_key_shards_2048'] for x in shard_counts),
    'source_block_shard_count_histogram':dict(sorted(collections.Counter(x['distinct_sorted_key_shards_2048'] for x in shard_counts).items())),
    'shard_counts':shard_counts,
    'unknown_key_default':'0 proposed, not needed as a correctness assumption',
    "per_block_certificate": "map g original_block_codes = List.range' offset actual_length",
    'g_key_fields':'original codeOfKey of five raw.lo values only; values are original global indices',
    'resource_feasibility':'unmeasured; no Lean run or memory guarantee'}
report['analysis_script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(OUT/'KEY_BLOCK_DATA_ANALYSIS.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','block_count','row_count','distinct_codes','distinct_geometry_keys','coordinate_minima','coordinate_maxima','non_strict_block_count','overlapping_original_block_code_interval_pairs','total_original_block_pairs']},ensure_ascii=False))
print('first_buckets',len(first_bucket),'max',first_max,'second_buckets',len(second_bucket),'max',second_max)
print('first bucket maxima',report['first_digit_buckets']['max_buckets'])
print('second bucket maxima',report['two_digit_buckets']['max_buckets'][:5])
print('source_order_example',unsorted_witnesses[:1])
