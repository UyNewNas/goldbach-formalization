#!/usr/bin/env python3
"""Package the finite-shape batch using the frozen connection packager."""
import sys
import json
import re

sys.dont_write_bytecode = True
import prepare_batch
from generate_shape import BATCH, HERE, REPO, TAG, TYPED_NS, fp, frozen_prior, write_new

# The parse/decode handoff joins the already frozen 718 predecessor paths.
# No original packager byte or previously generated source is rewritten.
prepare_batch.frozen_prior = frozen_prior

if __name__ == '__main__':
    manifest = json.loads((HERE / 'batches' / BATCH / 'SOURCE_MANIFEST.json').read_text())
    available = {}
    for path in sorted((REPO / 'ImbalancedChen').glob(TAG + 'Typed*.lean')):
        text = path.read_text()
        assert '\nnamespace ' + TYPED_NS + '\n' in text
        for name in re.findall(r'(?m)^theorem (geometry(?:Row\d+|Vertices_\d+|VertexValues_\d+|FacetVertices_\d+|Faces_\d+)_shape)\b', text):
            full = TYPED_NS + '.' + name
            assert full not in available
            available[full] = {'declaration': full, 'owner': 'ImbalancedChen.' + path.stem, 'source': fp(path)}
    required = manifest['required_local_shape_declarations']
    assert len(required) == len(set(required)) == len(available) == 168
    assert set(required) == set(available)
    write_new(HERE / 'batches' / BATCH / 'LOCAL_CONTRACT_CHECK.json', {
        'schema': 'cell05_finite_shape_local_source_contract_check_v1',
        'status': 'PASS_TEXTUAL_SOURCE_BINDINGS_ONLY',
        'required_local_shape_count': 168,
        'required_local_shape_declarations': [available[name] for name in required],
        'new_identifier_projection_blocks': 7, 'rows_per_identifier_block': 8,
        'new_facet_original_index_nat_checks': 2,
        'new_full_record_decisions': 0, 'new_Lean_steps_run': 0,
        'Lean_type_correctness_or_mathematical_acceptance_claimed': False})
    prepare_batch.main()
