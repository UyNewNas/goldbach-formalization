#!/usr/bin/env python3
"""Fixed, reviewed single-owner boundary; it contains no repair source."""
from pathlib import Path
import json

TARGET = 'ImbalancedChen.P2OriginalSaving19Geometry05ScalableShapeArrays'
TOOL_REL = Path('tools/p26/cell05-shape-repair-20261126')
BOUNDARY = json.loads(Path(__file__).with_name('BOUNDARY.json').read_text())
if not (BOUNDARY['schema'] == 'cell05_shape_repair_boundary_v1' and
        BOUNDARY['target_module'] == BOUNDARY['original_target']['module'] == TARGET and
        BOUNDARY['expected_direct_imports'] == BOUNDARY['original_target']['project_imports'] and
        BOUNDARY['expected_old_dependency_modules'] == BOUNDARY['original_target']['transitive_dependencies'] and
        BOUNDARY['target_count'] == 1 and BOUNDARY['planned_steps'] == 3 and
        len(BOUNDARY['expected_old_dependency_modules']) ==
        len(set(BOUNDARY['expected_old_dependency_modules'])) == 42 and
        BOUNDARY['actual_owned_project_closure_count'] == 43 and
        TARGET not in BOUNDARY['expected_old_dependency_modules']):
    raise ValueError('Invalid fixed ShapeArrays single-owner boundary')
