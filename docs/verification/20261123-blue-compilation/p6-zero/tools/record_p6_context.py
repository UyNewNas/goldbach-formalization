#!/usr/bin/env python3
"""Hash a P6 root's complete selected source closure and explicit proof overlays."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json

PROJECT = Path('/workspace/blue-p6-build')
ROOT = Path('/workspace/blue-p6-controller')
SELECTION = Path('/workspace/blue-p6-selection.json')
TARGETS = dict(seventh='ImbalancedChen.P6OriginalSeventhMeshPrice',
               eighth='ImbalancedChen.P6OriginalEighthMeshPrice',
               ninth='ImbalancedChen.P6OriginalNinthMeshPrice',
               zero='ImbalancedChen.P6OriginalZeroMarkedIntegralCost')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=TARGETS)
    args = parser.parse_args()
    selection = json.loads(SELECTION.read_text())
    target = TARGETS[args.phase]
    closure = selection['roots'][target]
    projects = {}
    natives = {}
    for name in closure['project_modules']:
        entry = selection['project_sources'][name]
        path = PROJECT / entry['install_path']
        current = sha(path)
        projects[name] = dict(install_path=entry['install_path'],
                              selected_preimage_sha256=entry['sha256'],
                              current_sha256=current, current_bytes=path.stat().st_size,
                              source_commit=entry['source_commit'], source_path=entry['source_path'],
                              proof_postimage=current != entry['sha256'])
    for name in closure['native_source_modules']:
        entry = selection['native_sources'][name]
        path = PROJECT / '.lake/packages/goldbach' / entry['install_path']
        current = sha(path)
        assert current == entry['sha256'], name + ': native source mismatch'
        natives[name] = dict(install_path=entry['install_path'], sha256=current,
                             source_commit=entry['source_commit'], source_path=entry['source_path'])
    result = dict(schema='p6_exact_root_current_source_context_v1', target=target,
                  recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  base_selection=dict(path=str(SELECTION), sha256=sha(SELECTION)),
                  pins=selection['pins'], manuscript_release='paper/release-20261106',
                  manuscript_commit='a988cba584d803ae2856a0de50efb582f4f3dd6a',
                  project_sources=projects, native_sources=natives,
                  summary=dict(project_source_count=len(projects), native_source_count=len(natives),
                               proof_postimage_count=sum(x['proof_postimage'] for x in projects.values()),
                               all_native_sources_exact_selected_hashes=True),
                  project_configuration={name: dict(sha256=sha(PROJECT / name),
                                                    bytes=(PROJECT / name).stat().st_size)
                                         for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']},
                  data_inputs=selection['data_inputs'],
                  scope_limitations=[
                      'Exact module kernel replay uses the recorded existing imported objects; '
                      'it is not fresh replay of every native or project dependency.',
                      'The price and normalization quantities retain release-20261106 identities. '
                      'No numerical archive or frozen source image was changed.'])
    output = ROOT / args.phase / 'SOURCE_CONTEXT.json'
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(summary=result['summary'], path=str(output), sha256=sha(output))))


if __name__ == '__main__':
    main()
