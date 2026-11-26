#!/usr/bin/env python3
"""Freeze the narrow SmoothLicence updater from verified V publication inputs."""
from pathlib import Path
import argparse, ast, hashlib, json, pprint, re

BASE = Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126')
OUT = Path('/tmp/p15-smooth-repair')


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--config', type=Path, required=True)
    args = p.parse_args()
    config = json.loads(args.config.read_text())
    assert re.fullmatch('[0-9a-f]{40}', config['repair_source_commit'])
    old = (BASE / 'apply_word_repair.py').read_text()
    assert hashlib.sha256(old.encode()).hexdigest() == 'e7058d2214b2119f1985cf21a073cc87d66603a930d7c49f29cf6e8705d390f4'
    funcs = {n.name: ast.get_source_segment(old, n) for n in ast.parse(old).body if isinstance(n, ast.FunctionDef)}
    names = ['need', 'raw_fp', 'value_fp', 'pin', 'git_file', 'file_fp', 'source_inventory',
             'artifact_inventory', 'normal_path', 'require_preimage', 'archive_binding', 'prior_archive',
             'fsync_directory', 'archive_setup']
    helpers = '\n\n\n'.join(funcs[n] for n in names)
    # Preserve the tested archive implementation; only fixed identities and messages change.
    helpers = helpers.replace('S/T/U/script-bound', 'U/V/W/script-bound')
    helpers = re.sub(r'\bS\b', 'U', helpers).replace('WordDictionary', 'SmoothLicence')
    start = (OUT / 'smooth_updater_header.py.txt').read_text()
    body = (OUT / 'smooth_updater_body.py.txt').read_text()
    code = start + '\nFROZEN = ' + pprint.pformat(config, width=110, sort_dicts=False) + '\n'
    code += "V = FROZEN['repair_source_commit']\nAFTER = FROZEN['after']\nPINS = FROZEN['document_pins']\n"
    code += '\n' + helpers + '\n\n\n' + body
    compile(code, 'apply_smooth_repair.py', 'exec')
    (OUT / 'apply_smooth_repair.py').write_text(code)
    print(json.dumps({'bytes': len(code.encode()), 'sha256': hashlib.sha256(code.encode()).hexdigest(),
                      'repair_source_commit': config['repair_source_commit'], 'new_lean_acceptance': False}))


if __name__ == '__main__':
    main()
