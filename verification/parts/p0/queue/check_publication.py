#!/usr/bin/env python3
"""Fail closed before publishing a CI-triggering ref update.

Feed the exact parent-to-candidate changed-path list from GitHub compare or
an equivalent Git diff. This does not perform any GitHub write or proof run.
"""
import argparse
import json
from pathlib import Path

TRIGGERS = {'automation/dispatch.json', 'automation/root-dispatch.json'}


def check(message, paths):
    if not isinstance(paths, list) or not all(isinstance(x, str) for x in paths):
        raise ValueError('Changed paths must be a string list')
    if len(paths) != len(set(paths)):
        raise ValueError('Duplicate changed path')
    skip = '[skip ci]' in message.lower()
    # A dispatch must never share a commit with the other dispatch or any
    # source/config/status path, even when the message suppresses CI.
    if TRIGGERS.intersection(paths) and (len(paths) != 1 or paths[0] not in TRIGGERS):
        raise ValueError('Dispatch commits must change exactly one dispatch file')
    if not skip and (len(paths) != 1 or paths[0] not in TRIGGERS):
        raise ValueError('Trigger commits may change only automation/dispatch.json OR automation/root-dispatch.json; publish source/config/status separately with [skip ci]')
    return {'status': 'PASS_PUBLICATION_PATH_SCOPE_ONLY', 'skip_ci': skip, 'changed_paths': paths}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--message', required=True)
    parser.add_argument('--paths-json', required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.message, json.loads(Path(args.paths_json).read_text()))))


if __name__ == '__main__':
    main()
