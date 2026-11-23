#!/usr/bin/env python3
"""Record exact source identity and executable declaration preservation."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess

PROJECT = Path('/workspace/blue-p6-build')
REPO = Path('/workspace/goldbach-formalization')
REPAIRS = Path('/workspace/blue-p6-controller/repairs')


def without_comments(text):
    out = list(text)
    index = 0
    depth = 0
    string = False
    while index < len(text):
        if depth:
            if text.startswith('/-', index):
                depth += 1
                out[index:index + 2] = '  '
                index += 2
            elif text.startswith('-/', index):
                depth -= 1
                out[index:index + 2] = '  '
                index += 2
            else:
                if text[index] != '\n':
                    out[index] = ' '
                index += 1
        elif string:
            if text[index] == '\\':
                index += 2
            else:
                if text[index] == '"':
                    string = False
                index += 1
        elif text.startswith('/-', index):
            depth = 1
            out[index:index + 2] = '  '
            index += 2
        elif text.startswith('--', index):
            end = text.find('\n', index)
            if end == -1:
                end = len(text)
            out[index:end] = ' ' * (end - index)
            index = end
        else:
            if text[index] == '"':
                string = True
            index += 1
    assert depth == 0
    return ''.join(out)


def commands(text):
    clean = without_comments(text)
    pattern = re.compile(r'(?m)^(?:(?:private|protected|noncomputable)\s+)*(?:@\[[^\n]*\]\s*)?'
                         r'(theorem|lemma|def|abbrev|structure|instance|class|opaque|axiom)\b')
    matches = list(pattern.finditer(clean))
    return [(match.group(1), clean[match.start():matches[index + 1].start()
                                  if index + 1 < len(matches) else len(clean)].strip())
            for index, match in enumerate(matches)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('module')
    parser.add_argument('--status', default='pending_aggregate_compile_and_exact_module_validation')
    args = parser.parse_args()
    module = args.module.removeprefix('ImbalancedChen.')
    directory = REPAIRS / module
    before = (directory / 'before.lean').read_bytes()
    source = PROJECT / 'ImbalancedChen' / (module + '.lean')
    after = source.read_bytes()
    main = REPO / 'ImbalancedChen' / (module + '.lean')
    assert main.read_bytes() == after
    old_commands, new_commands = commands(before.decode()), commands(after.decode())
    assert len(old_commands) == len(new_commands)
    changed = []
    for (old_kind, old), (new_kind, new) in zip(old_commands, new_commands):
        assert old_kind == new_kind
        if old_kind in {'theorem', 'lemma'}:
            old_header, sep, old_body = old.partition(':=')
            new_header, new_sep, new_body = new.partition(':=')
            assert sep == new_sep == ':='
            assert old_header.rstrip() == new_header.rstrip(), module + ': theorem header changed'
            if old_body != new_body:
                changed.append(new_header.rstrip())
        else:
            assert old == new, module + ': non-theorem command changed'
    record = json.loads((directory / 'ORIGIN.json').read_text())
    record.update(postimage_sha256=hashlib.sha256(after).hexdigest(),
                  postimage_git_blob_sha1=subprocess.check_output(
                      ['git', 'hash-object', '--stdin'], input=after, cwd=REPO).decode().strip(),
                  bytes=len(after), all_theorem_headers_preserved=True,
                  all_definitions_structures_instances_preserved=True,
                  source_command_count=len(old_commands), changed_proof_headers=changed,
                  validation_status=args.status)
    (directory / 'SOURCE_SELECTION.json').write_text(json.dumps(record, indent=2) + '\n')
    (directory / 'postimage.lean').write_bytes(after)
    (directory / 'candidate.patch').write_text(''.join(difflib.unified_diff(
        before.decode().splitlines(keepends=True), after.decode().splitlines(keepends=True),
        fromfile='a/ImbalancedChen/' + module + '.lean', tofile='b/ImbalancedChen/' + module + '.lean')))
    print(json.dumps({key: record[key] for key in ['module', 'preimage_sha256', 'postimage_sha256',
                                                  'source_command_count', 'validation_status']}))


if __name__ == '__main__':
    main()
