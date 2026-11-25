#!/usr/bin/env python3
"""Compare the public acceptance summary with local Git sources and the platform catalog."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
import run_selected as runner

GRAPH_PATH = 'docs/p1/20261124/batch5-parallel/run_batch5_parallel.py'
GRAPH_SHA256 = '1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5'
AXIOMS = {'Classical.choice', 'Quot.sound', 'propext'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_blob(repo, commit, path):
    return subprocess.check_output(['git', '--no-replace-objects', 'cat-file', 'blob',
                                   commit + ':' + path], cwd=repo)


def source_map(repo, commit):
    raw = git_blob(repo, runner.TOOLS, GRAPH_PATH)
    require(sha(raw) == GRAPH_SHA256, 'graph helper pin differs')
    helper = ModuleType('pinned_graph')
    exec(compile(raw, GRAPH_PATH, 'exec'), helper.__dict__)
    graph, local = helper.project_graph(repo, [runner.FIFTH, runner.FOURTH])
    fourth = helper.closure(graph, [runner.FOURTH])
    fifth = helper.closure(graph, [runner.FIFTH])
    require(len(fourth) == 252 and fourth <= fifth == set(graph) and len(fifth) == 304,
            'unexpected fourth or fifth project closure')
    sources = {}
    for module, entry in local.items():
        sources[module] = sha(git_blob(repo, commit, helper.module_path(module)))
        require(sources[module] == entry['sha256'], 'working source differs from commit: ' + module)
    return sources


def platform_owners(catalog):
    require(catalog['schema'] == 'p15_platform_capture_review_v1', 'unexpected platform catalog')
    verified = {}
    for job in catalog['jobs'].values():
        accepted = job['observed_accepted_owners']
        if not accepted:
            continue
        require(job['status'] in {'succeeded', 'failed'} and job['output_capture'] == 'lossless_complete',
                'owner event lacks terminal platform output')
        event_lines = job['acceptance_event_lines']
        result = job['proof_result']
        require(len(event_lines) == len(accepted) and all(0 < line < result['line'] for line in event_lines),
                'owner events do not precede the job result')
        for owner in accepted:
            require(owner not in verified, 'repeated platform owner: ' + owner)
            verified[owner] = result['source_commit']
    require(set(verified) == set(runner.TARGETS) and len(verified) == 23, 'platform owner set differs')
    require(catalog['owners_observed_in_completed_job_results'] == sorted(verified)
            and not catalog['repeated_observed_owner_counts'], 'platform catalog totals differ')
    return verified


def verify(summary, catalog, repo, commit):
    require(re.fullmatch('[0-9a-f]{40}', commit) and summary['source_commit'] == commit,
            'expected source commit differs from summary')
    require(summary['repository'] == 'UyNewNas/goldbach-formalization', 'unexpected repository')
    require(summary['source_runtime_unchanged'] is True and summary['git_unchanged'] is True
            and summary['whole_P1_complete'] is False and summary['whole_P1_5_complete'] is False,
            'summary state or scope differs')
    owners = summary['owners']
    commits = platform_owners(catalog)
    require(set(owners) == set(commits), 'summary owner set differs from platform')
    sources = source_map(repo, commit)
    digest = sha(json.dumps(sources, sort_keys=True, separators=(',', ':')).encode())
    require(summary['project_source_count'] == len(sources) and summary['project_source_map_sha256'] == digest,
            'project source map differs')
    require(re.fullmatch('[0-9a-f]{64}', summary['review_sha256']), 'invalid review digest')
    require(summary['observed_axioms'] == sorted(AXIOMS), 'observed aggregate axiom list differs')
    owned = public = 0
    for owner, row in owners.items():
        original = commits[owner]
        require(re.fullmatch('[0-9a-f]{40}', original) and row['original_source_commit'] == original,
                'original acceptance commit differs: ' + owner)
        prior_hash = sha(git_blob(repo, original, owner.replace('.', '/') + '.lean'))
        require(prior_hash == row['source_sha256'] == sources[owner], 'owner source differs: ' + owner)
        receipts = row['receipt_sha256']
        require(set(receipts) == {'normal', 'audit_plan', 'audit_result'}
                and all(re.fullmatch('[0-9a-f]{64}', value) for value in receipts.values()),
                'invalid public receipt bindings: ' + owner)
        n, p = row['owned_count'], row['public_count']
        require(type(n) is int and type(p) is int and n > 0 and 0 <= p <= n,
                'invalid declaration counts: ' + owner)
        owned += n
        public += p
    require(type(summary['owned_count']) is int and type(summary['public_count']) is int
            and (owned, public) == (summary['owned_count'], summary['public_count']), 'aggregate counts differ')
    return {'verified_owners': len(owners), 'project_source_count': len(sources),
            'project_source_map_sha256': digest, 'source_commit': commit,
            'owned_count': owned, 'public_count': public}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--summary', required=True, type=Path)
    parser.add_argument('--catalog', required=True, type=Path)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    args = parser.parse_args()
    summary = json.loads(args.summary.read_text().removeprefix('PUBLIC_ACCEPTANCE_SUMMARY '))
    catalog = json.loads(args.catalog.read_bytes())
    print(json.dumps(verify(summary, catalog, args.repo, args.source_commit), sort_keys=True))
