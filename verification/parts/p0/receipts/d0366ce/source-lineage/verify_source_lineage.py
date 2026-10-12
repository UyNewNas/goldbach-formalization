#!/usr/bin/env python3
"""Verify preserved fixed-commit parent evidence. No git/network/Lean/CI execution.

Local raw commit objects are rehashed with the Git commit-object prefix. Missing
local objects are backed by preserved responses from GitHub's pinned Git-commit
GET endpoint; their raw Git object bytes are not reconstructed or claimed here.
All output stays next to this script. This is source-lineage evidence, not a
proof compilation, kernel replay, or axiom-audit receipt.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
HEAD = 'd0366ce64272e81faf6166a8a90050f56b328d38'
DOC = '9fe1d6b8b68a97cad3a122410ad7fde1701eed35'
BASE = '1a80c1bcce67886f699d097fc37fd245cd3620bf'
REPO = 'UyNewNas/goldbach-formalization'
EXPECTED_HEAD_TREE = 'e2ab22b96f76c8969386296558c626c62a581700'
EXPECTED_PATH = [
    HEAD,
    '28fd630ef7cc38eba86beb6c0ba123336b5d05f2',
    'cce2334906f068fda2f58c400646366f2aa2d417',
    '80aca6710c83b5160f4c5fdd05d180e507990e95',
    '278f949444748a30b5165ff47bfa283ab0bad0d8',
    '5e31713690daba5ff926da61875a99171718fd1d',
    'c9f407efe66240c08c2e8a678330ba7b98b74db5',
    '30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb',
    DOC,
    BASE,
]


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def dump(name, data):
    (ROOT / name).write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def file_ref(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(ROOT)), 'bytes': len(data), 'sha256': sha256(data)}


def main():
    checks = []

    def check(name, valid):
        checks.append({'check': name, 'status': 'PASS' if valid else 'FAIL'})
        if not valid:
            dump('SOURCE_LINEAGE_CHECKS.json', {'scope': 'OFFLINE_FIXED_COMMIT_EVIDENCE',
                 'status': 'FAILED_CONSUMER_LINEAGE_CHECK_NOT_LEAN_DIAGNOSTIC', 'checks': checks})
            raise AssertionError(name)

    nodes = {}
    for requested_sha in EXPECTED_PATH:
        check('SHA syntax ' + requested_sha, re.fullmatch('[0-9a-f]{40}', requested_sha) is not None)
        local = ROOT / 'local-raw' / (requested_sha + '.commit')
        api_file = ROOT / 'github-api' / (requested_sha + '.json')
        if local.is_file():
            raw = local.read_bytes()
            actual_sha = hashlib.sha1(b'commit ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            check('raw Git commit identity ' + requested_sha, actual_sha == requested_sha)
            header, message = raw.decode().split('\n\n', 1)
            lines = header.splitlines()
            tree_rows = [line[5:] for line in lines if line.startswith('tree ')]
            parents = [line[7:] for line in lines if line.startswith('parent ')]
            check('one raw tree field ' + requested_sha, len(tree_rows) == 1)
            row = {'sha': requested_sha, 'tree': tree_rows[0], 'parents': parents,
                   'subject': message.splitlines()[0], 'source': 'LOCAL_RAW_COMMIT_OBJECT',
                   'commit_sha1_recomputed': actual_sha, 'raw_git_bytes_available': True,
                   'evidence': file_ref(local)}
        else:
            check('fixed API evidence present ' + requested_sha, api_file.is_file())
            wrapper = json.loads(api_file.read_text())
            expected_url = 'https://api.github.com/repos/' + REPO + '/git/commits/' + requested_sha
            check('fixed API requested identity ' + requested_sha, wrapper['requested_sha'] == requested_sha
                  and wrapper['requested_url'] == expected_url
                  and wrapper['method'] == 'READ_ONLY_GITHUB_GIT_COMMIT_API')
            response = wrapper['response']
            check('successful API result ' + requested_sha, response.get('isError') is False)
            payload_text = response['structuredContent']['content']
            payload = json.loads(payload_text)
            check('GitHub response source SHA and URL ' + requested_sha,
                  payload['sha'] == requested_sha and payload['url'] == expected_url
                  and response['structuredContent']['url'] == expected_url)
            check('normalized response retains same JSON body ' + requested_sha,
                  response['structuredContent']['structuredContent']['content'] == payload_text)
            metadata = ROOT / 'github-metadata' / (requested_sha + '.json')
            metadata.parent.mkdir(exist_ok=True)
            metadata.write_bytes(payload_text.encode())
            row = {'sha': requested_sha, 'tree': payload['tree']['sha'],
                   'parents': [parent['sha'] for parent in payload['parents']],
                   'subject': payload['message'].splitlines()[0],
                   'source': 'FIXED_GITHUB_GIT_COMMIT_API', 'source_url': expected_url,
                   'commit_sha1_recomputed': None, 'raw_git_bytes_available': False,
                   'signature_status_as_reported': payload.get('verification'),
                   'evidence': file_ref(api_file), 'returned_metadata': file_ref(metadata)}
        check('tree and parent SHA syntax ' + requested_sha,
              re.fullmatch('[0-9a-f]{40}', row['tree']) is not None and all(
                  re.fullmatch('[0-9a-f]{40}', parent) for parent in row['parents']))
        nodes[requested_sha] = row

    check('head tree equals integration tree', nodes[HEAD]['tree'] == EXPECTED_HEAD_TREE)
    edges = []
    for child, parent in zip(EXPECTED_PATH, EXPECTED_PATH[1:]):
        check('actual unique parent edge ' + child + ' -> ' + parent, nodes[child]['parents'] == [parent])
        edges.append({'child': child, 'parent': parent, 'source': nodes[child]['source'],
                      'child_evidence': nodes[child]['evidence']})
    check('documentation is direct child of proof baseline', nodes[DOC]['parents'] == [BASE])
    check('no repeated vertex in ancestor path', len(set(EXPECTED_PATH)) == len(EXPECTED_PATH))

    original_observation = ROOT / 'ORIGINAL_LOCAL_GIT_ANCESTRY_OBSERVATION.json'
    observed = json.loads(original_observation.read_text())
    observations = observed['observations']
    shallow = next(row for row in observations if row['argv'] == ['git', 'rev-parse', '--is-shallow-repository'])
    check('prior shallow repository observation retained', shallow['exit_code'] == 0 and shallow['stdout'] == 'true\n')
    failed_local_checks = [row for row in observations if row['argv'][:3] == ['git', 'merge-base', '--is-ancestor']
                           and row['argv'][3] in (BASE, DOC)]
    check('prior local exit 1 and 128 retained', {row['argv'][3]: row['exit_code'] for row in failed_local_checks}
          == {BASE: 1, DOC: 128})

    receipt = {
        'schema': 'p0.fixed-source-lineage.v1',
        'scope': 'RAW_COMMIT_AND_PINNED_API_PARENT_EDGES_NOT_LEAN_VALIDATION',
        'status': 'CONFIRMED_BOTH_REQUIRED_ANCESTORS',
        'repository': REPO,
        'integration_sha': HEAD,
        'integration_tree': nodes[HEAD]['tree'],
        'documentation_sha': DOC,
        'documentation_tree': nodes[DOC]['tree'],
        'proof_baseline_sha': BASE,
        'proof_baseline_tree': nodes[BASE]['tree'],
        'documentation_is_actual_ancestor': True,
        'proof_baseline_is_actual_ancestor': True,
        'documentation_parent_is_proof_baseline': True,
        'documentation_parent_edge_distance_from_integration': EXPECTED_PATH.index(DOC),
        'proof_baseline_parent_edge_distance_from_integration': EXPECTED_PATH.index(BASE),
        'unique_parent_chain_checked_to_baseline': True,
        'path_head_to_baseline': EXPECTED_PATH,
        'parent_edges': edges,
        'commit_records': [nodes[sha] for sha in EXPECTED_PATH],
        'evidence_counts': {
            'commit_nodes': len(nodes), 'verified_parent_edges': len(edges),
            'locally_rehashed_raw_commit_objects': sum(n['source'] == 'LOCAL_RAW_COMMIT_OBJECT' for n in nodes.values()),
            'fixed_api_metadata_nodes': sum(n['source'] == 'FIXED_GITHUB_GIT_COMMIT_API' for n in nodes.values()),
            'unresolved_edges_to_required_targets': 0,
        },
        'original_local_observation': file_ref(original_observation),
        'original_local_observation_interpretation':
            'The exit 1 for the baseline and exit 128 for the missing documentation object are observations of an incomplete shallow local graph. They are preserved, not treated as evidence of non-ancestry. Raw local parent headers and pinned GitHub parent metadata establish the actual chain.',
        'actions': {
            'git_object_reads': 'git cat-file -p only for lineage discovery',
            'remote_reads': 'GitHub GET /repos/UyNewNas/goldbach-formalization/git/commits/{fixed_sha}',
            'git_fetch_performed': False, 'git_shallow_modified': False,
            'git_refs_or_repository_files_modified': False,
            'repository_rebuilt': False,
            'lean_lake_elan_leanchecker_or_ci_executed': False,
            'ci_polled_or_healthy_build_interrupted': False,
        },
        'limits': [
            'Seven missing local commit nodes use the returned SHA/tree/parents from the fixed GitHub Git-commit API. Their raw Git commit bytes were not obtained or independently rehashed.',
            'Signature status is preserved as API metadata; no signature verification claim is made.',
            'Traversal stops at the required proof baseline. Its recorded earlier parent is preserved but pre-baseline history is not traversed.',
            'Ancestry is a source-history fact. This receipt does not assert any Lean compile/kernel/axiom gate result or unconditional final theorem.',
        ],
    }
    dump('SOURCE_LINEAGE_RECEIPT.json', receipt)
    dump('SOURCE_LINEAGE_CHECKS.json', {
        'status': 'PASS_FIXED_SOURCE_LINEAGE_EVIDENCE',
        'scope': receipt['scope'], 'script_sha256': sha256(Path(__file__).read_bytes()),
        'assertion_count': len(checks), 'checks': checks,
    })
    table = '\n'.join('| `' + n['sha'] + '` | `' + n['tree'] + '` | ' +
        ', '.join('`' + parent + '`' for parent in n['parents']) + ' | ' +
        ('本地原始 commit，已重算 SHA-1' if n['source'] == 'LOCAL_RAW_COMMIT_OBJECT' else '固定 GitHub Git-commit API') + ' |'
        for n in (nodes[sha] for sha in EXPECTED_PATH))
    (ROOT / 'SOURCE_LINEAGE_REPORT.md').write_text(
        '# d036 的实际父链核对\n\n'
        '**结论：符合用户指定祖先关系。** `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` 是集成 '
        '`d0366ce64272e81faf6166a8a90050f56b328d38` 的第 8 代父链祖先；共同证明基线 '
        '`1a80c1bcce67886f699d097fc37fd245cd3620bf` 是第 9 代。文档提交的直接父节点正是共同证明基线。\n\n'
        '9 条实际父边已逐项读取，这段链中每个子节点都只有表中列出的一个父节点，没有未闭合边。'
        '3 个节点使用本地 `git cat-file -p` 原始 commit 字节，并按 Git commit 对象格式重算 SHA-1；'
        '其余 7 个本地缺失节点使用固定 SHA 的 GitHub Git-commit GET 原始元数据。所有原件和摘要都保留在本目录。\n\n'
        '## 逐节点身份\n\n'
        '| Commit SHA | Tree SHA | 原始／API 返回的父 SHA | 证据 |\n| --- | --- | --- | --- |\n' + table + '\n\n'
        '## 浅克隆观察应如何解释\n\n'
        '`LOCAL_GIT_ANCESTRY_OBSERVATION.json` 的原字节副本保留为 '
        '`ORIGINAL_LOCAL_GIT_ANCESTRY_OBSERVATION.json`。其中本地 repository 明确为 shallow，'
        '`git log` 在 `28fd630…` 停止，`merge-base` 对共同基线返回 1，对本地缺失的文档对象返回 128。'
        '这些返回值属于本地不完整历史的观察，不等同于实际非祖先关系。\n\n'
        '直接读取 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` 的原始 commit 对象可见 '
        '`parent cce2334906f068fda2f58c400646366f2aa2d417`，因此浅克隆遍历隐藏的父边确实存在。'
        '继续沿固定元数据逐边读取即可到达文档提交与共同证明基线。没有通过改写 `.git/shallow`、'
        '重建仓库或改 refs 来改变原观察。\n\n'
        '## 证据边界\n\n'
        '固定 API 返回的 SHA、tree 和 parent 已核对，但没有取得这 7 个远端节点的原始 Git 字节，'
        '因此不声称对它们重算了 commit SHA-1。API 的 unsigned／signature 状态原样保留，不宣称完成签名验证。'
        '共同基线以前的历史不在本次遍历范围；基线原始对象里可见的更早父指针仍保留在表中。\n\n'
        '此回执只确认源代码历史，不增加任何 Lean 编译、内核重放、公理审计或最终定理验证状态。'
        '没有启动或轮询 CI，没有执行 Lean/Lake/Elan/leanchecker，没有触碰健康构建或集成分支。\n\n'
        '## 可复核文件\n\n'
        '- `SOURCE_LINEAGE_RECEIPT.json`：完整 SHA/tree/parents、9 条已闭合父边与机器结论。\n'
        '- `SOURCE_LINEAGE_CHECKS.json`：本消费者 ' + str(len(checks)) + ' 项证据核对。\n'
        '- `local-raw/`：3 个本地原始 commit 对象。\n'
        '- `github-api/`：7 个固定 Git-commit API 原始响应封装。\n'
        '- `github-metadata/`：上述 API 返回的原 JSON 内容字节。\n'
        '- `verify_source_lineage.py`：只使用这些已保存文件的离线复核程序，不执行 Git、网络、Lean 或 CI。\n'
        '- `OUTPUT_MANIFEST.json`：实际交付文件的字节数和 SHA-256，排除自身。\n')
    print(json.dumps({'status': receipt['status'], 'checks': len(checks),
          'raw_commit_nodes': 3, 'api_nodes': 7, 'edges': 9,
          'doc_distance': 8, 'baseline_distance': 9}))


if __name__ == '__main__':
    main()
