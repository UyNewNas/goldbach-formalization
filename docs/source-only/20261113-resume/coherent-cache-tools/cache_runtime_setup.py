"""GitHub-only explicit pre-exec extension around the exact original guard.

The baseline guard file stays byte-identical. Its factory, normalizer, locks,
environment/resource checks and auditor are not weakened. The actual generated
wrapper gains a separately recorded denial call before its log/exec sequence.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BASELINE = '837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877'
ANCHOR = "compiler = (C['shadow'] + '/bin/lean-runtime' if name == 'lean'"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def insert_hook(wrapper, policy, policy_sha):
    assert wrapper.count(ANCHOR) == 1
    hook = ("import importlib.util as _cache_importlib\n"
            "import hashlib as _cache_hashlib\n"
            "require(_cache_hashlib.sha256(pathlib.Path(" + repr(str(HERE / 'cache_preexec_policy.py')) + ").read_bytes()).hexdigest() == " + repr(sha(HERE / 'cache_preexec_policy.py')) + ", 'cache denial source changed')\n"
            "_cache_spec = _cache_importlib.spec_from_file_location('cache_preexec_policy', " + repr(str(HERE / 'cache_preexec_policy.py')) + ")\n"
            "_cache_policy = _cache_importlib.module_from_spec(_cache_spec)\n"
            "_cache_spec.loader.exec_module(_cache_policy)\n"
            "_cache_policy.enforce(name, args, os.getcwd(), " + repr(str(policy)) + ", " + repr(policy_sha) + ", raw_argv=sys.argv[1:])\n")
    return wrapper.replace(ANCHOR, hook + ANCHOR), hook


def main():
    assert os.environ.get('GITHUB_ACTIONS') == 'true' and sys.platform == 'linux', 'GitHub only'
    # Binding occurs before any toolchain/setup execution. The caller selects
    # exactly native398 or the separate single-parent graph, never both.
    from coherent_cache import bind_inputs, scope_policy
    scope = os.environ['CACHE_SCOPE']
    bound = bind_inputs(scope)
    project, logs = Path(os.environ['PROJECT']).resolve(), Path(os.environ['LOGS']).resolve()
    evidence = logs / 'runtime'
    policy_path = logs / 'CACHE_PREEXEC_POLICY.json'
    assert not policy_path.exists()
    policy = scope_policy(scope, project, logs, bound)
    policy_path.write_bytes((json.dumps(policy, indent=2) + '\n').encode())
    baseline = HERE / 'reused/ci_runtime_guard.py'
    assert sha(baseline) == BASELINE
    spec = importlib.util.spec_from_file_location('cache_original_runtime_guard', baseline)
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    original = guard.WRAPPER
    guard.WRAPPER, hook = insert_hook(original, policy_path, sha(policy_path))
    # Invoke the original CLI setup with every original pin/action/resource
    # check. No fake state, toolchain binary, or hash is supplied by this layer.
    sys.argv = [str(baseline), 'setup', '--evidence', str(evidence)]
    guard.main()
    state = json.loads((evidence / 'state.json').read_text())
    actual = {tool: sha(Path(state['shadow']) / 'bin' / tool) for tool in state['tools']}
    receipt = {'status': 'ORIGINAL_GUARD_PLUS_EXPLICIT_PREEXEC_CACHE_DENIAL', 'binding': bound,
               'baseline_guard_sha256': BASELINE, 'extension_sha256': sha(__file__),
               'policy_source_sha256': sha(HERE / 'cache_preexec_policy.py'),
               'policy_file_sha256': sha(policy_path), 'generated_wrapper_sha256': actual,
               'original_wrapper_template_sha256': hashlib.sha256(original.encode()).hexdigest(),
               'extended_wrapper_template_sha256': hashlib.sha256(guard.WRAPPER.encode()).hexdigest(),
               'exact_inserted_hook': hook, 'actual_runtime_state_sha256': sha(evidence / 'state.json'),
               'original_slot_normalizer_env_resource_and_audit_gates_preserved': True,
               'wrapper_bytes_are_explicitly_extended_not_claimed_original': True}
    (logs / 'CACHE_RUNTIME_EXTENSION.json').write_bytes((json.dumps(receipt, indent=2) + '\n').encode())


if __name__ == '__main__': main()
