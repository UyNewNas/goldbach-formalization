from pathlib import Path
import ast
import base64
import difflib
import hashlib
import json
import zlib

root = Path('/dev/shm/p29-omitted-controller-1126')
def fixed(name, size, digest):
    value = (root / name).read_bytes()
    assert len(value) == size
    assert hashlib.sha256(value).hexdigest() == digest
    return value

old = fixed('omitted-prime-wall-P2-controller-v2.py', 64804,
            '945a19ceecfd707c5fa801ca9ce4f170755c9bbe363079293198e40bacc09970')
new = fixed('omitted-prime-wall-P2-import-order-resume-v3-postimage.py', 66896,
            '4cf893cb8afac435e9a5286fc101db03e55991fe93e38ef1afadac400c84be77')
boot = fixed('omitted-prime-wall-P2-import-order-resume-v3-bootstrap.py', 6266,
             '1e29557d3b1b72bf4eaff57b2c4aa59b15aa1d320fc41a1365bca1b850e97534')
wrapper = fixed('omitted-prime-wall-P2-import-order-resume-v3-command-template.sh', 3528,
                'b2ac25cf06b5d920f0d2fec9d18e7fc91745075ebb748ca976a43d7a3ffae8e7')
contract = fixed('OMITTED_P2_INPUT_CONTRACT_V2.json', 15390,
                 '1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf')

diff = ''.join(difflib.unified_diff(
    old.decode().splitlines(True), new.decode().splitlines(True),
    fromfile='original-v2-source-2f9204',
    tofile='import-order-resume-v3-postimage'))
assert diff == (root / 'OMITTED_P2_IMPORT_ORDER_RESUME_V2_TO_V3.patch').read_text()
bast = ast.parse(boot)
kinds = [type(node).__name__ for node in bast.body]
assert kinds == ['ImportFrom', 'Import', 'Assign', 'Assign', 'Assert',
                 'Assign', 'Assert', 'Assign', 'Assign', 'For', 'Assert', 'Expr']
change_node = bast.body[7]
assert ast.unparse(change_node.targets[0]) == 'changes'
changes = ast.literal_eval(change_node.value)
assert len(changes) == 11
postimage = old.decode()
for before, after in changes:
    assert postimage.count(before) == 1
    postimage = postimage.replace(before, after, 1)
assert postimage.encode() == new
restored = new.decode()
for before, after in reversed(changes):
    assert restored.count(after) == 1
    restored = restored.replace(after, before, 1)
assert restored.encode() == old
assert ast.unparse(bast.body[2]) == "base = Path('/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77')"
assert ast.unparse(bast.body[3]) == "source = (base / 'verification/driver.py').read_bytes()"
assert ast.unparse(bast.body[5]) == "contract = (base / 'verification/INPUT_CONTRACT.json').read_bytes()"
assert ast.unparse(bast.body[8]) == 'text = source.decode()'
expected_loop = ast.parse('for old, new in changes:\n assert text.count(old) == 1\n text = text.replace(old, new, 1)\n').body[0]
dump = lambda node: ast.dump(node, include_attributes=False)
assert dump(bast.body[9]) == dump(expected_loop)
for index, variable, digest in [
    (4, 'source', hashlib.sha256(old).hexdigest()),
    (6, 'contract', hashlib.sha256(contract).hexdigest()),
    (10, 'text.encode()', hashlib.sha256(new).hexdigest()),
]:
    expected = ast.parse(f'assert hashlib.sha256({variable}).hexdigest() == {digest!r}').body[0]
    assert dump(bast.body[index]) == dump(expected)
last = bast.body[-1].value
assert ast.unparse(last.func) == 'exec' and len(last.args) == 2 and not last.keywords
assert ast.unparse(last.args[0]) == "compile(text, 'omitted-prime-wall-P2-import-order-resume-v3.py', 'exec')"
assert [ast.literal_eval(key) for key in last.args[1].keys] == [
    '__name__', 'SOURCE_TEXT', 'SOURCE_SHA256', 'INPUT_CONTRACT_TEXT',
    'SERVICE_OBSERVATION_JSON', 'SERVICE_OBSERVATION_SHA256']
assert [ast.unparse(value) for value in last.args[1].values] == [
    "'__main__'", 'text', repr(hashlib.sha256(new).hexdigest()), 'contract.decode()',
    'SERVICE_OBSERVATION_JSON', 'SERVICE_OBSERVATION_SHA256']

old_functions = {node.name: node for node in ast.parse(old).body if isinstance(node, ast.FunctionDef)}
new_functions = {node.name: node for node in ast.parse(new).body if isinstance(node, ast.FunctionDef)}
assert old_functions.keys() == new_functions.keys()
changed = [name for name in old_functions if dump(old_functions[name]) != dump(new_functions[name])]
assert changed == ['authority_file', 'main']
assert len(old_functions) - len(changed) == 26
authority_calls = [ast.unparse(node.func) for node in ast.walk(new_functions['authority_file'])
                   if isinstance(node, ast.Call)]
assert 'get_blob' not in authority_calls
assert ast.unparse(new_functions['authority_file'].body[0]) == "p = previous_out / 'original-authorities' / label"

lines = wrapper.decode().splitlines(True)
assert lines[0] == "python3 - <<'PY'\n" and lines[-1] == 'PY\n'
wt = ast.parse(''.join(lines[1:-1]))
assert [type(node).__name__ for node in wt.body] == ['Import', 'Assign', 'Assign', 'Assert', 'Expr']
source_assign = wt.body[1]
assert ast.unparse(source_assign.targets[0]) == 'source'
outer = source_assign.value
assert ast.unparse(outer.func) == 'zlib.decompress' and len(outer.args) == 1 and not outer.keywords
inner = outer.args[0]
assert ast.unparse(inner.func) == 'base64.b64decode' and len(inner.args) == 1 and not inner.keywords
assert zlib.decompress(base64.b64decode(ast.literal_eval(inner.args[0]), validate=True)) == boot
assert ast.unparse(wt.body[2]) == "observation = zlib.decompress(base64.b64decode('__SERVICE_OBSERVATION_ZLIB_BASE64__'))"
expected_assert = ast.parse(
    f"assert hashlib.sha256(source).hexdigest() == {hashlib.sha256(boot).hexdigest()!r} "
    "and hashlib.sha256(observation).hexdigest() == '__SERVICE_OBSERVATION_SHA256__'"
).body[0]
assert dump(wt.body[3]) == dump(expected_assert)
outer_exec = wt.body[-1].value
assert ast.unparse(outer_exec.func) == 'exec' and len(outer_exec.args) == 2 and not outer_exec.keywords
assert ast.unparse(outer_exec.args[0]) == "compile(source, 'omitted-prime-wall-P2-import-order-resume-v3-bootstrap.py', 'exec')"
assert [ast.literal_eval(key) for key in outer_exec.args[1].keys] == [
    '__name__', 'SERVICE_OBSERVATION_JSON', 'SERVICE_OBSERVATION_SHA256']
assert [ast.unparse(value) for value in outer_exec.args[1].values] == [
    "'__main__'", 'observation.decode()', "'__SERVICE_OBSERVATION_SHA256__'"]
assert b'\x00' not in wrapper and len(wrapper) < 65536
request = json.loads((root / 'OMITTED_P2_IMPORT_ORDER_RESUME_V3_REQUEST_TEMPLATE.json').read_bytes())
assert {key: request[key] for key in ['cwd', 'memory_mb', 'cpu_threads', 'timeout_seconds']} == {
    'cwd': '/workspace', 'memory_mb': 12800, 'cpu_threads': 2, 'timeout_seconds': 3600}
for key, data in [('source_postimage', new), ('bootstrap', boot), ('wrapper_template', wrapper)]:
    assert request[key]['bytes'] == len(data)
    assert request[key]['sha256'] == hashlib.sha256(data).hexdigest()
    assert request[key]['git_blob'] == hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
result = {
    'status': 'PASS_STATIC_ONLY',
    'whole_diff_exact': True,
    'literal_replacements_forward_and_reverse_exact': 11,
    'bootstrap_AST_statement_kinds': kinds,
    'changed_functions': changed,
    'unchanged_function_count': 26,
    'all_old_14_helpers_and_resource7_unchanged': True,
    'old_contract_exact': True,
    'authority_file_has_no_remote_fallback': True,
    'whole_template_AST_statement_kinds': [type(node).__name__ for node in wt.body],
    'complete_template_bootstrap_payload_and_exec_globals_exact': True,
    'template_bytes': len(wrapper),
    'template_has_no_NUL': True,
    'final_service_observation_injection_not_yet_reviewed': True,
    'request_limits': {key: request[key] for key in ['cwd', 'memory_mb', 'cpu_threads', 'timeout_seconds']},
    'controller_or_bootstrap_execution': False,
    'remote_calls': 0,
    'old_actual_graph_reads': 0
}
print(json.dumps(result, indent=2))
