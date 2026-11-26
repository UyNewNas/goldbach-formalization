from pathlib import Path
import ast
import base64
import difflib
import hashlib
import json

HERE = Path(__file__).resolve().parent
BASE = Path('/tmp/p24-integration-repairs-20261126/p2-select-original-audit-receipts-b55-draft01.py')
original = BASE.read_bytes()
assert hashlib.sha256(original).hexdigest() == 'bfd4ab5f2d08020eb9cd6cff250503e80c649c594c441acded774b636b81efd3'
setup = original.decode().split('common = [sys.executable,', 1)[0]
assert setup.endswith('}\n')
template = (HERE/'SerializedNames.template.lean').read_bytes()
tail = (HERE/'scanner-tail-draft01.py').read_text()
body = setup + '\nSERIALIZED_NAMES_TEMPLATE_BASE64 = ' + repr(base64.b64encode(template).decode()) + '\n'
body += 'SERIALIZED_NAMES_TEMPLATE_SHA256 = ' + repr(hashlib.sha256(template).hexdigest()) + '\n\n' + tail
ast.parse(body)
shell = "set -euo pipefail\nexport PYTHONDONTWRITEBYTECODE=1 GIT_OPTIONAL_LOCKS=0\ncd /workspace/p2-4-compact-proof-20261125\nexec 9<.lake/p2-private/p24-migration.lock\nflock -n 9\npython3 -B - <<'P24_SERIALIZED_322_PY'\n" + body + '\nP24_SERIALIZED_322_PY\n'
(HERE/'p2-current322-serialized-names-b55-draft01.py').write_text(body)
(HERE/'p2-current322-serialized-names-b55-draft01.sh').write_text(shell)
setup_sha = hashlib.sha256(setup.encode()).hexdigest()
manifest = {'source_pin':'b55fa93d39e6a4ddf2abd37b9b8481078e329f70',
            'base_reviewed_selector_setup':{'path':str(BASE),'bytes':len(original),'sha256':hashlib.sha256(original).hexdigest()},
            'unchanged_setup_bytes':len(setup.encode()),'unchanged_setup_sha256':setup_sha,
            'source_runtime_native_full324_guards_byte_identical':True,
            'original_template':'2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b',
            'serialized_api':'env.header.modules[i].module; require !data.isModule && imported.importAll && imported.hasData; data.constNames, as in unchanged original audit template',
            'no_merged_environment_owner_filter':True,
            'current322_scope':'original321 five roots plus A; exclude B and W',
            'original_verify_compilation_before_and_after':True,
            'zero_budget_not_repeated':True,'no_o_argument':True,
            'outer_resources':{'timeout_seconds':600,'memory_mb':13107,'cpu_threads':1},
            'child_timeout_seconds':300,'child_flags':['-t0','-j1','-M11264','-DwarningAsError=true','-DmaxRecDepth=50000','-DmaxHeartbeats=40000000'],
            'remote_output':'/workspace/p24-current322-serialized-names-b55-20261126/attempt-001',
            'stdout':'complete duplicate report if <=200 KiB, per-module 322 counts and small receipt; complete inventories lossless gzip',
            'not_a_full_audit':True,'no_type_or_axiom_or_replay_credit':True,'canonical_credit':False,'executed':False,
            'prior_inventory_reuse':'The existing old aggregate scan has only321 modules and predates b55 repaired objects; it cannot cover current A or certify all current322 bindings. No old counts are reused.',
            'files':{}}
for n in ['SerializedNames.template.lean','scanner-tail-draft01.py','p2-current322-serialized-names-b55-draft01.py','p2-current322-serialized-names-b55-draft01.sh']:
    raw=(HERE/n).read_bytes();manifest['files'][n]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
(HERE/'draft01-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(manifest,ensure_ascii=False))
