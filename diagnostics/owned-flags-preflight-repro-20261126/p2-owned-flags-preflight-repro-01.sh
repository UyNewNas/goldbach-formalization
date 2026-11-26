#!/usr/bin/env bash
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_FLAGS_REPRO_PY'
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

root = Path('/workspace/p2-4-compact-proof-20261125')
out = Path('/workspace/p24-owned-flags-preflight-repro-20261126/attempt-001')
pin = '6e616f4e0372555f7a78bcdba3e198d0e277eec8'
scope_sha = 'c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f'
template_sha = '5c2f7d5d006a2b2b33ef20be52216489a5262750b011d819b85badacf10bb1a3'
snapshot_path = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
snapshot_sha = 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
native_context = '71451bbb4a755fb5ec8744663121d0630ba5afd3d5774f7d0ec7931d9d387e90'
lean_sha = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
checker_sha = 'ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a'
expected_tools = {
    'verification/part2/run_winner9_private_checks.py': '164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac',
    'verification/part2/run_winner9_private_audit.py': '571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5',
    'verification/part2/winner9_private_audit_template.lean': '2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b',
    'verification/part2/export_winner9_private_evidence.py': 'fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645',
}
roots = [
    'ImbalancedChen.P2OriginalCompactQ80CompleteSoundness',
    'ImbalancedChen.P2OriginalCompactCachedRun',
    'ImbalancedChen.P2OriginalCompactQ80FixedBindings',
    'ImbalancedChen.P4AOrdinaryRootFirstIntegral',
    'ImbalancedChen.Part4ActualThirdFiniteDensityReserve',
]
finite = {
    'ImbalancedChen.P2OriginalCompactArchivedTotalCandidate',
    'ImbalancedChen.P2OriginalCompactCachedEndpointCandidate',
    'ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint',
}
template_b64 = 'aW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxDb21wYWN0UTgwQ29tcGxldGVTb3VuZG5lc3MKaW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxDb21wYWN0Q2FjaGVkUnVuCmltcG9ydCBJbWJhbGFuY2VkQ2hlbi5QMk9yaWdpbmFsQ29tcGFjdFE4MEZpeGVkQmluZGluZ3MKaW1wb3J0IEltYmFsYW5jZWRDaGVuLlA0QU9yZGluYXJ5Um9vdEZpcnN0SW50ZWdyYWwKaW1wb3J0IEltYmFsYW5jZWRDaGVuLlBhcnQ0QWN0dWFsVGhpcmRGaW5pdGVEZW5zaXR5UmVzZXJ2ZQppbXBvcnQgTGVhbi5VdGlsLkNvbGxlY3RBeGlvbXMKCi8tIERpYWdub3N0aWMgb25seTogbm8gaW5kZXBlbmRlbnQgcmVwbGF5IGFuZCBubyBmdWxsIGRlY2xhcmF0aW9uLXR5cGUgb3V0cHV0LgogICBUaGUgb3JpZ2luYWwgcGVyLW1vZHVsZSBhdWRpdCByZW1haW5zIHJlcXVpcmVkLiBObyBzb3VyY2Ugb3B0aW9ucyBhcmUgc2V0LiAtLwpvcGVuIExlYW4gRWxhYiBDb21tYW5kIGluCnJ1bl9jbWQgZG8KICBsZXQgZW52IOKGkCBnZXRFbnYKICBsZXQgZXhwZWN0ZWRNb2R1bGVzIDogQXJyYXkgTmFtZSA6PSAjWwpfX1AyNF9FWFBFQ1RFRF9NT0RVTEVfTkFNRVNfXwogIF0KICB1bmxlc3MgZXhwZWN0ZWRNb2R1bGVzLnNpemUgPT0gMzIxIGRvCiAgICB0aHJvd0Vycm9yICJXcm9uZyBzeW1ib2xpYyBkaWFnbm9zdGljIHNjb3BlIgogIGxldCBhY3R1YWxQcm9qZWN0IDo9IGVudi5oZWFkZXIubW9kdWxlTmFtZXMuZmlsdGVyIGZ1biBuID0+CiAgICBuLnRvU3RyaW5nLnN0YXJ0c1dpdGggIkltYmFsYW5jZWRDaGVuLiIKICB1bmxlc3MgYWN0dWFsUHJvamVjdC5xc29ydCBOYW1lLmx0ID09IGV4cGVjdGVkTW9kdWxlcy5xc29ydCBOYW1lLmx0IGRvCiAgICB0aHJvd0Vycm9yICJMb2FkZWQgcHJvamVjdCBtb2R1bGVzIGRpZmZlciBmcm9tIHRoZSBmaXhlZCBzeW1ib2xpYyBjbG9zdXJlIgogIGxpZnRJTyA8fCBJTy5wcmludGxuIHMhIlAyNF9GTEFHU19JTVBPUlRTIHsodG9Kc29uIChlbnYuaGVhZGVyLm1vZHVsZU5hbWVzLm1hcCBOYW1lLnRvU3RyaW5nKSkuY29tcHJlc3N9IgogIGxldCBtdXQgdGFyZ2V0SW5kaWNlcyA6IFN0ZC5IYXNoTWFwIE1vZHVsZUlkeCBOYW1lIDo9IHt9CiAgZm9yIG1vZHVsZU5hbWUgaW4gZXhwZWN0ZWRNb2R1bGVzIGRvCiAgICBsZXQgc29tZSBpZHggOj0gZW52LmdldE1vZHVsZUlkeD8gbW9kdWxlTmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgdGFyZ2V0IG1vZHVsZSB7bW9kdWxlTmFtZX0iCiAgICBpZiB0YXJnZXRJbmRpY2VzLmNvbnRhaW5zIGlkeCB0aGVuCiAgICAgIHRocm93RXJyb3IgIlJlcGVhdGVkIHRhcmdldCBtb2R1bGUvaW5kZXgge21vZHVsZU5hbWV9IgogICAgdGFyZ2V0SW5kaWNlcyA6PSB0YXJnZXRJbmRpY2VzLmluc2VydCBpZHggbW9kdWxlTmFtZQogIC0tIFNhbWUgb3duZXJzaGlwIGNyaXRlcmlvbiBhcyB0aGUgb3JpZ2luYWwgdGVtcGxhdGUsIGV2YWx1YXRlZCBpbiBvbmUgZm9sZC4KICAtLSBDb2RlLWdlbmVyYXRvci1vbmx5IGV4dHJhIG5hbWVzIGxhY2tpbmcgQ29uc3RhbnRJbmZvIGFyZSBleGNsdWRlZCBleGFjdGx5CiAgLS0gYXMgaW4gdGhhdCB0ZW1wbGF0ZTsgcHJpdmF0ZSBhbmQgZ2VuZXJhdGVkIHNlcmlhbGl6ZWQgbmFtZXMgYXJlIG5vdCBmaWx0ZXJlZC4KICBsZXQgYnVja2V0cyA6PSBlbnYuY29uc3QyTW9kSWR4LmZvbGQKICAgICAgKGluaXQgOj0gKHt9IDogU3RkLkhhc2hNYXAgTW9kdWxlSWR4IChBcnJheSBOYW1lKSkpIGZ1biBieU1vZHVsZSBuYW1lIGlkeCA9PgogICAgaWYgdGFyZ2V0SW5kaWNlcy5jb250YWlucyBpZHggJiYgKGVudi5maW5kPyBuYW1lKS5pc1NvbWUgdGhlbgogICAgICBieU1vZHVsZS5pbnNlcnQgaWR4ICgoKGJ5TW9kdWxlW2lkeF0/KS5nZXREICNbXSkucHVzaCBuYW1lKQogICAgZWxzZSBieU1vZHVsZQogIGxldCBtdXQgdG90YWxPd25lZCA6PSAwCiAgbGV0IG11dCB0b3RhbEJhZCA6PSAwCiAgbGV0IG11dCB0b3RhbFVuc2FmZSA6PSAwCiAgbGV0IG11dCB0b3RhbFBhcnRpYWwgOj0gMAogIGxldCBtdXQgdG90YWxBeGlvbSA6PSAwCiAgbGV0IG11dCB0b3RhbEZvcmJpZGRlbkF4aW9tIDo9IDAKICBmb3IgbW9kdWxlTmFtZSBpbiBleHBlY3RlZE1vZHVsZXMgZG8KICAgIGxpZnRJTyA8fCBJTy5wcmludGxuIHMhIlAyNF9GTEFHU19TVEFSVCB7bW9kdWxlTmFtZX0iCiAgICBsZXQgc29tZSBpZHggOj0gZW52LmdldE1vZHVsZUlkeD8gbW9kdWxlTmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgdGFyZ2V0IG1vZHVsZSB7bW9kdWxlTmFtZX0iCiAgICBsZXQgbmFtZXMgOj0gKGJ1Y2tldHNbaWR4XT8pLmdldEQgI1tdCiAgICBsZXQgbXV0IHNlcmlhbGl6ZWQgOiBBcnJheSBOYW1lIDo9ICNbXQogICAgbGV0IG11dCBmb3VuZCA6PSBmYWxzZQogICAgZm9yIGkgaW4gTGlzdC5yYW5nZSBlbnYuaGVhZGVyLm1vZHVsZXMuc2l6ZSBkbwogICAgICBsZXQgaW1wb3J0ZWQgOj0gZW52LmhlYWRlci5tb2R1bGVzW2ldIQogICAgICBpZiBpbXBvcnRlZC5tb2R1bGUgPT0gbW9kdWxlTmFtZSB0aGVuCiAgICAgICAgaWYgZm91bmQgdGhlbiB0aHJvd0Vycm9yICJEdXBsaWNhdGUgbW9kdWxlIHttb2R1bGVOYW1lfSIKICAgICAgICBmb3VuZCA6PSB0cnVlCiAgICAgICAgbGV0IGRhdGEgOj0gZW52LmhlYWRlci5tb2R1bGVEYXRhW2ldIQogICAgICAgIGlmIGRhdGEuaXNNb2R1bGUgfHwgIWltcG9ydGVkLmltcG9ydEFsbCB8fCAhaW1wb3J0ZWQuaGFzRGF0YSB0aGVuCiAgICAgICAgICB0aHJvd0Vycm9yICJJbmNvbXBsZXRlIGltcG9ydGVkIGxlZ2FjeSBkYXRhIGZvciB7bW9kdWxlTmFtZX0iCiAgICAgICAgc2VyaWFsaXplZCA6PSBkYXRhLmNvbnN0TmFtZXMKICAgIHVubGVzcyBmb3VuZCAmJiBuYW1lcy5zaXplID4gMCAmJiBuYW1lcy5xc29ydCBOYW1lLmx0ID09IHNlcmlhbGl6ZWQucXNvcnQgTmFtZS5sdCBkbwogICAgICB0aHJvd0Vycm9yICJDb21wbGV0ZSBzZXJpYWxpemVkL2Vudmlyb25tZW50IGludmVudG9yeSBtaXNtYXRjaCBmb3Ige21vZHVsZU5hbWV9IgogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X0ZMQUdTX0lOVkVOVE9SWSB7KEpzb24ubWtPYmogWygibW9kdWxlIiwgdG9Kc29uIG1vZHVsZU5hbWUudG9TdHJpbmcpLCAoIm1vZHVsZV9pbmRleCIsIHRvSnNvbiBpZHgudG9OYXQpLCAoInNlcmlhbGl6ZWQiLCB0b0pzb24gKHNlcmlhbGl6ZWQubWFwIE5hbWUudG9TdHJpbmcpKSwgKCJlbnZpcm9ubWVudCIsIHRvSnNvbiAobmFtZXMubWFwIE5hbWUudG9TdHJpbmcpKV0pLmNvbXByZXNzfSIKICAgIGxldCBtdXQgY2hlY2tlZCA6PSAwCiAgICBsZXQgbXV0IGJhZCA6PSAwCiAgICBsZXQgbXV0IHVuc2FmZUNvdW50IDo9IDAKICAgIGxldCBtdXQgcGFydGlhbENvdW50IDo9IDAKICAgIGxldCBtdXQgYXhpb21Db3VudCA6PSAwCiAgICBsZXQgbXV0IGZvcmJpZGRlbkF4aW9tQ291bnQgOj0gMAogICAgZm9yIG5hbWUgaW4gbmFtZXMucXNvcnQgTmFtZS5sdCBkbwogICAgICB1bmxlc3MgZW52LmdldE1vZHVsZUlkeEZvcj8gbmFtZSA9PSBzb21lIGlkeCBkbwogICAgICAgIHRocm93RXJyb3IgIkRlY2xhcmF0aW9uIG93bmVyc2hpcCBjaGFuZ2VkIGZvciB7bmFtZX0iCiAgICAgIGxldCBzb21lIGluZm8gOj0gZW52LmZpbmQ/IG5hbWUgfCB0aHJvd0Vycm9yICJNaXNzaW5nIGludmVudG9yaWVkIGRlY2xhcmF0aW9uIHtuYW1lfSIKICAgICAgbGV0IGF4aW9tcyDihpAgY29sbGVjdEF4aW9tcyBuYW1lCiAgICAgIGxldCBmb3JiaWRkZW4gOj0gYXhpb21zLmZpbHRlciBmdW4gYXggPT4KICAgICAgICAhKCNbYHByb3BleHQsIGBDbGFzc2ljYWwuY2hvaWNlLCBgUXVvdC5zb3VuZF0uY29udGFpbnMgYXgpCiAgICAgIGNoZWNrZWQgOj0gY2hlY2tlZCArIDEKICAgICAgaWYgaW5mby5pc1Vuc2FmZSB0aGVuIHVuc2FmZUNvdW50IDo9IHVuc2FmZUNvdW50ICsgMQogICAgICBpZiBpbmZvLmlzUGFydGlhbCB0aGVuIHBhcnRpYWxDb3VudCA6PSBwYXJ0aWFsQ291bnQgKyAxCiAgICAgIGlmIGluZm8uaXNBeGlvbSB0aGVuIGF4aW9tQ291bnQgOj0gYXhpb21Db3VudCArIDEKICAgICAgaWYgIWZvcmJpZGRlbi5pc0VtcHR5IHRoZW4gZm9yYmlkZGVuQXhpb21Db3VudCA6PSBmb3JiaWRkZW5BeGlvbUNvdW50ICsgMQogICAgICBpZiBpbmZvLmlzVW5zYWZlIHx8IGluZm8uaXNQYXJ0aWFsIHx8IGluZm8uaXNBeGlvbSB8fCAhZm9yYmlkZGVuLmlzRW1wdHkgdGhlbgogICAgICAgIGJhZCA6PSBiYWQgKyAxCiAgICAgICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X0ZMQUdTX0JBRCB7KEpzb24ubWtPYmogWygibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksICgidW5zYWZlIiwgdG9Kc29uIGluZm8uaXNVbnNhZmUpLCAoInBhcnRpYWwiLCB0b0pzb24gaW5mby5pc1BhcnRpYWwpLCAoImF4aW9tIiwgdG9Kc29uIGluZm8uaXNBeGlvbSksICgiYXhpb21zIiwgdG9Kc29uIChheGlvbXMubWFwIE5hbWUudG9TdHJpbmcpKSwgKCJmb3JiaWRkZW5fYXhpb21zIiwgdG9Kc29uIChmb3JiaWRkZW4ubWFwIE5hbWUudG9TdHJpbmcpKV0pLmNvbXByZXNzfSIKICAgIHRvdGFsT3duZWQgOj0gdG90YWxPd25lZCArIGNoZWNrZWQKICAgIHRvdGFsQmFkIDo9IHRvdGFsQmFkICsgYmFkCiAgICB0b3RhbFVuc2FmZSA6PSB0b3RhbFVuc2FmZSArIHVuc2FmZUNvdW50CiAgICB0b3RhbFBhcnRpYWwgOj0gdG90YWxQYXJ0aWFsICsgcGFydGlhbENvdW50CiAgICB0b3RhbEF4aW9tIDo9IHRvdGFsQXhpb20gKyBheGlvbUNvdW50CiAgICB0b3RhbEZvcmJpZGRlbkF4aW9tIDo9IHRvdGFsRm9yYmlkZGVuQXhpb20gKyBmb3JiaWRkZW5BeGlvbUNvdW50CiAgICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMjRfRkxBR1NfTU9EVUxFIHsoSnNvbi5ta09iaiBbKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksICgibW9kdWxlX2luZGV4IiwgdG9Kc29uIGlkeC50b05hdCksICgic2VyaWFsaXplZF9jb3VudCIsIHRvSnNvbiBzZXJpYWxpemVkLnNpemUpLCAoImVudmlyb25tZW50X2NvdW50IiwgdG9Kc29uIG5hbWVzLnNpemUpLCAoImNoZWNrZWQiLCB0b0pzb24gY2hlY2tlZCksICgiYmFkX2RlY2xhcmF0aW9ucyIsIHRvSnNvbiBiYWQpLCAoInVuc2FmZV9jb3VudCIsIHRvSnNvbiB1bnNhZmVDb3VudCksICgicGFydGlhbF9jb3VudCIsIHRvSnNvbiBwYXJ0aWFsQ291bnQpLCAoImF4aW9tX2NvdW50IiwgdG9Kc29uIGF4aW9tQ291bnQpLCAoImZvcmJpZGRlbl9heGlvbV9kZWNsYXJhdGlvbnMiLCB0b0pzb24gZm9yYmlkZGVuQXhpb21Db3VudCldKS5jb21wcmVzc30iCiAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X0ZMQUdTX0NPTVBMRVRFIHsoSnNvbi5ta09iaiBbKCJtb2R1bGVzIiwgdG9Kc29uIGV4cGVjdGVkTW9kdWxlcy5zaXplKSwgKCJjaGVja2VkIiwgdG9Kc29uIHRvdGFsT3duZWQpLCAoImJhZF9kZWNsYXJhdGlvbnMiLCB0b0pzb24gdG90YWxCYWQpLCAoInVuc2FmZV9jb3VudCIsIHRvSnNvbiB0b3RhbFVuc2FmZSksICgicGFydGlhbF9jb3VudCIsIHRvSnNvbiB0b3RhbFBhcnRpYWwpLCAoImF4aW9tX2NvdW50IiwgdG9Kc29uIHRvdGFsQXhpb20pLCAoImZvcmJpZGRlbl9heGlvbV9kZWNsYXJhdGlvbnMiLCB0b0pzb24gdG90YWxGb3JiaWRkZW5BeGlvbSksICgiYWxsX2ZsYWdzX2F4aW9tc19jbGVhciIsIHRvSnNvbiAodG90YWxCYWQgPT0gMCkpLCAoImRpYWdub3N0aWNfb25seSIsIHRvSnNvbiB0cnVlKSwgKCJmdWxsX3R5cGVfYXVkaXQiLCB0b0pzb24gZmFsc2UpLCAoImluZGVwZW5kZW50X3JlcGxheSIsIHRvSnNvbiBmYWxzZSksICgiYWNjZXB0YW5jZV9jcmVkaXQiLCB0b0pzb24gZmFsc2UpXSkuY29tcHJlc3N9IgogIGlmIHRvdGFsQmFkID4gMCB0aGVuCiAgICB0aHJvd0Vycm9yICJBZ2dyZWdhdGUgb3duZWQgZmxhZy9heGlvbSBkaWFnbm9zdGljIGZvdW5kIHt0b3RhbEJhZH0gZGVjbGFyYXRpb24ocyk7IHNlZSBhbGwgUDI0X0ZMQUdTX0JBRCByZWNvcmRzIgo='
credits = {'diagnostic_only': True, 'compile_credit': False, 'kernel_replay_credit': False,
           'owned_audit_credit': False, 'finite_A_credit': False, 'finite_B_credit': False,
           'whole_functional_credit': False, 'full_p2_complete': False, 'acceptance_credit': False}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def write_json(path, value):
    with path.open('x', encoding='utf-8') as stream:
        json.dump(value, stream, ensure_ascii=False, sort_keys=True, indent=2)
        stream.write('\n')

def check_source():
    require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == pin,
            'Production pin changed')
    require(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                       cwd=root, text=True).strip(), 'Tracked source dirty')
    for relative, expected in expected_tools.items():
        require(digest(root / relative) == expected, 'Original tool changed: ' + relative)

check_source()
require(not out.exists(), 'Preserve existing persistent reproduction directory')
sys.path.insert(0, str(root / 'verification/part2'))
from run_winner9_private_audit import (LEAN, LEANCHECKER, MATHLIB, PIN as MATHLIB_PIN,
                                     project_nodes, snapshot, verify_compilation)
from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes

full_nodes = project_nodes(root, 'ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint')
full = list(full_nodes)
require(len(full) == len(set(full)) == 324, 'Wrong full scope')
require(hashlib.sha256(('\n'.join(full) + '\n').encode()).hexdigest() == scope_sha,
        'Ordered full324 scope changed')
symbolic = set().union(*(set(project_nodes(root, name)) for name in roots))
require(len(symbolic) == 321 and set(full) - symbolic == finite, 'Wrong symbolic partition')
modules = [name for name in full if name in symbolic]
require(all(re.fullmatch(r'ImbalancedChen(?:\.[A-Za-z_][A-Za-z_0-9]*)+', name) for name in modules),
        'Cannot render exact module names as Lean literals')
nodes = {name: full_nodes[name] for name in modules}
registry = root / '.lake/p2-private/records.json'
registry_before = digest(registry)
records = json.loads(registry.read_text())
require(digest(LEAN) == lean_sha and digest(LEANCHECKER) == checker_sha, 'Wrong runtime bytes')
require(digest(snapshot_path) == snapshot_sha, 'Original external snapshot changed')
require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=MATHLIB,
                                text=True).strip() == MATHLIB_PIN, 'Wrong Mathlib pin')
toolchain = {'lean_version': subprocess.check_output([LEAN, '--version'], text=True).strip(),
             'lean_binary_sha256': lean_sha, 'mathlib_commit': MATHLIB_PIN}
lib = root / '.lake/p2-private/lib'
external = ExternalSnapshot(snapshot_path, lean=LEAN, mathlib_pin=MATHLIB_PIN, project_lib=lib)
native_before = external.verify()
require(native_before['snapshot_sha256'] == snapshot_sha
        and native_before['context_signature'] == native_context, 'Qualified native binding changed')
require(Path(external.value['runtime']['leanchecker']).resolve() == Path(LEANCHECKER).resolve(),
        'Wrong native checker')
require(external.files[external.value['runtime']['leanchecker']]['sha256'] == checker_sha,
        'Native checker hash differs')
mark_project_nodes(full_nodes, set(external.modules))
before = snapshot(root, lib, full_nodes, toolchain, external)
# Read-only validation; do not invoke the original compiler or its registry writer.
verify_compilation(records, nodes, before)
template = base64.b64decode(template_b64, validate=True)
require(hashlib.sha256(template).hexdigest() == template_sha, 'Original diagnostic template changed')
token = '__P24_EXPECTED_MODULE_NAMES__'
require(template.decode().count(token) == 1, 'Unexpected substitution boundary')
source = template.decode().replace(token, ',\n'.join('    `' + name for name in modules)).encode()
out.mkdir(parents=True, exist_ok=False)
(out / 'OwnedFlags.template.lean').write_bytes(template)
(out / 'OwnedFlags.lean').write_bytes(source)
write_json(out / 'scope.json', {'full324': full, 'symbolic321': modules, 'roots': roots,
                              'ordered324_sha256': scope_sha})
write_json(out / 'inputs-before.json', {'snapshot': before, 'registry_sha256': registry_before,
                                      'native': native_before})
flags = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000']
command = [LEAN, *flags, str(out / 'OwnedFlags.lean')]
log = out / 'owned-flags.log'
receipt = {'source_pin': pin, 'original_template_sha256': template_sha,
           'rendered_source_sha256': hashlib.sha256(source).hexdigest(),
           'registry_sha256_before': registry_before, 'symbolic_scope': 321,
           'ordered324_sha256': scope_sha, 'command': command,
           'original_verify_compilation_readonly_passed': True,
           'zero_budget_driver_repeated': False, 'native_qualification_repeated': False,
           'production_module_compilation_started': False, **credits}
print(json.dumps({'phase': 'original_flags_child_reproduction_start', 'directory': str(out),
                  **receipt}), flush=True)
started = time.monotonic()
try:
    with log.open('xb') as stream:
        child = subprocess.run(command, cwd=root, env=external.environment(dict(os.environ)),
                               stdout=stream, stderr=subprocess.STDOUT)
    receipt['child_exit_code'] = child.returncode
    receipt['child_seconds'] = time.monotonic() - started
except Exception as error:
    receipt['execution_error'] = type(error).__name__ + ': ' + str(error)
finally:
    errors = []
    try:
        check_source()
        after = snapshot(root, lib, full_nodes, toolchain, external)
        native_after = external.verify()
        registry_after = digest(registry)
        write_json(out / 'inputs-after.json', {'snapshot': after, 'registry_sha256': registry_after,
                                             'native': native_after})
        require(after == before, 'Protected full324 source/object/tools changed')
        require(registry_after == registry_before, 'Compile registry changed')
        require(native_after == native_before, 'Qualified native binding changed')
        require(digest(out / 'OwnedFlags.lean') == receipt['rendered_source_sha256'], 'Diagnostic source changed')
        require(digest(out / 'OwnedFlags.template.lean') == template_sha, 'Diagnostic template changed')
    except Exception as error:
        errors.append(type(error).__name__ + ': ' + str(error))
    receipt['protected_inputs_unchanged'] = not errors
    receipt['postcheck_errors'] = errors
    if log.is_file():
        receipt['child_log_path'] = str(log)
        receipt['child_log_bytes'] = log.stat().st_size
        receipt['child_log_sha256'] = digest(log)
        if log.stat().st_size <= 20 * 1024:
            raw = log.read_bytes()
            receipt['complete_small_child_log_base64'] = base64.b64encode(raw).decode('ascii')
            receipt['mcp_child_log_complete'] = True
            print('P24_FLAGS_REPRO_COMPLETE_CHILD_LOG_BEGIN', flush=True)
            sys.stdout.buffer.write(raw)
            if not raw.endswith(b'\n'):
                sys.stdout.buffer.write(b'\n')
            sys.stdout.buffer.flush()
            print('P24_FLAGS_REPRO_COMPLETE_CHILD_LOG_END', flush=True)
        else:
            receipt['mcp_child_log_complete'] = False
            receipt['child_log_retrieval'] = 'Full original log persists at child_log_path; no truncated substitute printed.'
    receipt['reproduction_recorded'] = ('child_exit_code' in receipt and not errors)
    write_json(out / 'diagnostic.json', receipt)
    print(json.dumps({'phase': 'original_flags_child_reproduction_complete',
                      'receipt_path': str(out / 'diagnostic.json'),
                      'receipt_sha256': digest(out / 'diagnostic.json'), **receipt}), flush=True)
raise SystemExit(0 if receipt.get('reproduction_recorded') else 1)
P24_FLAGS_REPRO_PY
