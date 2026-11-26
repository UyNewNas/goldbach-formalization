#!/usr/bin/env bash
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_FLAGS_RISK_SCAN_PY'
import base64
from collections import Counter
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

root = Path('/workspace/p2-4-compact-proof-20261125')
out = Path('/workspace/p24-owned-flags-preflight-repro-20261126/attempt-003')
OUT = out
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
pin = '6e616f4e0372555f7a78bcdba3e198d0e277eec8'
scope_sha = 'c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f'
template_sha = 'a0ee662eaaa93cecc572bb0a6e9fd1c6acee4f37605efcc44f194e4d78ae8714'
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
template_b64 = 'aW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxDb21wYWN0UTgwQ29tcGxldGVTb3VuZG5lc3MKaW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxDb21wYWN0Q2FjaGVkUnVuCmltcG9ydCBJbWJhbGFuY2VkQ2hlbi5QMk9yaWdpbmFsQ29tcGFjdFE4MEZpeGVkQmluZGluZ3MKaW1wb3J0IEltYmFsYW5jZWRDaGVuLlA0QU9yZGluYXJ5Um9vdEZpcnN0SW50ZWdyYWwKaW1wb3J0IEltYmFsYW5jZWRDaGVuLlBhcnQ0QWN0dWFsVGhpcmRGaW5pdGVEZW5zaXR5UmVzZXJ2ZQppbXBvcnQgTGVhbi5VdGlsLkNvbGxlY3RBeGlvbXMKCi8tIEF1eGlsaWFyeSByaXNrIHJlcG9ydCBvbmx5LiBJbnZlbnRvcnkgbWlzbWF0Y2hlcyBhcmUgcHJlc2VydmVkIGFuZCByZXBvcnRlZCwKICAgbmV2ZXIgYWNjZXB0ZWQuIFRoZSB1bmNoYW5nZWQgb3JpZ2luYWwgYXVkaXQgc3RpbGwgcmVxdWlyZXMgZXhhY3QgZXF1YWxpdHkuIC0vCm9wZW4gTGVhbiBFbGFiIENvbW1hbmQgaW4KcnVuX2NtZCBkbwogIGxldCBlbnYg4oaQIGdldEVudgogIGxldCBleHBlY3RlZE1vZHVsZXMgOiBBcnJheSBOYW1lIDo9ICNbCl9fUDI0X0VYUEVDVEVEX01PRFVMRV9OQU1FU19fCiAgXQogIHVubGVzcyBleHBlY3RlZE1vZHVsZXMuc2l6ZSA9PSAzMjEgZG8gdGhyb3dFcnJvciAiV3Jvbmcgc3ltYm9saWMgc2NvcGUiCiAgbGV0IGFjdHVhbFByb2plY3QgOj0gZW52LmhlYWRlci5tb2R1bGVOYW1lcy5maWx0ZXIgZnVuIG4gPT4KICAgIG4udG9TdHJpbmcuc3RhcnRzV2l0aCAiSW1iYWxhbmNlZENoZW4uIgogIHVubGVzcyBhY3R1YWxQcm9qZWN0LnFzb3J0IE5hbWUubHQgPT0gZXhwZWN0ZWRNb2R1bGVzLnFzb3J0IE5hbWUubHQgZG8KICAgIHRocm93RXJyb3IgIkxvYWRlZCBwcm9qZWN0IG1vZHVsZXMgZGlmZmVyIGZyb20gZml4ZWQgc3ltYm9saWMgY2xvc3VyZSIKICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMjRfRkxBR1NfSU1QT1JUUyB7KHRvSnNvbiAoZW52LmhlYWRlci5tb2R1bGVOYW1lcy5tYXAgTmFtZS50b1N0cmluZykpLmNvbXByZXNzfSIKICBsZXQgbXV0IHRhcmdldEluZGljZXMgOiBTdGQuSGFzaE1hcCBNb2R1bGVJZHggTmFtZSA6PSB7fQogIGZvciBtb2R1bGVOYW1lIGluIGV4cGVjdGVkTW9kdWxlcyBkbwogICAgbGV0IHNvbWUgaWR4IDo9IGVudi5nZXRNb2R1bGVJZHg/IG1vZHVsZU5hbWUgfCB0aHJvd0Vycm9yICJNaXNzaW5nIG1vZHVsZSB7bW9kdWxlTmFtZX0iCiAgICBpZiB0YXJnZXRJbmRpY2VzLmNvbnRhaW5zIGlkeCB0aGVuIHRocm93RXJyb3IgIkR1cGxpY2F0ZSB0YXJnZXQgbW9kdWxlL2luZGV4IHttb2R1bGVOYW1lfSIKICAgIHRhcmdldEluZGljZXMgOj0gdGFyZ2V0SW5kaWNlcy5pbnNlcnQgaWR4IG1vZHVsZU5hbWUKICBsZXQgYnVja2V0cyA6PSBlbnYuY29uc3QyTW9kSWR4LmZvbGQKICAgICAgKGluaXQgOj0gKHt9IDogU3RkLkhhc2hNYXAgTW9kdWxlSWR4IChBcnJheSBOYW1lKSkpIGZ1biBieU1vZHVsZSBuYW1lIGlkeCA9PgogICAgaWYgdGFyZ2V0SW5kaWNlcy5jb250YWlucyBpZHggJiYgKGVudi5maW5kPyBuYW1lKS5pc1NvbWUgdGhlbgogICAgICBieU1vZHVsZS5pbnNlcnQgaWR4ICgoKGJ5TW9kdWxlW2lkeF0/KS5nZXREICNbXSkucHVzaCBuYW1lKQogICAgZWxzZSBieU1vZHVsZQogIGxldCBtdXQgdG90YWxDaGVja2VkIDogTmF0IDo9IDAKICBsZXQgbXV0IHRvdGFsQ2FuZGlkYXRlcyA6IE5hdCA6PSAwCiAgbGV0IG11dCB0b3RhbE1pc3NpbmcgOiBOYXQgOj0gMAogIGxldCBtdXQgdG90YWxCYWQgOiBOYXQgOj0gMAogIGxldCBtdXQgdG90YWxJc3N1ZXMgOiBOYXQgOj0gMAogIGxldCBtdXQgdG90YWxNaXNtYXRjaCA6IE5hdCA6PSAwCiAgZm9yIG1vZHVsZU5hbWUgaW4gZXhwZWN0ZWRNb2R1bGVzIGRvCiAgICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMjRfRkxBR1NfU1RBUlQge21vZHVsZU5hbWV9IgogICAgbGV0IHNvbWUgaWR4IDo9IGVudi5nZXRNb2R1bGVJZHg/IG1vZHVsZU5hbWUgfCB0aHJvd0Vycm9yICJNaXNzaW5nIG1vZHVsZSB7bW9kdWxlTmFtZX0iCiAgICBsZXQgbmFtZXMgOj0gKGJ1Y2tldHNbaWR4XT8pLmdldEQgI1tdCiAgICBsZXQgbXV0IHNlcmlhbGl6ZWQgOiBBcnJheSBOYW1lIDo9ICNbXQogICAgbGV0IG11dCBlbnRyaWVzIDogQXJyYXkgSnNvbiA6PSAjW10KICAgIGxldCBtdXQgbGVnYWN5RGF0YU9LIDo9IHRydWUKICAgIGZvciBpIGluIExpc3QucmFuZ2UgZW52LmhlYWRlci5tb2R1bGVzLnNpemUgZG8KICAgICAgbGV0IGltcG9ydGVkIDo9IGVudi5oZWFkZXIubW9kdWxlc1tpXSEKICAgICAgaWYgaW1wb3J0ZWQubW9kdWxlID09IG1vZHVsZU5hbWUgdGhlbgogICAgICAgIGxldCBkYXRhIDo9IGVudi5oZWFkZXIubW9kdWxlRGF0YVtpXSEKICAgICAgICBpZiBkYXRhLmlzTW9kdWxlIHx8ICFpbXBvcnRlZC5pbXBvcnRBbGwgfHwgIWltcG9ydGVkLmhhc0RhdGEgdGhlbgogICAgICAgICAgbGVnYWN5RGF0YU9LIDo9IGZhbHNlCiAgICAgICAgZW50cmllcyA6PSBlbnRyaWVzLnB1c2ggPHwgSnNvbi5ta09iaiBbKCJtb2R1bGVfaW5kZXgiLCB0b0pzb24gaSksCiAgICAgICAgICAoImRhdGFfaXNfbW9kdWxlIiwgdG9Kc29uIGRhdGEuaXNNb2R1bGUpLCAoImltcG9ydF9hbGwiLCB0b0pzb24gaW1wb3J0ZWQuaW1wb3J0QWxsKSwKICAgICAgICAgICgiaGFzX2RhdGEiLCB0b0pzb24gaW1wb3J0ZWQuaGFzRGF0YSksICgic2VyaWFsaXplZF9jb3VudCIsIHRvSnNvbiBkYXRhLmNvbnN0TmFtZXMuc2l6ZSldCiAgICAgICAgc2VyaWFsaXplZCA6PSBzZXJpYWxpemVkICsrIGRhdGEuY29uc3ROYW1lcwogICAgbGV0IGludmVudG9yeU9LIDo9IGVudHJpZXMuc2l6ZSA9PSAxICYmIGxlZ2FjeURhdGFPSyAmJiBuYW1lcy5zaXplID4gMCAmJgogICAgICBuYW1lcy5xc29ydCBOYW1lLmx0ID09IHNlcmlhbGl6ZWQucXNvcnQgTmFtZS5sdAogICAgaWYgIWludmVudG9yeU9LIHRoZW4gdG90YWxNaXNtYXRjaCA6PSB0b3RhbE1pc21hdGNoICsgMQogICAgbGV0IGVudlNldCA6PSBuYW1lcy5mb2xkbCAoaW5pdCA6PSAoe30gOiBTdGQuSGFzaE1hcCBOYW1lIFVuaXQpKSBmdW4gcyBuID0+IHMuaW5zZXJ0IG4gKCkKICAgIGxldCBzZXJTZXQgOj0gc2VyaWFsaXplZC5mb2xkbCAoaW5pdCA6PSAoe30gOiBTdGQuSGFzaE1hcCBOYW1lIFVuaXQpKSBmdW4gcyBuID0+IHMuaW5zZXJ0IG4gKCkKICAgIGxldCB1bmlvblNldCA6PSBzZXJpYWxpemVkLmZvbGRsIChpbml0IDo9IGVudlNldCkgZnVuIHMgbiA9PiBzLmluc2VydCBuICgpCiAgICBsZXQgY2FuZGlkYXRlcyA6PSAodW5pb25TZXQuZm9sZCAoaW5pdCA6PSAoI1tdIDogQXJyYXkgTmFtZSkpIGZ1biBucyBuIF8gPT4gbnMucHVzaCBuKS5xc29ydCBOYW1lLmx0CiAgICBsZXQgc2VyaWFsaXplZE9ubHkgOj0gKHNlcmlhbGl6ZWQuZmlsdGVyIGZ1biBuID0+ICFlbnZTZXQuY29udGFpbnMgbikucXNvcnQgTmFtZS5sdAogICAgbGV0IGVudmlyb25tZW50T25seSA6PSAobmFtZXMuZmlsdGVyIGZ1biBuID0+ICFzZXJTZXQuY29udGFpbnMgbikucXNvcnQgTmFtZS5sdAogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X0ZMQUdTX0lOVkVOVE9SWSB7KEpzb24ubWtPYmogWygibW9kdWxlIiwgdG9Kc29uIG1vZHVsZU5hbWUudG9TdHJpbmcpLCAoIm1vZHVsZV9pbmRleCIsIHRvSnNvbiBpZHgudG9OYXQpLCAoImludmVudG9yeV9vayIsIHRvSnNvbiBpbnZlbnRvcnlPSyksICgibGVnYWN5X2RhdGFfb2siLCB0b0pzb24gbGVnYWN5RGF0YU9LKSwgKCJoZWFkZXJfZW50cmllcyIsIHRvSnNvbiBlbnRyaWVzKSwgKCJzZXJpYWxpemVkIiwgdG9Kc29uIChzZXJpYWxpemVkLm1hcCBOYW1lLnRvU3RyaW5nKSksICgiZW52aXJvbm1lbnQiLCB0b0pzb24gKG5hbWVzLm1hcCBOYW1lLnRvU3RyaW5nKSksICgic2VyaWFsaXplZF9vbmx5IiwgdG9Kc29uIChzZXJpYWxpemVkT25seS5tYXAgTmFtZS50b1N0cmluZykpLCAoImVudmlyb25tZW50X29ubHkiLCB0b0pzb24gKGVudmlyb25tZW50T25seS5tYXAgTmFtZS50b1N0cmluZykpXSkuY29tcHJlc3N9IgogICAgbGV0IG11dCBjaGVja2VkTmFtZXMgOiBBcnJheSBOYW1lIDo9ICNbXQogICAgbGV0IG11dCBtaXNzaW5nTmFtZXMgOiBBcnJheSBOYW1lIDo9ICNbXQogICAgbGV0IG11dCBiYWQgOiBOYXQgOj0gMAogICAgbGV0IG11dCBpc3N1ZXMgOiBOYXQgOj0gMAogICAgbGV0IG11dCB1bnNhZmVDb3VudCA6IE5hdCA6PSAwCiAgICBsZXQgbXV0IHBhcnRpYWxDb3VudCA6IE5hdCA6PSAwCiAgICBsZXQgbXV0IGF4aW9tQ291bnQgOiBOYXQgOj0gMAogICAgbGV0IG11dCBmb3JiaWRkZW5Db3VudCA6IE5hdCA6PSAwCiAgICBmb3IgbmFtZSBpbiBjYW5kaWRhdGVzIGRvCiAgICAgIGxldCBvd25lciA6PSBlbnYuZ2V0TW9kdWxlSWR4Rm9yPyBuYW1lCiAgICAgIGxldCBvd25lck5hbWUgOj0gb3duZXIuYmluZCBmdW4gaSA9PiBlbnYuaGVhZGVyLm1vZHVsZU5hbWVzW2ldPwogICAgICBsZXQgaW5mbz8gOj0gZW52LmZpbmQ/IG5hbWUKICAgICAgbGV0IGluU2VyaWFsaXplZCA6PSBzZXJTZXQuY29udGFpbnMgbmFtZQogICAgICBsZXQgaW5FbnZpcm9ubWVudCA6PSBlbnZTZXQuY29udGFpbnMgbmFtZQogICAgICBsZXQgb3duZXJPSyA6PSBvd25lciA9PSBzb21lIGlkeAogICAgICBpZiAhaW5TZXJpYWxpemVkIHx8ICFpbkVudmlyb25tZW50IHx8ICFvd25lck9LIHx8IGluZm8/LmlzTm9uZSB0aGVuCiAgICAgICAgaXNzdWVzIDo9IGlzc3VlcyArIDEKICAgICAgICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMjRfRkxBR1NfREVDTF9JU1NVRSB7KEpzb24ubWtPYmogWygibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksICgiZXhwZWN0ZWRfbW9kdWxlX2luZGV4IiwgdG9Kc29uIGlkeC50b05hdCksICgib3duZXJfaW5kZXgiLCB0b0pzb24gKG93bmVyLm1hcCBNb2R1bGVJZHgudG9OYXQpKSwgKCJvd25lcl9tb2R1bGUiLCB0b0pzb24gKG93bmVyTmFtZS5tYXAgTmFtZS50b1N0cmluZykpLCAoImluX3NlcmlhbGl6ZWQiLCB0b0pzb24gaW5TZXJpYWxpemVkKSwgKCJpbl9lbnZpcm9ubWVudCIsIHRvSnNvbiBpbkVudmlyb25tZW50KSwgKCJvd25lcl9tYXRjaGVzIiwgdG9Kc29uIG93bmVyT0spLCAoIm1pc3NpbmdfY29uc3RhbnRfaW5mbyIsIHRvSnNvbiBpbmZvPy5pc05vbmUpXSkuY29tcHJlc3N9IgogICAgICBtYXRjaCBpbmZvPyB3aXRoCiAgICAgIHwgbm9uZSA9PiBtaXNzaW5nTmFtZXMgOj0gbWlzc2luZ05hbWVzLnB1c2ggbmFtZQogICAgICB8IHNvbWUgaW5mbyA9PgogICAgICAgIGxldCBheGlvbXMg4oaQIGNvbGxlY3RBeGlvbXMgbmFtZQogICAgICAgIGxldCBmb3JiaWRkZW4gOj0gYXhpb21zLmZpbHRlciBmdW4gYXggPT4KICAgICAgICAgICEoI1tgcHJvcGV4dCwgYENsYXNzaWNhbC5jaG9pY2UsIGBRdW90LnNvdW5kXS5jb250YWlucyBheCkKICAgICAgICBjaGVja2VkTmFtZXMgOj0gY2hlY2tlZE5hbWVzLnB1c2ggbmFtZQogICAgICAgIGlmIGluZm8uaXNVbnNhZmUgdGhlbiB1bnNhZmVDb3VudCA6PSB1bnNhZmVDb3VudCArIDEKICAgICAgICBpZiBpbmZvLmlzUGFydGlhbCB0aGVuIHBhcnRpYWxDb3VudCA6PSBwYXJ0aWFsQ291bnQgKyAxCiAgICAgICAgaWYgaW5mby5pc0F4aW9tIHRoZW4gYXhpb21Db3VudCA6PSBheGlvbUNvdW50ICsgMQogICAgICAgIGlmICFmb3JiaWRkZW4uaXNFbXB0eSB0aGVuIGZvcmJpZGRlbkNvdW50IDo9IGZvcmJpZGRlbkNvdW50ICsgMQogICAgICAgIGlmIGluZm8uaXNVbnNhZmUgfHwgaW5mby5pc1BhcnRpYWwgfHwgaW5mby5pc0F4aW9tIHx8ICFmb3JiaWRkZW4uaXNFbXB0eSB0aGVuCiAgICAgICAgICBiYWQgOj0gYmFkICsgMQogICAgICAgICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X0ZMQUdTX0JBRCB7KEpzb24ubWtPYmogWygibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksICgib3duZXJfaW5kZXgiLCB0b0pzb24gKG93bmVyLm1hcCBNb2R1bGVJZHgudG9OYXQpKSwgKCJvd25lcl9tb2R1bGUiLCB0b0pzb24gKG93bmVyTmFtZS5tYXAgTmFtZS50b1N0cmluZykpLCAoIm93bmVyX21hdGNoZXMiLCB0b0pzb24gb3duZXJPSyksICgiaW5fc2VyaWFsaXplZCIsIHRvSnNvbiBpblNlcmlhbGl6ZWQpLCAoImluX2Vudmlyb25tZW50IiwgdG9Kc29uIGluRW52aXJvbm1lbnQpLCAoInVuc2FmZSIsIHRvSnNvbiBpbmZvLmlzVW5zYWZlKSwgKCJwYXJ0aWFsIiwgdG9Kc29uIGluZm8uaXNQYXJ0aWFsKSwgKCJheGlvbSIsIHRvSnNvbiBpbmZvLmlzQXhpb20pLCAoImF4aW9tcyIsIHRvSnNvbiAoYXhpb21zLm1hcCBOYW1lLnRvU3RyaW5nKSksICgiZm9yYmlkZGVuX2F4aW9tcyIsIHRvSnNvbiAoZm9yYmlkZGVuLm1hcCBOYW1lLnRvU3RyaW5nKSldKS5jb21wcmVzc30iCiAgICB0b3RhbENoZWNrZWQgOj0gdG90YWxDaGVja2VkICsgY2hlY2tlZE5hbWVzLnNpemUKICAgIHRvdGFsQ2FuZGlkYXRlcyA6PSB0b3RhbENhbmRpZGF0ZXMgKyBjYW5kaWRhdGVzLnNpemUKICAgIHRvdGFsTWlzc2luZyA6PSB0b3RhbE1pc3NpbmcgKyBtaXNzaW5nTmFtZXMuc2l6ZQogICAgdG90YWxCYWQgOj0gdG90YWxCYWQgKyBiYWQKICAgIHRvdGFsSXNzdWVzIDo9IHRvdGFsSXNzdWVzICsgaXNzdWVzCiAgICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMjRfRkxBR1NfTU9EVUxFIHsoSnNvbi5ta09iaiBbKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksICgibW9kdWxlX2luZGV4IiwgdG9Kc29uIGlkeC50b05hdCksICgiaW52ZW50b3J5X29rIiwgdG9Kc29uIGludmVudG9yeU9LKSwgKCJjYW5kaWRhdGVfY291bnQiLCB0b0pzb24gY2FuZGlkYXRlcy5zaXplKSwgKCJjaGVja2VkIiwgdG9Kc29uIGNoZWNrZWROYW1lcy5zaXplKSwgKCJjaGVja2VkX25hbWVzIiwgdG9Kc29uIChjaGVja2VkTmFtZXMubWFwIE5hbWUudG9TdHJpbmcpKSwgKCJtaXNzaW5nIiwgdG9Kc29uIG1pc3NpbmdOYW1lcy5zaXplKSwgKCJtaXNzaW5nX25hbWVzIiwgdG9Kc29uIChtaXNzaW5nTmFtZXMubWFwIE5hbWUudG9TdHJpbmcpKSwgKCJkZWNsYXJhdGlvbl9pc3N1ZXMiLCB0b0pzb24gaXNzdWVzKSwgKCJiYWRfZGVjbGFyYXRpb25zIiwgdG9Kc29uIGJhZCksICgidW5zYWZlX2NvdW50IiwgdG9Kc29uIHVuc2FmZUNvdW50KSwgKCJwYXJ0aWFsX2NvdW50IiwgdG9Kc29uIHBhcnRpYWxDb3VudCksICgiYXhpb21fY291bnQiLCB0b0pzb24gYXhpb21Db3VudCksICgiZm9yYmlkZGVuX2F4aW9tX2RlY2xhcmF0aW9ucyIsIHRvSnNvbiBmb3JiaWRkZW5Db3VudCldKS5jb21wcmVzc30iCiAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X0ZMQUdTX0NPTVBMRVRFIHsoSnNvbi5ta09iaiBbKCJtb2R1bGVzIiwgdG9Kc29uIGV4cGVjdGVkTW9kdWxlcy5zaXplKSwgKCJjYW5kaWRhdGVfb2NjdXJyZW5jZXMiLCB0b0pzb24gdG90YWxDYW5kaWRhdGVzKSwgKCJjaGVja2VkX29jY3VycmVuY2VzIiwgdG9Kc29uIHRvdGFsQ2hlY2tlZCksICgibWlzc2luZ19vY2N1cnJlbmNlcyIsIHRvSnNvbiB0b3RhbE1pc3NpbmcpLCAoImJhZF9vY2N1cnJlbmNlcyIsIHRvSnNvbiB0b3RhbEJhZCksICgiZGVjbGFyYXRpb25faXNzdWVfb2NjdXJyZW5jZXMiLCB0b0pzb24gdG90YWxJc3N1ZXMpLCAoImludmVudG9yeV9taXNtYXRjaF9tb2R1bGVzIiwgdG9Kc29uIHRvdGFsTWlzbWF0Y2gpLCAoImFsbF9pbnZlbnRvcnlfb2siLCB0b0pzb24gKHRvdGFsTWlzbWF0Y2ggPT0gMCkpLCAoImFsbF9mbGFnc19heGlvbXNfY2xlYXIiLCB0b0pzb24gKHRvdGFsQmFkID09IDApKSwgKCJhbGxfY2FuZGlkYXRlc19leGFtaW5lZCIsIHRvSnNvbiAodG90YWxNaXNzaW5nID09IDApKSwgKCJkaWFnbm9zdGljX29ubHkiLCB0b0pzb24gdHJ1ZSksICgiZnVsbF90eXBlX2F1ZGl0IiwgdG9Kc29uIGZhbHNlKSwgKCJpbmRlcGVuZGVudF9yZXBsYXkiLCB0b0pzb24gZmFsc2UpLCAoIm9yaWdpbmFsX293bmVkX2FjY2VwdGVkIiwgdG9Kc29uIGZhbHNlKSwgKCJhY2NlcHRhbmNlX2NyZWRpdCIsIHRvSnNvbiBmYWxzZSldKS5jb21wcmVzc30iCiAgaWYgdG90YWxCYWQgPiAwIHx8IHRvdGFsTWlzbWF0Y2ggPiAwIHx8IHRvdGFsTWlzc2luZyA+IDAgfHwgdG90YWxJc3N1ZXMgPiAwIHRoZW4KICAgIHRocm93RXJyb3IgIkF1eGlsaWFyeSByaXNrIHNjYW4gY29tcGxldGU6IHt0b3RhbEJhZH0gYmFkIGRlY2xhcmF0aW9uIG9jY3VycmVuY2VzLCB7dG90YWxNaXNtYXRjaH0gaW52ZW50b3J5IG1pc21hdGNoZXMsIHt0b3RhbE1pc3Npbmd9IG1pc3NpbmcgQ29uc3RhbnRJbmZvIG9jY3VycmVuY2VzOyBubyBvcmlnaW5hbCBhdWRpdCBhY2NlcHRhbmNlIgo='
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

def parse_flags(path, modules):
    records = {kind: [] for kind in ("IMPORTS", "INVENTORY", "DECL_ISSUE", "BAD", "MODULE", "COMPLETE")}
    starts = []
    with path.open(encoding="utf-8") as stream:
        for line in stream:
            if line.startswith("P24_FLAGS_START "):
                starts.append(line.removeprefix("P24_FLAGS_START ").strip())
            for kind in records:
                prefix = "P24_FLAGS_" + kind + " "
                if line.startswith(prefix):
                    records[kind].append(json.loads(line[len(prefix):]))
                    break
    for kind, filename in (("INVENTORY", "inventories.json"), ("DECL_ISSUE", "declaration-issues.json"),
                           ("BAD", "bad-records.json"), ("MODULE", "module-counts.json")):
        write_json(OUT / filename, records[kind])
    mismatches = [row for row in records["INVENTORY"] if row.get("inventory_ok") is False]
    write_json(OUT / "inventory-mismatches.json", mismatches)
    write_json(OUT / "protocol.json", {"imports": records["IMPORTS"], "starts": starts, "complete": records["COMPLETE"]})
    require(len(records["IMPORTS"]) == 1 and isinstance(records["IMPORTS"][0], list), "Missing import list")
    imported = records["IMPORTS"][0]
    actual = [name for name in imported if name.startswith("ImbalancedChen.")]
    require(len(actual) == len(set(actual)) and set(actual) == set(modules), "Wrong project scope")
    require(starts == modules, "Incomplete module-start coverage")
    require([row["module"] for row in records["INVENTORY"]] == modules, "Incomplete inventories")
    require([row["module"] for row in records["MODULE"]] == modules, "Incomplete module scans")
    require(len(records["COMPLETE"]) == 1, "Missing complete marker")
    inv = {row["module"]: row for row in records["INVENTORY"]}
    issues = {name: [] for name in modules}
    bads = {name: [] for name in modules}
    for kind, table in (("DECL_ISSUE", issues), ("BAD", bads)):
        for row in records[kind]:
            require(row["module"] in inv, "Record outside scope")
            table[row["module"]].append(row)
    totals = Counter()
    all_checked = set()
    all_bad = set()
    for row in records["MODULE"]:
        name = row["module"]
        i = inv[name]
        ser, env = i["serialized"], i["environment"]
        union = set(ser) | set(env)
        idx = i["module_index"]
        require(type(idx) is int and 0 <= idx < len(imported) and imported[idx] == name, "Wrong module index")
        require(row["module_index"] == idx, "Module index changed")
        entries = i["header_entries"]
        data_ok = all(not e["data_is_module"] and e["import_all"] and e["has_data"] for e in entries)
        expected_ok = len(entries) == 1 and data_ok and bool(env) and sorted(env) == sorted(ser)
        require(i["legacy_data_ok"] is data_ok and i["inventory_ok"] is expected_ok
                and row["inventory_ok"] is expected_ok, "Inventory result misreported")
        require(sorted(i["serialized_only"]) == sorted(n for n in ser if n not in set(env))
                and sorted(i["environment_only"]) == sorted(n for n in env if n not in set(ser)), "Wrong inventory difference")
        checked, missing = row["checked_names"], row["missing_names"]
        require(len(checked) == len(set(checked)) and len(missing) == len(set(missing))
                and not set(checked).intersection(missing) and set(checked) | set(missing) == union,
                "Union candidates not fully classified")
        require(row["candidate_count"] == len(union) and row["checked"] == len(checked)
                and row["missing"] == len(missing), "Wrong scan counts")
        by_issue = {r["name"]: r for r in issues[name]}
        require(len(by_issue) == len(issues[name]) == row["declaration_issues"], "Duplicate/wrong issue count")
        for decl, r in by_issue.items():
            require(decl in union, "Issue outside candidate union")
            require(r["in_serialized"] is (decl in ser) and r["in_environment"] is (decl in env), "Wrong membership")
            owner = r["owner_index"]
            require(r["owner_module"] == (imported[owner] if owner is not None and 0 <= owner < len(imported) else None),
                    "Wrong actual owner module")
            require(r["owner_matches"] is (owner == idx), "Wrong owner-match flag")
            require(r["missing_constant_info"] is (decl in missing), "Wrong missing ConstantInfo flag")
            require(not r["in_serialized"] or not r["in_environment"] or not r["owner_matches"]
                    or r["missing_constant_info"], "Spurious declaration issue")
        require((set(i["serialized_only"]) | set(i["environment_only"]) | set(missing)) <= set(by_issue),
                "Unreported inventory difference or missing declaration")
        bad = bads[name]
        require(len({r["name"] for r in bad}) == len(bad) == row["bad_declarations"], "Duplicate/wrong bad count")
        for r in bad:
            require(r["name"] in checked, "Bad record was not examined")
            require(all(type(r[k]) is bool for k in ("unsafe", "partial", "axiom")), "Malformed flags")
            require(r["forbidden_axioms"] == [ax for ax in r["axioms"] if ax not in AXIOMS], "Wrong axiom classification")
            require(any(r[k] for k in ("unsafe", "partial", "axiom")) or r["forbidden_axioms"], "Spurious bad record")
            owner = r["owner_index"]
            require(r["owner_module"] == (imported[owner] if owner is not None and 0 <= owner < len(imported) else None)
                    and r["owner_matches"] is (owner == idx), "Bad record owner mismatch")
            require(r["in_serialized"] is (r["name"] in ser) and r["in_environment"] is (r["name"] in env), "Bad membership mismatch")
            all_bad.add(r["name"])
        expected_counts = {"unsafe_count": sum(r["unsafe"] for r in bad),
                           "partial_count": sum(r["partial"] for r in bad),
                           "axiom_count": sum(r["axiom"] for r in bad),
                           "forbidden_axiom_declarations": sum(bool(r["forbidden_axioms"]) for r in bad)}
        require(all(row[k] == v for k, v in expected_counts.items()), "Flag totals disagree")
        totals.update({"candidate_occurrences": len(union), "checked_occurrences": len(checked),
                       "missing_occurrences": len(missing), "bad_occurrences": len(bad),
                       "declaration_issue_occurrences": len(by_issue), "inventory_mismatch_modules": int(not expected_ok)})
        all_checked.update(checked)
    final = records["COMPLETE"][0]
    require(final["modules"] == 321 and all(final[k] == v for k, v in totals.items()), "Final coverage/count mismatch")
    require(final["all_inventory_ok"] is (totals["inventory_mismatch_modules"] == 0)
            and final["all_flags_axioms_clear"] is (totals["bad_occurrences"] == 0)
            and final["all_candidates_examined"] is (totals["missing_occurrences"] == 0), "Wrong final risk status")
    require(final["diagnostic_only"] is True and all(final[k] is False for k in
            ("full_type_audit", "independent_replay", "original_owned_accepted", "acceptance_credit")), "Acceptance boundary changed")
    return {**final, "unique_declarations_checked": len(all_checked), "unique_bad_declarations": sorted(all_bad),
            "mismatch_modules": [row["module"] for row in mismatches],
            "bad_modules": [name for name in modules if bads[name]],
            "all_requested_module_reports_complete": True}

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
from inspect_winner9_owner_native import imports as parsed_source_imports

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
# Separate source-only risk list: aggregate imports can supply APIs absent when a
# leaf is imported alone by the unchanged original per-module audit template.
std_init_leaves = []
no_explicit_import_leaves = []
for name, node in nodes.items():
    all_imports = parsed_source_imports(node['source'].read_text())
    if node['deps']:
        continue
    item = {'module': name, 'source': str(node['source'].relative_to(root)), 'imports': all_imports}
    if not all_imports:
        no_explicit_import_leaves.append(item)
    elif all(x in ('Std', 'Init') or x.startswith(('Std.', 'Init.')) for x in all_imports):
        std_init_leaves.append(item)
leaf_report = {'source_only': True, 'api_availability_tested': False, 'audit_credit': False,
               'std_init_only_project_leaf_modules': std_init_leaves,
               'no_explicit_import_project_leaf_modules': no_explicit_import_leaves}
# Source graph only: unchanged original project_nodes defines A/B closure membership.
a_nodes = set(project_nodes(root, 'ImbalancedChen.P2OriginalCompactArchivedTotalCandidate'))
b_nodes = set(project_nodes(root, 'ImbalancedChen.P2OriginalCompactCachedEndpointCandidate'))
require(len(a_nodes) == 102 and len(b_nodes) == 103, 'Original finite closure sizes changed')
closure_by_name = {}
for name, node in full_nodes.items():
    closure_by_name[name] = {name}.union(*(closure_by_name[d] for d in node['deps']))
dependency_rows = []
for target in ['ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore',
               'ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector']:
    require(target in symbolic, 'Requested dependency target is outside symbolic321')
    affected = [name for name in modules if target in closure_by_name[name]]
    dependency_rows.append({'module': target, 'in_A102_closure': target in a_nodes,
                            'in_B103_closure': target in b_nodes,
                            'symbolic_reverse_closure_including_self_count': len(affected),
                            'symbolic_strict_dependents_count': len(affected) - 1,
                            'symbolic_reverse_closure_including_self': affected})
leaf_report['source_dependency_report'] = {'source_only': True, 'compile_reuse_decided': False,
                                         'A_closure_size': 102, 'B_closure_size': 103,
                                         'modules': dependency_rows}
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
write_json(out / 'leaf-imports.json', leaf_report)
write_json(out / 'inputs-before.json', {'snapshot': before, 'registry_sha256': registry_before,
                                      'native': native_before})
flags = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000']
command = [LEAN, *flags, str(out / 'OwnedFlags.lean')]
log = out / 'owned-flags.log'
receipt = {'source_pin': pin, 'original_template_sha256': '5c2f7d5d006a2b2b33ef20be52216489a5262750b011d819b85badacf10bb1a3',
           'candidate_template_sha256': template_sha, 'diagnostic_scope_change': 'report all inventory differences and actual owners; scan serialized/environment union without original acceptance',
           'source_only_leaf_imports': leaf_report,
           'rendered_source_sha256': hashlib.sha256(source).hexdigest(),
           'registry_sha256_before': registry_before, 'symbolic_scope': 321,
           'ordered324_sha256': scope_sha, 'command': command,
           'original_verify_compilation_readonly_passed': True,
           'zero_budget_driver_repeated': False, 'native_qualification_repeated': False,
           'production_module_compilation_started': False, **credits}
print(json.dumps({'phase': 'auxiliary_risk_full321_scan_start', 'directory': str(out),
                  **receipt}), flush=True)
started = time.monotonic()
try:
    with log.open('xb') as stream:
        child = subprocess.run(command, cwd=root, env=external.environment(dict(os.environ)),
                               stdout=stream, stderr=subprocess.STDOUT)
    receipt['child_exit_code'] = child.returncode
    receipt['child_seconds'] = time.monotonic() - started
    parsed = parse_flags(log, modules)
    receipt['flags_scan_result'] = parsed
    require(child.returncode == int(not (parsed['all_flags_axioms_clear'] and parsed['all_inventory_ok'] and parsed['all_candidates_examined'] and parsed['declaration_issue_occurrences'] == 0)),
            'Lean exit disagrees with complete auxiliary risk findings')
    receipt['scan_completed'] = True
    receipt['all_flags_axioms_clear'] = parsed['all_flags_axioms_clear']
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
    bad_path = out / 'bad-records.json'
    if bad_path.is_file():
        raw_bad = bad_path.read_bytes()
        compressed_bad = gzip.compress(raw_bad, mtime=0)
        receipt['bad_records'] = {'path': str(bad_path), 'bytes': len(raw_bad),
                                  'sha256': hashlib.sha256(raw_bad).hexdigest(),
                                  'gzip_bytes': len(compressed_bad),
                                  'gzip_sha256': hashlib.sha256(compressed_bad).hexdigest(),
                                  'inline_complete': len(compressed_bad) < 256 * 1024}
        if receipt['bad_records']['inline_complete']:
            receipt['bad_records']['gzip_base64'] = base64.b64encode(compressed_bad).decode('ascii')
        else:
            receipt['bad_records']['retrieval'] = 'Complete persistent raw file retained; exact chunks required; no records truncated.'
    for filename, field in [('inventory-mismatches.json', 'inventory_mismatches'),
                            ('declaration-issues.json', 'declaration_issues')]:
        artifact = out / filename
        if artifact.is_file():
            raw_report = artifact.read_bytes()
            zipped_report = gzip.compress(raw_report, mtime=0)
            receipt[field] = {'path': str(artifact), 'bytes': len(raw_report),
                              'sha256': hashlib.sha256(raw_report).hexdigest(),
                              'gzip_bytes': len(zipped_report),
                              'gzip_sha256': hashlib.sha256(zipped_report).hexdigest(),
                              'inline_complete': len(zipped_report) < 256 * 1024}
            if receipt[field]['inline_complete']:
                receipt[field]['gzip_base64'] = base64.b64encode(zipped_report).decode('ascii')
            else:
                receipt[field]['retrieval'] = 'Full persistent original retained; retrieve exact chunks; no records truncated.'
    if log.is_file():
        ordinary = [line for line in log.read_text().splitlines() if not line.startswith('P24_FLAGS_')]
        ordinary_raw = ('\n'.join(ordinary) + '\n').encode()
        receipt['nonprotocol_output_bytes'] = len(ordinary_raw)
        if len(ordinary_raw) <= 20 * 1024:
            receipt['complete_nonprotocol_output'] = ordinary
        else:
            receipt['nonprotocol_output_location'] = str(log)
    receipt['diagnostic_scan_completed'] = receipt.get('scan_completed') is True and not errors
    receipt['diagnostic_clear'] = receipt['diagnostic_scan_completed'] and all(receipt.get('flags_scan_result', {}).get(k) is True for k in ('all_flags_axioms_clear', 'all_inventory_ok', 'all_candidates_examined')) and receipt.get('flags_scan_result', {}).get('declaration_issue_occurrences') == 0
    write_json(out / 'diagnostic.json', receipt)
    print(json.dumps({'phase': 'auxiliary_risk_full321_scan_complete',
                      'receipt_path': str(out / 'diagnostic.json'),
                      'receipt_sha256': digest(out / 'diagnostic.json'), **receipt}), flush=True)
raise SystemExit(0 if receipt.get('diagnostic_scan_completed') else 1)
P24_FLAGS_RISK_SCAN_PY
