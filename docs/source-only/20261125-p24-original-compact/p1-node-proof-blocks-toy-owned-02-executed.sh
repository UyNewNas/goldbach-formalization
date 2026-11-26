set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 -B - <<'PY'
import base64, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path

# Root must change only these two inputs to a known successful compilation attempt.
# Attempt 001 is known to have failed; the preflight below deliberately refuses it.
SOURCE_ATTEMPT = "attempt-005"
EXPECTED_SOURCE_SHA256 = "78decf5bb633707f0de05a9b8c4043e2d6b540d1510dc9e654ba4be549d76ed6"

root = Path("/workspace")
family = "p24-node-proof-blocks-toy-20261126"
old = root / family / SOURCE_ATTEMPT
out = root / "p24-node-proof-blocks-toy-owned-20261126" / "attempt-002"
lean = Path("/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean")
leanchecker = lean.with_name("leanchecker")
expected_lean_hash = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
template_hash = "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b"
template = base64.b64decode("aW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyV2lubmVyOUZpbml0ZU1vbWVudEtlcm5lbAppbXBvcnQgTGVhbi5VdGlsLkNvbGxlY3RBeGlvbXMKc2V0X29wdGlvbiBwcC5hbGwgdHJ1ZQpzZXRfb3B0aW9uIHBwLnByb29mcyB0cnVlCnNldF9vcHRpb24gcHAuZGVlcFRlcm1zIHRydWUKc2V0X29wdGlvbiBwcC51bml2ZXJzZXMgdHJ1ZQpzZXRfb3B0aW9uIHBwLmV4cGxpY2l0IHRydWUKc2V0X29wdGlvbiBwcC5mdWxsTmFtZXMgdHJ1ZQpzZXRfb3B0aW9uIHBwLnByaXZhdGVOYW1lcyB0cnVlCnNldF9vcHRpb24gcHAubWF4U3RlcHMgMTAwMDAwMApvcGVuIExlYW4gRWxhYiBDb21tYW5kIGluCnJ1bl9jbWQgZG8KICBsZXQgZW52IOKGkCBnZXRFbnYKICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMF9RVUVVRV9JTVBPUlRTIHsodG9Kc29uIChlbnYuaGVhZGVyLm1vZHVsZU5hbWVzLm1hcCBOYW1lLnRvU3RyaW5nKSkuY29tcHJlc3N9IgogIGxldCBtb2R1bGVOYW1lIDo9IGBJbWJhbGFuY2VkQ2hlbi5QMldpbm5lcjlGaW5pdGVNb21lbnRLZXJuZWwKICBsZXQgc29tZSBpZHggOj0gZW52LmdldE1vZHVsZUlkeD8gbW9kdWxlTmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgdGFyZ2V0IG1vZHVsZSIKICBsZXQgbmFtZXMgOj0gZW52LmNvbnN0Mk1vZElkeC5mb2xkIChpbml0IDo9ICgjW10gOiBBcnJheSBOYW1lKSkgZnVuIG5zIG4gaSA9PgogICAgaWYgaSA9PSBpZHggJiYgKGVudi5maW5kPyBuKS5pc1NvbWUgdGhlbiBucy5wdXNoIG4gZWxzZSBucwogIGxldCBtdXQgc2VyaWFsaXplZCA6IEFycmF5IE5hbWUgOj0gI1tdCiAgbGV0IG11dCBmb3VuZCA6PSBmYWxzZQogIGZvciBpIGluIExpc3QucmFuZ2UgZW52LmhlYWRlci5tb2R1bGVzLnNpemUgZG8KICAgIGxldCBpbXBvcnRlZCA6PSBlbnYuaGVhZGVyLm1vZHVsZXNbaV0hCiAgICBpZiBpbXBvcnRlZC5tb2R1bGUgPT0gbW9kdWxlTmFtZSB0aGVuCiAgICAgIGlmIGZvdW5kIHRoZW4gdGhyb3dFcnJvciAiRHVwbGljYXRlIG1vZHVsZSIKICAgICAgZm91bmQgOj0gdHJ1ZQogICAgICBsZXQgZGF0YSA6PSBlbnYuaGVhZGVyLm1vZHVsZURhdGFbaV0hCiAgICAgIGlmIGRhdGEuaXNNb2R1bGUgfHwgIWltcG9ydGVkLmltcG9ydEFsbCB8fCAhaW1wb3J0ZWQuaGFzRGF0YSB0aGVuCiAgICAgICAgdGhyb3dFcnJvciAiSW5jb21wbGV0ZSBpbXBvcnRlZCBsZWdhY3kgZGF0YSIKICAgICAgc2VyaWFsaXplZCA6PSBkYXRhLmNvbnN0TmFtZXMKICB1bmxlc3MgZm91bmQgJiYgbmFtZXMuc2l6ZSA+IDAgJiYgbmFtZXMucXNvcnQgTmFtZS5sdCA9PSBzZXJpYWxpemVkLnFzb3J0IE5hbWUubHQgZG8KICAgIHRocm93RXJyb3IgIkNvbXBsZXRlIHNlcmlhbGl6ZWQvZW52aXJvbm1lbnQgaW52ZW50b3J5IG1pc21hdGNoIgogIGxpZnRJTyA8fCBJTy5wcmludGxuIHMhIlAwX1FVRVVFX0lOVkVOVE9SWSB7KEpzb24ubWtPYmogWygibW9kdWxlIiwgdG9Kc29uIG1vZHVsZU5hbWUudG9TdHJpbmcpLCAoInNlcmlhbGl6ZWQiLCB0b0pzb24gKHNlcmlhbGl6ZWQubWFwIE5hbWUudG9TdHJpbmcpKSwgKCJlbnZpcm9ubWVudCIsIHRvSnNvbiAobmFtZXMubWFwIE5hbWUudG9TdHJpbmcpKV0pLmNvbXByZXNzfSIKICBmb3IgbmFtZSBpbiBuYW1lcy5xc29ydCBOYW1lLmx0IGRvCiAgICBsZXQgc29tZSBpbmZvIDo9IGVudi5maW5kPyBuYW1lIHwgdGhyb3dFcnJvciAiTWlzc2luZyBpbnZlbnRvcmllZCBkZWNsYXJhdGlvbiIKICAgIGlmIGluZm8uaXNVbnNhZmUgfHwgaW5mby5pc1BhcnRpYWwgfHwgaW5mby5pc0F4aW9tIHRoZW4gdGhyb3dFcnJvciAiVW5zYWZlL3BhcnRpYWwvYXhpb20gdGFyZ2V0IgogICAgbGV0IGF4aW9tcyDihpAgY29sbGVjdEF4aW9tcyBuYW1lCiAgICBmb3IgYXggaW4gYXhpb21zIGRvCiAgICAgIHVubGVzcyAjW2Bwcm9wZXh0LCBgQ2xhc3NpY2FsLmNob2ljZSwgYFF1b3Quc291bmRdLmNvbnRhaW5zIGF4IGRvCiAgICAgICAgdGhyb3dFcnJvciAiRm9yYmlkZGVuIHRyYW5zaXRpdmUgYXhpb20ge2F4fSIKICAgIGxldCB0eXBlIOKGkCBsaWZ0VGVybUVsYWJNIGRvIHJldHVybiAo4oaQIE1ldGEucHBFeHByIGluZm8udHlwZSkucHJldHR5CiAgICBpZiB0eXBlLmNvbnRhaW5zICfii68nIHRoZW4gdGhyb3dFcnJvciAiVHJ1bmNhdGVkIHR5cGUiCiAgICBsZXQgcmVjb3JkIDo9IEpzb24ubWtPYmogWygibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksCiAgICAgICgidW5zYWZlIiwgdG9Kc29uIGluZm8uaXNVbnNhZmUpLCAoInBhcnRpYWwiLCB0b0pzb24gaW5mby5pc1BhcnRpYWwpLCAoImF4aW9tIiwgdG9Kc29uIGluZm8uaXNBeGlvbSksCiAgICAgICgidHlwZSIsIHRvSnNvbiB0eXBlKSwgKCJheGlvbXMiLCB0b0pzb24gKGF4aW9tcy5tYXAgTmFtZS50b1N0cmluZykpXQogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDBfUVVFVUVfREVDTCB7cmVjb3JkLmNvbXByZXNzfSIKCg==", validate=True)
inspector_template = base64.b64decode("aW1wb3J0IEBUT1lfTU9EVUxFQAppbXBvcnQgTGVhbgppbXBvcnQgTGVhbi5NZXRhLlN5bS5MaXRWYWx1ZXMKCm9wZW4gTGVhbiBFbGFiIENvbW1hbmQgaW4KcnVuX2NtZCBkbwogIGxldCBlbnYg4oaQIGdldEVudgogIGxldCBtb2R1bGVOYW1lIDo9IGBAVE9ZX01PRFVMRUAKICBsZXQgc29tZSBvd25lciA6PSBlbnYuZ2V0TW9kdWxlSWR4PyBtb2R1bGVOYW1lCiAgICB8IHRocm93RXJyb3IgIk1pc3NpbmcgdG95IG1vZHVsZSIKICBsZXQgbmFtZXMgOj0gZW52LmNvbnN0Mk1vZElkeC5mb2xkIChpbml0IDo9ICgjW10gOiBBcnJheSBOYW1lKSkgZnVuIG5zIG4gaSA9PgogICAgaWYgaSA9PSBvd25lciAmJiAoZW52LmZpbmQ/IG4pLmlzU29tZSB0aGVuIG5zLnB1c2ggbiBlbHNlIG5zCiAgbGV0IHNvdXJjZU5hbWVzIDo9IG5hbWVzLmZpbHRlciBmdW4gbiA9PgogICAgcHJpdmF0ZVRvVXNlck5hbWUgbiA9PSBgUDI0Tm9kZVByb29mQmxvY2tzVG95LnNvdXJjZVN0YXRlCiAgbGV0IG5vZGVOYW1lcyA6PSBuYW1lcy5maWx0ZXIgZnVuIG4gPT4KICAgIHByaXZhdGVUb1VzZXJOYW1lIG4gPT0gYFAyNE5vZGVQcm9vZkJsb2Nrc1RveS5Ob2RlCiAgbGV0IGN0b3JOYW1lcyA6PSBuYW1lcy5maWx0ZXIgZnVuIG4gPT4KICAgIHByaXZhdGVUb1VzZXJOYW1lIG4gPT0gYFAyNE5vZGVQcm9vZkJsb2Nrc1RveS5Ob2RlLm1rCiAgdW5sZXNzIHNvdXJjZU5hbWVzLnNpemUgPT0gMSAmJiBub2RlTmFtZXMuc2l6ZSA9PSAxICYmIGN0b3JOYW1lcy5zaXplID09IDEgZG8KICAgIHRocm93RXJyb3IgIkNhbm5vdCB1bmlxdWVseSByZXNvbHZlIHRoZSBvcmlnaW5hbCB0b3kgc291cmNlU3RhdGUvTm9kZSBjb25zdHJ1Y3RvcnMiCiAgbGV0IHNvdXJjZU5hbWUgOj0gc291cmNlTmFtZXNbMF0hCiAgbGV0IG5vZGVOYW1lIDo9IG5vZGVOYW1lc1swXSEKICBsZXQgY3Rvck5hbWUgOj0gY3Rvck5hbWVzWzBdIQogIGxldCBibG9ja3MgOj0gKG5hbWVzLmZpbHRlciBmdW4gbiA9PgogICAgbi5hbnlTIChmdW4gcGFydCA9PiAiX25vZGVQcm9vZkJsb2NrIi5pc1ByZWZpeE9mIHBhcnQpKS5xc29ydCBOYW1lLmx0CiAgbGV0IGFzTmF0PyA6IEV4cHIg4oaSIE9wdGlvbiBOYXQgOj0gZnVuIGUgPT4KICAgIG1hdGNoIGUuY29uc3VtZU1EYXRhIHdpdGgKICAgIHwgLmxpdCAoLm5hdFZhbCBuKSA9PiBzb21lIG4KICAgIHwgXyA9PiBub25lCiAgbGV0IG11dCBhbGxPSyA6PSBibG9ja3Muc2l6ZSA9PSAyCiAgbGV0IG11dCBhbGxJbmRpY2VzIDogQXJyYXkgTmF0IDo9ICNbXQogIGxldCBtdXQgdG90YWxUeXBlTm9kZXMgOj0gMAogIGZvciBuYW1lIGluIGJsb2NrcyBkbwogICAgbGV0IHNvbWUgaW5mbyA6PSBlbnYuZmluZD8gbmFtZQogICAgICB8IHRocm93RXJyb3IgIk1pc3NpbmcgZ2VuZXJhdGVkIGJsb2NrIgogICAgbGV0IGlzVGhlb3JlbSA6PSBtYXRjaCBpbmZvIHdpdGgKICAgICAgfCAudGhtSW5mbyBfID0+IHRydWUKICAgICAgfCBfID0+IGZhbHNlCiAgICBsZXQgdHlwZSA6PSBpbmZvLnR5cGUuY29uc3VtZU1EYXRhCiAgICBsZXQgbXV0IGZhY3RzIDogQXJyYXkgRXhwciA6PSAjW10KICAgIGlmIHR5cGUuaXNBcHBPZkFyaXR5IGBgQW5kIDIgdGhlbgogICAgICBsZXQgcGFpciA6PSB0eXBlLmdldEFwcEFyZ3MKICAgICAgbGV0IGxlZnQgOj0gcGFpclswXSEuY29uc3VtZU1EYXRhCiAgICAgIGxldCByaWdodCA6PSBwYWlyWzFdIS5jb25zdW1lTURhdGEKICAgICAgaWYgbGVmdC5pc0FwcE9mQXJpdHkgYGBBbmQgMiAmJiByaWdodC5pc0FwcE9mQXJpdHkgYGBBbmQgMiB0aGVuCiAgICAgICAgbGV0IGxocyA6PSBsZWZ0LmdldEFwcEFyZ3MKICAgICAgICBsZXQgcmhzIDo9IHJpZ2h0LmdldEFwcEFyZ3MKICAgICAgICBmYWN0cyA6PSAjW2xoc1swXSEsIGxoc1sxXSEsIHJoc1swXSEsIHJoc1sxXSFdCiAgICBsZXQgbXV0IGJsb2NrT0sgOj0gaXNQcml2YXRlTmFtZSBuYW1lICYmIGlzVGhlb3JlbSAmJgogICAgICAhaW5mby5pc1Vuc2FmZSAmJiAhaW5mby5pc1BhcnRpYWwgJiYgIWluZm8uaXNBeGlvbSAmJgogICAgICAhdHlwZS5oYXNGVmFyICYmICF0eXBlLmhhc01WYXIgJiYgZmFjdHMuc2l6ZSA9PSA0CiAgICBsZXQgbXV0IGluZGljZXMgOiBBcnJheSBOYXQgOj0gI1tdCiAgICBsZXQgbXV0IGZhY3RSZWNvcmRzIDogQXJyYXkgSnNvbiA6PSAjW10KICAgIGZvciBvcmlnaW5hbEZhY3QgaW4gZmFjdHMgZG8KICAgICAgbGV0IGZhY3QgOj0gb3JpZ2luYWxGYWN0LmNvbnN1bWVNRGF0YQogICAgICBsZXQgbXV0IGZhY3RPSyA6PSBmYWxzZQogICAgICBsZXQgbXV0IGluZGV4IDogT3B0aW9uIE5hdCA6PSBub25lCiAgICAgIGxldCBtdXQgZ3JpZCA6IE9wdGlvbiBOYXQgOj0gbm9uZQogICAgICBsZXQgbXV0IGNvbXBsZXRlZCA6IE9wdGlvbiBOYXQgOj0gbm9uZQogICAgICBsZXQgbXV0IHZhbHVlcyA6IEFycmF5IChPcHRpb24gSW50KSA6PSAjW10KICAgICAgaWYgZmFjdC5pc0FwcE9mQXJpdHkgYGBFcSAzIHRoZW4KICAgICAgICBsZXQgZXF1YWxpdHkgOj0gZmFjdC5nZXRBcHBBcmdzCiAgICAgICAgbGV0IGxocyA6PSBlcXVhbGl0eVsxXSEuY29uc3VtZU1EYXRhCiAgICAgICAgbGV0IHJocyA6PSBlcXVhbGl0eVsyXSEuY29uc3VtZU1EYXRhCiAgICAgICAgaWYgZXF1YWxpdHlbMF0hLmlzQ29uc3RPZiBub2RlTmFtZSAmJgogICAgICAgICAgICBsaHMuaXNBcHBPZkFyaXR5IHNvdXJjZU5hbWUgMyAmJiByaHMuaXNBcHBPZkFyaXR5IGN0b3JOYW1lIDQgdGhlbgogICAgICAgICAgbGV0IHNvdXJjZUFyZ3MgOj0gbGhzLmdldEFwcEFyZ3MKICAgICAgICAgIGdyaWQgOj0gYXNOYXQ/IHNvdXJjZUFyZ3NbMF0hCiAgICAgICAgICBjb21wbGV0ZWQgOj0gYXNOYXQ/IHNvdXJjZUFyZ3NbMV0hCiAgICAgICAgICBpbmRleCA6PSBhc05hdD8gc291cmNlQXJnc1syXSEKICAgICAgICAgIHZhbHVlcyA6PSByaHMuZ2V0QXBwQXJncy5tYXAgTGVhbi5NZXRhLlN5bS5nZXRJbnRWYWx1ZT8KICAgICAgICAgIGZhY3RPSyA6PSBncmlkID09IHNvbWUgMiAmJiBpbmRleC5pc1NvbWUgJiYKICAgICAgICAgICAgY29tcGxldGVkID09IGluZGV4ICYmIHZhbHVlcy5hbGwgT3B0aW9uLmlzU29tZQogICAgICBpZiBsZXQgc29tZSBpIDo9IGluZGV4IHRoZW4gaW5kaWNlcyA6PSBpbmRpY2VzLnB1c2ggaQogICAgICBibG9ja09LIDo9IGJsb2NrT0sgJiYgZmFjdE9LCiAgICAgIGZhY3RSZWNvcmRzIDo9IGZhY3RSZWNvcmRzLnB1c2ggPHwgSnNvbi5ta09iaiBbCiAgICAgICAgKCJncmlkIiwgdG9Kc29uIGdyaWQpLCAoImNvbXBsZXRlZCIsIHRvSnNvbiBjb21wbGV0ZWQpLAogICAgICAgICgiaW5kZXgiLCB0b0pzb24gaW5kZXgpLCAoImZvdXJfaW50X25vcm1hbF9mb3JtIiwgdG9Kc29uIHZhbHVlcyksCiAgICAgICAgKCJleGFjdF9zb3VyY2Vfbm9kZV9lcXVhbGl0eSIsIHRvSnNvbiBmYWN0T0spXQogICAgYmxvY2tPSyA6PSBibG9ja09LICYmCiAgICAgIChpbmRpY2VzID09ICNbNSwgNiwgNywgOF0gfHwgaW5kaWNlcyA9PSAjWzksIDEwLCAxMSwgMTJdKQogICAgYWxsT0sgOj0gYWxsT0sgJiYgYmxvY2tPSwogICAgYWxsSW5kaWNlcyA6PSBhbGxJbmRpY2VzICsrIGluZGljZXMKICAgIGxldCBub2RlcyA6PSBpbmZvLnR5cGUuc2l6ZVdpdGhvdXRTaGFyaW5nCiAgICB0b3RhbFR5cGVOb2RlcyA6PSB0b3RhbFR5cGVOb2RlcyArIG5vZGVzCiAgICBsZXQgcmVjb3JkIDo9IEpzb24ubWtPYmogWwogICAgICAoIm5hbWUiLCB0b0pzb24gbmFtZS50b1N0cmluZyksICgicHJpdmF0ZSIsIHRvSnNvbiAoaXNQcml2YXRlTmFtZSBuYW1lKSksCiAgICAgICgidGhlb3JlbSIsIHRvSnNvbiBpc1RoZW9yZW0pLCAoInVuc2FmZSIsIHRvSnNvbiBpbmZvLmlzVW5zYWZlKSwKICAgICAgKCJwYXJ0aWFsIiwgdG9Kc29uIGluZm8uaXNQYXJ0aWFsKSwgKCJheGlvbSIsIHRvSnNvbiBpbmZvLmlzQXhpb20pLAogICAgICAoImZvdXJfZmFjdF9iYWxhbmNlZF9hbmQiLCB0b0pzb24gKGZhY3RzLnNpemUgPT0gNCkpLAogICAgICAoImluZGljZXMiLCB0b0pzb24gaW5kaWNlcyksICgiZmFjdHMiLCB0b0pzb24gZmFjdFJlY29yZHMpLAogICAgICAoInR5cGVfZXhwcl9ub2Rlc193aXRob3V0X3NoYXJpbmciLCB0b0pzb24gbm9kZXMpLAogICAgICAoInNoYXBlX2NoZWNrc19wYXNzZWQiLCB0b0pzb24gYmxvY2tPSyldCiAgICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMjRfVE9ZX0JMT0NLIHtyZWNvcmQuY29tcHJlc3N9IgogIGFsbE9LIDo9IGFsbE9LICYmCiAgICBhbGxJbmRpY2VzLnFzb3J0ICjCtyA8IMK3KSA9PSAjWzUsIDYsIDcsIDgsIDksIDEwLCAxMSwgMTJdCiAgbGV0IHN1bW1hcnkgOj0gSnNvbi5ta09iaiBbCiAgICAoIm1vZHVsZSIsIHRvSnNvbiBtb2R1bGVOYW1lLnRvU3RyaW5nKSwgKCJkaWFnbm9zdGljX29ubHkiLCB0b0pzb24gdHJ1ZSksCiAgICAoIm93bmVkX2Jsb2NrX2NvdW50IiwgdG9Kc29uIGJsb2Nrcy5zaXplKSwKICAgICgidG90YWxfdHlwZV9leHByX25vZGVzX3dpdGhvdXRfc2hhcmluZyIsIHRvSnNvbiB0b3RhbFR5cGVOb2RlcyksCiAgICAoImluZGljZXMiLCB0b0pzb24gYWxsSW5kaWNlcyksICgic2hhcGVfY2hlY2tzX3Bhc3NlZCIsIHRvSnNvbiBhbGxPSyksCiAgICAoIlAyX2FjY2VwdGFuY2VfY3JlZGl0IiwgdG9Kc29uIGZhbHNlKV0KICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMjRfVE9ZX0JMT0NLX1NVTU1BUlkge3N1bW1hcnkuY29tcHJlc3N9IgogIHVubGVzcyBhbGxPSyBkbwogICAgdGhyb3dFcnJvciAiVG95IGJsb2NrIHNoYXBlIGRpYWdub3N0aWNzIGZhaWxlZCIK", validate=True)

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def snapshot():
    return {
        "source_attempt_files": {str(p.relative_to(old)): digest(p)
                                 for p in sorted(old.rglob("*")) if p.is_file()},
        "lean_sha256": digest(lean),
        "leanchecker_sha256": digest(leanchecker),
    }

require(re.fullmatch(r"attempt-[0-9]{3}", SOURCE_ATTEMPT) is not None, "Bad attempt parameter")
require(re.fullmatch(r"[0-9a-f]{64}", EXPECTED_SOURCE_SHA256) is not None, "Bad source SHA parameter")
require(old.is_dir(), "Source attempt directory does not exist")
receipt_path = old / "diagnostic.json"
compile_receipt = json.loads(receipt_path.read_text())
require(compile_receipt.get("exit_code") == 0, "Refusing to audit a failed or incomplete toy compilation")
require(compile_receipt.get("diagnostic_only") is True, "Missing isolated compilation provenance")
require(compile_receipt.get("source_sha256") == EXPECTED_SOURCE_SHA256,
        "Successful compilation receipt belongs to another source")
require(digest(old / "Toy.lean") == EXPECTED_SOURCE_SHA256, "Toy source differs from successful receipt")
require(digest(old / "compile.log") == compile_receipt.get("log_sha256"),
        "Compilation log differs from successful receipt")
require((old / "Toy.olean").is_file() and (old / "Toy.olean").stat().st_size > 0,
        "Successful toy object is missing")
require(digest(lean) == expected_lean_hash, "Lean executable differs from the pinned P1 compiler")
require(leanchecker.is_file(), "Pinned adjacent leanchecker is missing")
version = subprocess.check_output([str(lean), "--version"], text=True).strip()
require("62eed1db4d67327ec8120be05f1a1b0847d74561" in version, "Wrong Lean version")
require(hashlib.sha256(template).hexdigest() == template_hash, "Original audit template digest changed")
require(template.count(b"ImbalancedChen.P2Winner9FiniteMomentKernel") == 2,
        "Original audit template target count changed")
require(os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= 64 * 1024 * 1024,
        "Less than 64 MiB free space")

# String.toName parses escaped identifiers; unescaped hyphens are invalid.
target = f"«{family}».«{SOURCE_ATTEMPT}».Toy"
audit_bytes = template.replace(b"ImbalancedChen.P2Winner9FiniteMomentKernel", target.encode())
inspect_bytes = inspector_template.replace(b"@TOY_MODULE@", target.encode())
before = snapshot()
out.mkdir(parents=True, exist_ok=False)
(out / "Audit.lean").write_bytes(audit_bytes)
(out / "InspectBlocks.lean").write_bytes(inspect_bytes)
env = dict(os.environ)
env["LEAN_PATH"] = str(root)
env["LEAN_SYSROOT"] = str(lean.parent.parent)
env.pop("LEAN_SRC_PATH", None)
flags = ["-t0", "-j1", "-M6144", "-DwarningAsError=true",
         "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
result = {
    "diagnostic_only": True, "compile_credit": False, "kernel_credit": False,
    "acceptance_credit": False, "finite_A_credit": False, "full_owned_audit_credit": False,
    "scope": "independent replay and complete owned audit of one successful toy module only",
    "target_module": target, "source_attempt": str(old),
    "source_sha256": EXPECTED_SOURCE_SHA256,
    "successful_compile_receipt_sha256": digest(receipt_path),
    "successful_compile_receipt": compile_receipt,
    "template_sha256": template_hash,
    "audit_source_sha256": hashlib.sha256(audit_bytes).hexdigest(),
    "audit_template_changes": "exactly two replacements of the original target module",
    "inspector_source_sha256": hashlib.sha256(inspect_bytes).hexdigest(),
    "lean_version": version, "before": before,
    "canonical_P2_touched": False, "existing_P1_project_touched": False,
    "stages": {}, "original_replay_and_owned_rules_passed": False,
    "extra_block_shape_checks_passed": False,
}
print(json.dumps({k:v for k,v in result.items() if k != "successful_compile_receipt"},
                 ensure_ascii=False), flush=True)

def run_stage(stage, command, timeout=120):
    print("P24_TOY_AUDIT_STAGE_BEGIN " + stage, flush=True)
    log = out / (stage + ".log")
    started = time.monotonic()
    timed_out = False
    with log.open("wb") as stream:
        proc = subprocess.Popen(command, cwd=root, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
        try:
            rc = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            proc.kill()
            rc = proc.wait()
    elapsed = time.monotonic() - started
    raw = log.read_bytes()
    sys.stdout.buffer.write(raw)
    sys.stdout.buffer.flush()
    state = snapshot()
    row = {"command": command, "exit_code": rc, "timed_out": timed_out,
           "elapsed_seconds": elapsed, "log": str(log),
           "log_sha256": hashlib.sha256(raw).hexdigest(), "log_bytes": len(raw),
           "inputs_unchanged": state == before}
    result["stages"][stage] = row
    print(json.dumps({"stage":stage, **row}, ensure_ascii=False), flush=True)
    require(row["inputs_unchanged"], "Source attempt or tool binaries changed during " + stage)
    require(rc == 0 and not timed_out, stage + " failed; later stages were not run")
    return raw

def records_with_prefix(raw, prefix):
    return [json.loads(line[len(prefix):]) for line in raw.decode("utf-8").splitlines()
            if line.startswith(prefix)]

try:
    run_stage("replay", [str(leanchecker), "--verbose", target])
    audit_raw = run_stage("audit", [str(lean), *flags, str(out / "Audit.lean")])
    import_rows = records_with_prefix(audit_raw, "P0_QUEUE_IMPORTS ")
    inventory_rows = records_with_prefix(audit_raw, "P0_QUEUE_INVENTORY ")
    declarations = records_with_prefix(audit_raw, "P0_QUEUE_DECL ")
    require(len(import_rows) == 1 and isinstance(import_rows[0], list), "Missing/duplicate import inventory")
    require(not any(n.startswith("ImbalancedChen.") for n in import_rows[0]),
            "Toy unexpectedly imports a production project module")
    require(len(inventory_rows) == 1 and inventory_rows[0].get("module") == target,
            "Missing/duplicate/wrong target inventory")
    inventory = inventory_rows[0]
    serialized, environment = inventory["serialized"], inventory["environment"]
    require(serialized and len(serialized) == len(set(serialized)) and
            sorted(serialized) == sorted(environment), "Serialized/environment mismatch")
    names = [d["name"] for d in declarations]
    require(len(names) == len(set(names)) and sorted(names) == sorted(serialized),
            "Owned declaration rows do not exactly cover the complete inventory")
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    for row in declarations:
        require(row.get("module") == target, "Declaration belongs to another module")
        require(all(row.get(k) is False for k in ("unsafe", "partial", "axiom")),
                "Unsafe/partial/axiom owned declaration")
        require(isinstance(row.get("type"), str) and row["type"] and "⋯" not in row["type"],
                "Missing/truncated declaration type")
        require(isinstance(row.get("axioms"), list) and set(row["axioms"]) <= allowed_axioms,
                "Forbidden transitive axiom")
    (out / "declarations.json").write_text(json.dumps(
        {"inventory":inventory, "imports":import_rows[0], "declarations":declarations},
        ensure_ascii=False, indent=2) + "\n")
    (out / "types.txt").write_text("\n\n".join(
        row["name"] + "\n" + row["type"] for row in declarations) + "\n")
    result["original_replay_and_owned_rules_passed"] = True
    result["owned_declaration_count"] = len(declarations)
    result["all_owned_printed_type_utf8_bytes"] = sum(len(row["type"].encode()) for row in declarations)

    inspect_raw = run_stage("blocks", [str(lean), *flags, str(out / "InspectBlocks.lean")])
    blocks = records_with_prefix(inspect_raw, "P24_TOY_BLOCK ")
    summaries = records_with_prefix(inspect_raw, "P24_TOY_BLOCK_SUMMARY ")
    require(len(summaries) == 1 and summaries[0].get("module") == target, "Missing block summary")
    require(len(blocks) == 2 and summaries[0].get("owned_block_count") == 2 and
            summaries[0].get("shape_checks_passed") is True, "Incorrect block inventory/shape")
    by_name = {row["name"]:row for row in declarations}
    for block in blocks:
        require(block["name"] in by_name, "Inspected block is absent from original owned audit")
        block["printed_type_utf8_bytes"] = len(by_name[block["name"]]["type"].encode())
        block["axioms"] = by_name[block["name"]]["axioms"]
    result["extra_block_shape_checks_passed"] = True
    result["blocks"] = blocks
    result["block_summary"] = summaries[0]
    result["total_block_printed_type_utf8_bytes"] = sum(b["printed_type_utf8_bytes"] for b in blocks)
    (out / "blocks.json").write_text(json.dumps(
        {"blocks":blocks,"summary":summaries[0]}, ensure_ascii=False, indent=2) + "\n")
except (OSError, ValueError, KeyError, TypeError, AssertionError) as error:
    result["error"] = str(error)
finally:
    after = snapshot()
    result["after"] = after
    result["source_attempt_and_tools_unchanged"] = after == before
    result["diagnostic_passed"] = (result["original_replay_and_owned_rules_passed"] and
                                  result["extra_block_shape_checks_passed"] and after == before)
    (out / "diagnostic.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result, ensure_ascii=False), flush=True)
raise SystemExit(0 if result["diagnostic_passed"] else 1)
PY
