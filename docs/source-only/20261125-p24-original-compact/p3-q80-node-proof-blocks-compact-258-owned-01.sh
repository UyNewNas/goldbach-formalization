set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 -B - <<'PY'
import base64, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path

# Frozen successful Q80 diagnostic 56afa9b1d65d4947bf7fe4c99ebb6a69.
# Any future attempt must independently pass compilation and match its exact source hash.
SOURCE_ATTEMPT = "attempt-001"
EXPECTED_SOURCE_SHA256 = "2541a03476ca4a381402a0bc0f99558fa9701b7d15984621db16dfeaa67cc505"

root = Path("/workspace")
family = "p24-q80-node-proof-blocks-compact-258-20261126"
old = root / family / SOURCE_ATTEMPT
out = root / "p24-q80-node-proof-blocks-compact-258-owned-20261126" / "attempt-001"
lean = Path("/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean")
leanchecker = lean.with_name("leanchecker")
expected_lean_hash = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
template_hash = "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b"
template = base64.b64decode("aW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyV2lubmVyOUZpbml0ZU1vbWVudEtlcm5lbAppbXBvcnQgTGVhbi5VdGlsLkNvbGxlY3RBeGlvbXMKc2V0X29wdGlvbiBwcC5hbGwgdHJ1ZQpzZXRfb3B0aW9uIHBwLnByb29mcyB0cnVlCnNldF9vcHRpb24gcHAuZGVlcFRlcm1zIHRydWUKc2V0X29wdGlvbiBwcC51bml2ZXJzZXMgdHJ1ZQpzZXRfb3B0aW9uIHBwLmV4cGxpY2l0IHRydWUKc2V0X29wdGlvbiBwcC5mdWxsTmFtZXMgdHJ1ZQpzZXRfb3B0aW9uIHBwLnByaXZhdGVOYW1lcyB0cnVlCnNldF9vcHRpb24gcHAubWF4U3RlcHMgMTAwMDAwMApvcGVuIExlYW4gRWxhYiBDb21tYW5kIGluCnJ1bl9jbWQgZG8KICBsZXQgZW52IOKGkCBnZXRFbnYKICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMF9RVUVVRV9JTVBPUlRTIHsodG9Kc29uIChlbnYuaGVhZGVyLm1vZHVsZU5hbWVzLm1hcCBOYW1lLnRvU3RyaW5nKSkuY29tcHJlc3N9IgogIGxldCBtb2R1bGVOYW1lIDo9IGBJbWJhbGFuY2VkQ2hlbi5QMldpbm5lcjlGaW5pdGVNb21lbnRLZXJuZWwKICBsZXQgc29tZSBpZHggOj0gZW52LmdldE1vZHVsZUlkeD8gbW9kdWxlTmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgdGFyZ2V0IG1vZHVsZSIKICBsZXQgbmFtZXMgOj0gZW52LmNvbnN0Mk1vZElkeC5mb2xkIChpbml0IDo9ICgjW10gOiBBcnJheSBOYW1lKSkgZnVuIG5zIG4gaSA9PgogICAgaWYgaSA9PSBpZHggJiYgKGVudi5maW5kPyBuKS5pc1NvbWUgdGhlbiBucy5wdXNoIG4gZWxzZSBucwogIGxldCBtdXQgc2VyaWFsaXplZCA6IEFycmF5IE5hbWUgOj0gI1tdCiAgbGV0IG11dCBmb3VuZCA6PSBmYWxzZQogIGZvciBpIGluIExpc3QucmFuZ2UgZW52LmhlYWRlci5tb2R1bGVzLnNpemUgZG8KICAgIGxldCBpbXBvcnRlZCA6PSBlbnYuaGVhZGVyLm1vZHVsZXNbaV0hCiAgICBpZiBpbXBvcnRlZC5tb2R1bGUgPT0gbW9kdWxlTmFtZSB0aGVuCiAgICAgIGlmIGZvdW5kIHRoZW4gdGhyb3dFcnJvciAiRHVwbGljYXRlIG1vZHVsZSIKICAgICAgZm91bmQgOj0gdHJ1ZQogICAgICBsZXQgZGF0YSA6PSBlbnYuaGVhZGVyLm1vZHVsZURhdGFbaV0hCiAgICAgIGlmIGRhdGEuaXNNb2R1bGUgfHwgIWltcG9ydGVkLmltcG9ydEFsbCB8fCAhaW1wb3J0ZWQuaGFzRGF0YSB0aGVuCiAgICAgICAgdGhyb3dFcnJvciAiSW5jb21wbGV0ZSBpbXBvcnRlZCBsZWdhY3kgZGF0YSIKICAgICAgc2VyaWFsaXplZCA6PSBkYXRhLmNvbnN0TmFtZXMKICB1bmxlc3MgZm91bmQgJiYgbmFtZXMuc2l6ZSA+IDAgJiYgbmFtZXMucXNvcnQgTmFtZS5sdCA9PSBzZXJpYWxpemVkLnFzb3J0IE5hbWUubHQgZG8KICAgIHRocm93RXJyb3IgIkNvbXBsZXRlIHNlcmlhbGl6ZWQvZW52aXJvbm1lbnQgaW52ZW50b3J5IG1pc21hdGNoIgogIGxpZnRJTyA8fCBJTy5wcmludGxuIHMhIlAwX1FVRVVFX0lOVkVOVE9SWSB7KEpzb24ubWtPYmogWygibW9kdWxlIiwgdG9Kc29uIG1vZHVsZU5hbWUudG9TdHJpbmcpLCAoInNlcmlhbGl6ZWQiLCB0b0pzb24gKHNlcmlhbGl6ZWQubWFwIE5hbWUudG9TdHJpbmcpKSwgKCJlbnZpcm9ubWVudCIsIHRvSnNvbiAobmFtZXMubWFwIE5hbWUudG9TdHJpbmcpKV0pLmNvbXByZXNzfSIKICBmb3IgbmFtZSBpbiBuYW1lcy5xc29ydCBOYW1lLmx0IGRvCiAgICBsZXQgc29tZSBpbmZvIDo9IGVudi5maW5kPyBuYW1lIHwgdGhyb3dFcnJvciAiTWlzc2luZyBpbnZlbnRvcmllZCBkZWNsYXJhdGlvbiIKICAgIGlmIGluZm8uaXNVbnNhZmUgfHwgaW5mby5pc1BhcnRpYWwgfHwgaW5mby5pc0F4aW9tIHRoZW4gdGhyb3dFcnJvciAiVW5zYWZlL3BhcnRpYWwvYXhpb20gdGFyZ2V0IgogICAgbGV0IGF4aW9tcyDihpAgY29sbGVjdEF4aW9tcyBuYW1lCiAgICBmb3IgYXggaW4gYXhpb21zIGRvCiAgICAgIHVubGVzcyAjW2Bwcm9wZXh0LCBgQ2xhc3NpY2FsLmNob2ljZSwgYFF1b3Quc291bmRdLmNvbnRhaW5zIGF4IGRvCiAgICAgICAgdGhyb3dFcnJvciAiRm9yYmlkZGVuIHRyYW5zaXRpdmUgYXhpb20ge2F4fSIKICAgIGxldCB0eXBlIOKGkCBsaWZ0VGVybUVsYWJNIGRvIHJldHVybiAo4oaQIE1ldGEucHBFeHByIGluZm8udHlwZSkucHJldHR5CiAgICBpZiB0eXBlLmNvbnRhaW5zICfii68nIHRoZW4gdGhyb3dFcnJvciAiVHJ1bmNhdGVkIHR5cGUiCiAgICBsZXQgcmVjb3JkIDo9IEpzb24ubWtPYmogWygibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksCiAgICAgICgidW5zYWZlIiwgdG9Kc29uIGluZm8uaXNVbnNhZmUpLCAoInBhcnRpYWwiLCB0b0pzb24gaW5mby5pc1BhcnRpYWwpLCAoImF4aW9tIiwgdG9Kc29uIGluZm8uaXNBeGlvbSksCiAgICAgICgidHlwZSIsIHRvSnNvbiB0eXBlKSwgKCJheGlvbXMiLCB0b0pzb24gKGF4aW9tcy5tYXAgTmFtZS50b1N0cmluZykpXQogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDBfUVVFVUVfREVDTCB7cmVjb3JkLmNvbXByZXNzfSIKCg==", validate=True)
inspector_template = base64.b64decode("aW1wb3J0IEBRODBfTU9EVUxFQAppbXBvcnQgTGVhbgppbXBvcnQgTGVhbi5NZXRhLlN5bS5MaXRWYWx1ZXMKCm9wZW4gTGVhbiBFbGFiIENvbW1hbmQgaW4KcnVuX2NtZCBkbwogIGxldCBlbnYg4oaQIGdldEVudgogIGxldCBtb2R1bGVOYW1lIDo9IGBAUTgwX01PRFVMRUAKICBsZXQgc29tZSBvd25lciA6PSBlbnYuZ2V0TW9kdWxlSWR4PyBtb2R1bGVOYW1lCiAgICB8IHRocm93RXJyb3IgIk1pc3NpbmcgUTgwIGRpYWdub3N0aWMgbW9kdWxlIgogIGxldCBuYW1lcyA6PSBlbnYuY29uc3QyTW9kSWR4LmZvbGQgKGluaXQgOj0gKCNbXSA6IEFycmF5IE5hbWUpKSBmdW4gbnMgbiBpID0+CiAgICBpZiBpID09IG93bmVyICYmIChlbnYuZmluZD8gbikuaXNTb21lIHRoZW4gbnMucHVzaCBuIGVsc2UgbnMKICBsZXQgcmVzb2x2ZSA6PSBmdW4gd2FudGVkID0+IG5hbWVzLmZpbHRlciBmdW4gbiA9PiBwcml2YXRlVG9Vc2VyTmFtZSBuID09IHdhbnRlZAogIGxldCBzb3VyY2VOYW1lcyA6PSByZXNvbHZlCiAgICBgUDI0UTgwTm9kZVByb29mQmxvY2tzLkltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxDb21wYWN0UTgwRW5jbG9zZXJTb3VyY2VPbmx5LnNvdXJjZVN0YXRlCiAgbGV0IGFsaWFzTmFtZXMgOj0gcmVzb2x2ZQogICAgYFAyNFE4ME5vZGVQcm9vZkJsb2Nrcy5JbWJhbGFuY2VkQ2hlbi5QMk9yaWdpbmFsQ29tcGFjdFE4MEVuY2xvc2VyU291cmNlT25seS5Ob2RlCiAgbGV0IG5vZGVOYW1lcyA6PSByZXNvbHZlCiAgICBgUDI0UTgwTm9kZVByb29mQmxvY2tzLkltYmFsYW5jZWRDaGVuLlAySGlzdG9yaWNTaWV2ZVRhYmxlU2VtYW50aWNzLkhpc3RvcmljTm9kZQogIGxldCBjdG9yTmFtZXMgOj0gcmVzb2x2ZQogICAgYFAyNFE4ME5vZGVQcm9vZkJsb2Nrcy5JbWJhbGFuY2VkQ2hlbi5QMkhpc3RvcmljU2lldmVUYWJsZVNlbWFudGljcy5IaXN0b3JpY05vZGUubWsKICBsZXQgZW50cnlOYW1lcyA6PSByZXNvbHZlIGBQMjRRODBOb2RlUHJvb2ZCbG9ja3MuTm9kZVN0ZXBQcm9vZi5wcmVmaXhfMjU4X3E4MF9ibG9ja3NfcG9zaXRpdmUKICB1bmxlc3Mgc291cmNlTmFtZXMuc2l6ZSA9PSAxICYmIGFsaWFzTmFtZXMuc2l6ZSA9PSAxICYmIG5vZGVOYW1lcy5zaXplID09IDEgJiYKICAgICAgY3Rvck5hbWVzLnNpemUgPT0gMSAmJiBlbnRyeU5hbWVzLnNpemUgPT0gMSBkbwogICAgdGhyb3dFcnJvciAiQ2Fubm90IHVuaXF1ZWx5IHJlc29sdmUgdGhlIGV4YWN0IFE4MCBzb3VyY2UvTm9kZS9jb25zdHJ1Y3Rvci9wdWJsaWMgZW50cnkiCiAgbGV0IHNvdXJjZU5hbWUgOj0gc291cmNlTmFtZXNbMF0hCiAgbGV0IGFsaWFzTmFtZSA6PSBhbGlhc05hbWVzWzBdIQogIGxldCBub2RlTmFtZSA6PSBub2RlTmFtZXNbMF0hCiAgbGV0IGN0b3JOYW1lIDo9IGN0b3JOYW1lc1swXSEKICBsZXQgZW50cnlOYW1lIDo9IGVudHJ5TmFtZXNbMF0hCiAgbGV0IHNvbWUgYWxpYXNJbmZvIDo9IGVudi5maW5kPyBhbGlhc05hbWUgfCB0aHJvd0Vycm9yICJNaXNzaW5nIE5vZGUgYWxpYXMiCiAgLS0gUmVhZCB0aGUgYWxpYXMgYm9keSBvbmx5LiBObyBkZWZlcSwgd2huZiwgb3IgZXZhbHVhdGlvbiBvZiBhIHNvdXJjZVN0YXRlIHRlcm0uCiAgbGV0IGFsaWFzSXNEaXJlY3QgOj0gbWF0Y2ggYWxpYXNJbmZvIHdpdGgKICAgIHwgLmRlZm5JbmZvIHZhbHVlID0+IHZhbHVlLnZhbHVlLmNvbnN1bWVNRGF0YS5pc0NvbnN0T2Ygbm9kZU5hbWUKICAgIHwgXyA9PiBmYWxzZQogIHVubGVzcyBhbGlhc0lzRGlyZWN0IGRvCiAgICB0aHJvd0Vycm9yICJOb2RlIGlzIG5vdCB0aGUgZXhwZWN0ZWQgZGlyZWN0IEhpc3RvcmljTm9kZSB0eXBlIGFsaWFzIgogIGxldCBzb21lIGVudHJ5SW5mbyA6PSBlbnYuZmluZD8gZW50cnlOYW1lIHwgdGhyb3dFcnJvciAiTWlzc2luZyBwdWJsaWMgZW50cnkiCiAgbGV0IGVudHJ5SXNUaGVvcmVtIDo9IG1hdGNoIGVudHJ5SW5mbyB3aXRoCiAgICB8IC50aG1JbmZvIF8gPT4gdHJ1ZQogICAgfCBfID0+IGZhbHNlCiAgbGV0IGVudHJ5T0sgOj0gIWlzUHJpdmF0ZU5hbWUgZW50cnlOYW1lICYmIGVudHJ5SXNUaGVvcmVtICYmCiAgICAhZW50cnlJbmZvLmlzVW5zYWZlICYmICFlbnRyeUluZm8uaXNQYXJ0aWFsICYmICFlbnRyeUluZm8uaXNBeGlvbQogIHVubGVzcyBlbnRyeU9LIGRvCiAgICB0aHJvd0Vycm9yICJUaGUgZGlhZ25vc3RpYyBlbnRyeSBpcyBub3QgYSBwdWJsaWMgc2FmZSBub25wYXJ0aWFsIHRoZW9yZW0iCiAgbGV0IGJsb2NrcyA6PSAobmFtZXMuZmlsdGVyIGZ1biBuID0+CiAgICBuLmFueVMgKGZ1biBwYXJ0ID0+ICJfcTgwTm9kZVByb29mQmxvY2siLmlzUHJlZml4T2YgcGFydCkpLnFzb3J0IE5hbWUubHQKCiAgLS0gT25seSBhIE5hdCBsaXRlcmFsIG9yIGl0cyBjYW5vbmljYWwgT2ZOYXQgTmF0IC8gaW5zdE9mTmF0TmF0IHdyYXBwZXIuCiAgbGV0IGFzTmF0PyA6IEV4cHIg4oaSIE9wdGlvbiBOYXQgOj0gZnVuIG9yaWdpbmFsID0+CiAgICBtYXRjaCBvcmlnaW5hbC5jb25zdW1lTURhdGEgd2l0aAogICAgfCAubGl0ICgubmF0VmFsIG4pID0+IHNvbWUgbgogICAgfCAuYXBwICguYXBwICguYXBwICguY29uc3Qgb2ZOYXROYW1lIF8pICguY29uc3QgbmF0TmFtZSBbXSkpCiAgICAgICAgKC5saXQgKC5uYXRWYWwgbikpKSAoLmFwcCAoLmNvbnN0IGluc3ROYW1lIFtdKSAoLmxpdCAoLm5hdFZhbCBtKSkpID0+CiAgICAgICAgaWYgb2ZOYXROYW1lID09IGBgT2ZOYXQub2ZOYXQgJiYgbmF0TmFtZSA9PSBgYE5hdCAmJgogICAgICAgICAgICBpbnN0TmFtZSA9PSBgYGluc3RPZk5hdE5hdCAmJiBuID09IG0gdGhlbiBzb21lIG4gZWxzZSBub25lCiAgICB8IF8gPT4gbm9uZQogIC0tIEtlZXAgdGhlIG9yaWdpbmFsIFN5bSBsaXRlcmFsIGZvcm1zLCBwbHVzIGV4YWN0IEludCBjb25zdHJ1Y3RvcnMgb24gdGhlCiAgLS0gcmVjb2duaXplZCBOYXQgc3ludGF4LiBuZWdTdWNjIG4gZGVub3RlcyAtKG4rMSksIG5vdCAtbi4KICBsZXQgYXNJbnQ/IDogRXhwciDihpIgT3B0aW9uIEludCA6PSBmdW4gb3JpZ2luYWwgPT4KICAgIGxldCBlIDo9IG9yaWdpbmFsLmNvbnN1bWVNRGF0YQogICAgbWF0Y2ggZSB3aXRoCiAgICB8IC5hcHAgKC5jb25zdCBjdG9yIFtdKSBuID0+CiAgICAgICAgaWYgY3RvciA9PSBgYEludC5vZk5hdCB0aGVuIChhc05hdD8gbikubWFwIEludC5vZk5hdAogICAgICAgIGVsc2UgaWYgY3RvciA9PSBgYEludC5uZWdTdWNjIHRoZW4gKGFzTmF0PyBuKS5tYXAgSW50Lm5lZ1N1Y2MKICAgICAgICBlbHNlIG5vbmUKICAgIHwgXyA9PiBMZWFuLk1ldGEuU3ltLmdldEludFZhbHVlPyBlCgogIGxldCBtdXQgYWxsT0sgOj0gYmxvY2tzLnNpemUgPT0gMjU4CiAgbGV0IG11dCBhbGxJbmRpY2VzIDogQXJyYXkgTmF0IDo9ICNbXQogIGxldCBtdXQgdG90YWxUeXBlTm9kZXMgOj0gMAogIGZvciBuYW1lIGluIGJsb2NrcyBkbwogICAgbGV0IHNvbWUgaW5mbyA6PSBlbnYuZmluZD8gbmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgZ2VuZXJhdGVkIFE4MCBibG9jayIKICAgIGxldCBpc1RoZW9yZW0gOj0gbWF0Y2ggaW5mbyB3aXRoCiAgICAgIHwgLnRobUluZm8gXyA9PiB0cnVlCiAgICAgIHwgXyA9PiBmYWxzZQogICAgbGV0IHR5cGUgOj0gaW5mby50eXBlLmNvbnN1bWVNRGF0YQogICAgbGV0IG11dCBmYWN0cyA6IEFycmF5IEV4cHIgOj0gI1t0eXBlXQogICAgbGV0IG11dCBiYWxhbmNlZCA6PSB0cnVlCiAgICBmb3IgXyBpbiBbOjZdIGRvCiAgICAgIGxldCBtdXQgbmV4dCA6IEFycmF5IEV4cHIgOj0gI1tdCiAgICAgIGZvciBvcmlnaW5hbCBpbiBmYWN0cyBkbwogICAgICAgIGxldCB0ZXJtIDo9IG9yaWdpbmFsLmNvbnN1bWVNRGF0YQogICAgICAgIGlmIHRlcm0uaXNBcHBPZkFyaXR5IGBgQW5kIDIgdGhlbgogICAgICAgICAgbGV0IGFyZ3MgOj0gdGVybS5nZXRBcHBBcmdzCiAgICAgICAgICBuZXh0IDo9IG5leHQucHVzaCBhcmdzWzBdIQogICAgICAgICAgbmV4dCA6PSBuZXh0LnB1c2ggYXJnc1sxXSEKICAgICAgICBlbHNlCiAgICAgICAgICBiYWxhbmNlZCA6PSBmYWxzZQogICAgICBmYWN0cyA6PSBuZXh0CiAgICBiYWxhbmNlZCA6PSBiYWxhbmNlZCAmJiBmYWN0cy5zaXplID09IDY0CiAgICBsZXQgbXV0IGJsb2NrT0sgOj0gaXNQcml2YXRlTmFtZSBuYW1lICYmIGlzVGhlb3JlbSAmJgogICAgICAhaW5mby5pc1Vuc2FmZSAmJiAhaW5mby5pc1BhcnRpYWwgJiYgIWluZm8uaXNBeGlvbSAmJgogICAgICAhdHlwZS5oYXNGVmFyICYmICF0eXBlLmhhc01WYXIgJiYgYmFsYW5jZWQKICAgIGxldCBtdXQgaW5kaWNlcyA6IEFycmF5IE5hdCA6PSAjW10KICAgIGxldCBtdXQgZmFjdFJlY29yZHMgOiBBcnJheSBKc29uIDo9ICNbXQogICAgZm9yIG9yaWdpbmFsRmFjdCBpbiBmYWN0cyBkbwogICAgICBsZXQgZmFjdCA6PSBvcmlnaW5hbEZhY3QuY29uc3VtZU1EYXRhCiAgICAgIGxldCBtdXQgZmFjdE9LIDo9IGZhbHNlCiAgICAgIGxldCBtdXQgaW5kZXggOiBPcHRpb24gTmF0IDo9IG5vbmUKICAgICAgbGV0IG11dCBncmlkIDogT3B0aW9uIE5hdCA6PSBub25lCiAgICAgIGxldCBtdXQgY29tcGxldGVkIDogT3B0aW9uIE5hdCA6PSBub25lCiAgICAgIGxldCBtdXQgdmFsdWVzIDogQXJyYXkgKE9wdGlvbiBJbnQpIDo9ICNbXQogICAgICBpZiBmYWN0LmlzQXBwT2ZBcml0eSBgYEVxIDMgdGhlbgogICAgICAgIGxldCBlcXVhbGl0eSA6PSBmYWN0LmdldEFwcEFyZ3MKICAgICAgICBsZXQgY2FycmllciA6PSBlcXVhbGl0eVswXSEuY29uc3VtZU1EYXRhCiAgICAgICAgbGV0IGxocyA6PSBlcXVhbGl0eVsxXSEuY29uc3VtZU1EYXRhCiAgICAgICAgbGV0IHJocyA6PSBlcXVhbGl0eVsyXSEuY29uc3VtZU1EYXRhCiAgICAgICAgaWYgKGNhcnJpZXIuaXNDb25zdE9mIGFsaWFzTmFtZSB8fCBjYXJyaWVyLmlzQ29uc3RPZiBub2RlTmFtZSkgJiYKICAgICAgICAgICAgbGhzLmlzQXBwT2ZBcml0eSBzb3VyY2VOYW1lIDMgJiYgcmhzLmlzQXBwT2ZBcml0eSBjdG9yTmFtZSA0IHRoZW4KICAgICAgICAgIGxldCBzb3VyY2VBcmdzIDo9IGxocy5nZXRBcHBBcmdzCiAgICAgICAgICBncmlkIDo9IGFzTmF0PyBzb3VyY2VBcmdzWzBdIQogICAgICAgICAgY29tcGxldGVkIDo9IGFzTmF0PyBzb3VyY2VBcmdzWzFdIQogICAgICAgICAgaW5kZXggOj0gYXNOYXQ/IHNvdXJjZUFyZ3NbMl0hCiAgICAgICAgICB2YWx1ZXMgOj0gcmhzLmdldEFwcEFyZ3MubWFwIGFzSW50PwogICAgICAgICAgZmFjdE9LIDo9IGdyaWQgPT0gc29tZSAxNjM4NCAmJiBpbmRleC5pc1NvbWUgJiYKICAgICAgICAgICAgY29tcGxldGVkID09IGluZGV4ICYmIHZhbHVlcy5hbGwgT3B0aW9uLmlzU29tZQogICAgICBpZiBsZXQgc29tZSBpIDo9IGluZGV4IHRoZW4gaW5kaWNlcyA6PSBpbmRpY2VzLnB1c2ggaQogICAgICBibG9ja09LIDo9IGJsb2NrT0sgJiYgZmFjdE9LCiAgICAgIC0tIERlY2ltYWwgc3RyaW5ncyBwcmVzZXJ2ZSB0aGUgZXhhY3QgUTgwIGludGVnZXJzIGluIEpTT04gY29uc3VtZXJzLgogICAgICBsZXQgZGVjaW1hbFZhbHVlcyA6PSB2YWx1ZXMubWFwIGZ1biB2YWx1ZSA9PiB2YWx1ZS5tYXAgdG9TdHJpbmcKICAgICAgZmFjdFJlY29yZHMgOj0gZmFjdFJlY29yZHMucHVzaCA8fCBKc29uLm1rT2JqIFsKICAgICAgICAoImdyaWQiLCB0b0pzb24gZ3JpZCksICgiY29tcGxldGVkIiwgdG9Kc29uIGNvbXBsZXRlZCksICgiaW5kZXgiLCB0b0pzb24gaW5kZXgpLAogICAgICAgICgiZm91cl9pbnRfbm9ybWFsX2Zvcm1fZGVjaW1hbCIsIHRvSnNvbiBkZWNpbWFsVmFsdWVzKSwKICAgICAgICAoImV4YWN0X3NvdXJjZV9ub2RlX2VxdWFsaXR5IiwgdG9Kc29uIGZhY3RPSyldCiAgICBsZXQgZmlyc3QgOj0gKGluZGljZXNbMF0/KS5nZXREIDAKICAgIGxldCBleHBlY3RlZCA6PSAoTGlzdC5yYW5nZSA2NCkudG9BcnJheS5tYXAgZnVuIGkgPT4gZmlyc3QgKyBpCiAgICBsZXQgYWxpZ25lZCA6PSBkZWNpZGUgKDMyNzY5IOKJpCBmaXJzdCDiiKcgZmlyc3Qg4omkIDQ5MjE3KSAmJgogICAgICAoZmlyc3QgLSAzMjc2OSkgJSA2NCA9PSAwCiAgICBibG9ja09LIDo9IGJsb2NrT0sgJiYgYWxpZ25lZCAmJiBpbmRpY2VzID09IGV4cGVjdGVkCiAgICBhbGxPSyA6PSBhbGxPSyAmJiBibG9ja09LCiAgICBhbGxJbmRpY2VzIDo9IGFsbEluZGljZXMgKysgaW5kaWNlcwogICAgbGV0IG5vZGVzIDo9IGluZm8udHlwZS5zaXplV2l0aG91dFNoYXJpbmcKICAgIHRvdGFsVHlwZU5vZGVzIDo9IHRvdGFsVHlwZU5vZGVzICsgbm9kZXMKICAgIGxldCByZWNvcmQgOj0gSnNvbi5ta09iaiBbCiAgICAgICgibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJwcml2YXRlIiwgdG9Kc29uIChpc1ByaXZhdGVOYW1lIG5hbWUpKSwKICAgICAgKCJ0aGVvcmVtIiwgdG9Kc29uIGlzVGhlb3JlbSksICgidW5zYWZlIiwgdG9Kc29uIGluZm8uaXNVbnNhZmUpLAogICAgICAoInBhcnRpYWwiLCB0b0pzb24gaW5mby5pc1BhcnRpYWwpLCAoImF4aW9tIiwgdG9Kc29uIGluZm8uaXNBeGlvbSksCiAgICAgICgiYmFsYW5jZWRfYW5kX2RlcHRoIiwgdG9Kc29uICg2IDogTmF0KSksCiAgICAgICgic2l4dHlfZm91cl9mYWN0X2JhbGFuY2VkX2FuZCIsIHRvSnNvbiBiYWxhbmNlZCksCiAgICAgICgiZmFjdF9jb3VudCIsIHRvSnNvbiBmYWN0cy5zaXplKSwgKCJpbmRpY2VzIiwgdG9Kc29uIGluZGljZXMpLCAoImZhY3RzIiwgdG9Kc29uIGZhY3RSZWNvcmRzKSwKICAgICAgKCJ0eXBlX2V4cHJfbm9kZXNfd2l0aG91dF9zaGFyaW5nIiwgdG9Kc29uIG5vZGVzKSwKICAgICAgKCJzaGFwZV9jaGVja3NfcGFzc2VkIiwgdG9Kc29uIGJsb2NrT0spXQogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X1E4MF9CTE9DSyB7cmVjb3JkLmNvbXByZXNzfSIKICBhbGxPSyA6PSBhbGxPSyAmJgogICAgYWxsSW5kaWNlcy5xc29ydCAowrcgPCDCtykgPT0gKExpc3QucmFuZ2UgMTY1MTIpLnRvQXJyYXkubWFwIChmdW4gaSA9PiAzMjc2OSArIGkpCiAgbGV0IHN1bW1hcnkgOj0gSnNvbi5ta09iaiBbCiAgICAoIm1vZHVsZSIsIHRvSnNvbiBtb2R1bGVOYW1lLnRvU3RyaW5nKSwgKCJkaWFnbm9zdGljX29ubHkiLCB0b0pzb24gdHJ1ZSksCiAgICAoInB1YmxpY19lbnRyeV9uYW1lIiwgdG9Kc29uIGVudHJ5TmFtZS50b1N0cmluZyksICgicHVibGljX2VudHJ5X2NoZWNrc19wYXNzZWQiLCB0b0pzb24gZW50cnlPSyksCiAgICAoIm5vZGVfYWxpYXNfZGlyZWN0bHlfZXF1YWxzX2hpc3RvcmljX25vZGUiLCB0b0pzb24gYWxpYXNJc0RpcmVjdCksCiAgICAoIm93bmVkX2Jsb2NrX2NvdW50IiwgdG9Kc29uIGJsb2Nrcy5zaXplKSwgKCJ0b3RhbF9mYWN0X2NvdW50IiwgdG9Kc29uIGFsbEluZGljZXMuc2l6ZSksCiAgICAoInRvdGFsX3R5cGVfZXhwcl9ub2Rlc193aXRob3V0X3NoYXJpbmciLCB0b0pzb24gdG90YWxUeXBlTm9kZXMpLAogICAgKCJpbmRpY2VzIiwgdG9Kc29uIGFsbEluZGljZXMpLCAoInNoYXBlX2NoZWNrc19wYXNzZWQiLCB0b0pzb24gYWxsT0spLAogICAgKCJQMl9hY2NlcHRhbmNlX2NyZWRpdCIsIHRvSnNvbiBmYWxzZSldCiAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X1E4MF9CTE9DS19TVU1NQVJZIHtzdW1tYXJ5LmNvbXByZXNzfSIKICB1bmxlc3MgYWxsT0sgZG8KICAgIHRocm93RXJyb3IgIlE4MCBibG9jayBzaGFwZSBkaWFnbm9zdGljcyBmYWlsZWQiCg==", validate=True)

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
require(digest(old / "Blocks.lean") == EXPECTED_SOURCE_SHA256, "Toy source differs from successful receipt")
require(digest(old / "compile.log") == compile_receipt.get("log_sha256"),
        "Compilation log differs from successful receipt")
require((old / "Blocks.olean").is_file() and (old / "Blocks.olean").stat().st_size > 0,
        "Successful toy object is missing")
require(digest(lean) == expected_lean_hash, "Lean executable differs from the pinned compiler")
require(leanchecker.is_file(), "Pinned adjacent leanchecker is missing")
version = subprocess.check_output([str(lean), "--version"], text=True).strip()
require("62eed1db4d67327ec8120be05f1a1b0847d74561" in version, "Wrong Lean version")
require(hashlib.sha256(template).hexdigest() == template_hash, "Original audit template digest changed")
require(template.count(b"ImbalancedChen.P2Winner9FiniteMomentKernel") == 2,
        "Original audit template target count changed")
require(os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= 64 * 1024 * 1024,
        "Less than 64 MiB free space")

# String.toName parses escaped identifiers; unescaped hyphens are invalid.
target = f"«{family}».«{SOURCE_ATTEMPT}».Blocks"
audit_bytes = template.replace(b"ImbalancedChen.P2Winner9FiniteMomentKernel", target.encode())
inspect_bytes = inspector_template.replace(b"@Q80_MODULE@", target.encode())
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
    "scope": "independent replay and complete owned audit of the successful first-16512 original-Q80 diagnostic module only",
    "target_module": target, "source_attempt": str(old),
    "source_sha256": EXPECTED_SOURCE_SHA256,
    "source_object_sha256": before["source_attempt_files"]["Blocks.olean"],
    "source_object_bytes": (old / "Blocks.olean").stat().st_size,
    "source_bytes": (old / "Blocks.lean").stat().st_size,
    "successful_compilation_task": "56afa9b1d65d4947bf7fe4c99ebb6a69",
    "successful_compile_receipt_sha256": digest(receipt_path),
    "successful_compile_receipt": compile_receipt,
    "template_sha256": template_hash,
    "audit_source_sha256": hashlib.sha256(audit_bytes).hexdigest(),
    "audit_template_changes": "exactly two replacements of the original target module",
    "inspector_source_sha256": hashlib.sha256(inspect_bytes).hexdigest(),
    "lean_version": version, "before": before,
    "canonical_P2_touched": False, "existing_projects_touched": False,
    "stages": {}, "original_replay_and_owned_rules_passed": False,
    "extra_block_shape_checks_passed": False,
}
print(json.dumps({k:v for k,v in result.items() if k != "successful_compile_receipt"},
                 ensure_ascii=False), flush=True)

def run_stage(stage, command, timeout=600):
    print("P24_Q80_AUDIT_STAGE_BEGIN " + stage, flush=True)
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
    # Full untruncated stage output remains in the stage log; MCP emits bounded metadata.
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
    blocks = records_with_prefix(inspect_raw, "P24_Q80_BLOCK ")
    summaries = records_with_prefix(inspect_raw, "P24_Q80_BLOCK_SUMMARY ")
    require(len(summaries) == 1 and summaries[0].get("module") == target, "Missing block summary")
    require(len(blocks) == 258 and summaries[0].get("owned_block_count") == 258 and
            summaries[0].get("shape_checks_passed") is True, "Incorrect block inventory/shape")
    require(summaries[0].get("public_entry_checks_passed") is True and
            summaries[0].get("node_alias_directly_equals_historic_node") is True and
            summaries[0].get("total_fact_count") == 16512,
            "Incorrect public entry/carrier/total fact count")
    require(sorted(summaries[0].get("indices", [])) == list(range(32769, 49281)),
            "Q80 block indices do not cover the exact original first-16512 prefix")
    require(all(block.get("shape_checks_passed") is True and
                block.get("balanced_and_depth") == 6 and block.get("fact_count") == 64
                for block in blocks), "Q80 block depth/fact count differs")
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
    bounded = {k:v for k,v in result.items() if k not in ("blocks", "block_summary")}
    if "block_summary" in result:
        bounded["block_summary"] = {k:v for k,v in result["block_summary"].items() if k != "indices"}
        bounded["block_summary"]["indices_count"] = len(result["block_summary"]["indices"])
        bounded["block_summary"]["indices_min"] = min(result["block_summary"]["indices"])
        bounded["block_summary"]["indices_max"] = max(result["block_summary"]["indices"])
    bounded["full_receipt_sha256"] = digest(out / "diagnostic.json")
    bounded["full_receipt_bytes"] = (out / "diagnostic.json").stat().st_size
    bounded["complete_stage_logs_saved"] = True
    print(json.dumps(bounded, ensure_ascii=False), flush=True)
raise SystemExit(0 if result["diagnostic_passed"] else 1)
PY
