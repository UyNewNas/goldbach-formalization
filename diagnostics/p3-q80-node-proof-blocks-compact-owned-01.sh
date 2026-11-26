set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 -B - <<'PY'
import base64, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path

# Frozen successful Q80 diagnostic d7e40f1c3ed1476ea8cb838d0dba2d0e.
# Any future attempt must independently pass compilation and match its exact source hash.
SOURCE_ATTEMPT = "attempt-001"
EXPECTED_SOURCE_SHA256 = "a6e9808c67847e27d8e09a9c2d68f117690d8b5bf9f49678e4eda14a41820d3f"

root = Path("/workspace")
family = "p24-q80-node-proof-blocks-compact-20261126"
old = root / family / SOURCE_ATTEMPT
out = root / "p24-q80-node-proof-blocks-compact-owned-20261126" / "attempt-001"
lean = Path("/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean")
leanchecker = lean.with_name("leanchecker")
expected_lean_hash = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
template_hash = "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b"
template = base64.b64decode("aW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyV2lubmVyOUZpbml0ZU1vbWVudEtlcm5lbAppbXBvcnQgTGVhbi5VdGlsLkNvbGxlY3RBeGlvbXMKc2V0X29wdGlvbiBwcC5hbGwgdHJ1ZQpzZXRfb3B0aW9uIHBwLnByb29mcyB0cnVlCnNldF9vcHRpb24gcHAuZGVlcFRlcm1zIHRydWUKc2V0X29wdGlvbiBwcC51bml2ZXJzZXMgdHJ1ZQpzZXRfb3B0aW9uIHBwLmV4cGxpY2l0IHRydWUKc2V0X29wdGlvbiBwcC5mdWxsTmFtZXMgdHJ1ZQpzZXRfb3B0aW9uIHBwLnByaXZhdGVOYW1lcyB0cnVlCnNldF9vcHRpb24gcHAubWF4U3RlcHMgMTAwMDAwMApvcGVuIExlYW4gRWxhYiBDb21tYW5kIGluCnJ1bl9jbWQgZG8KICBsZXQgZW52IOKGkCBnZXRFbnYKICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMF9RVUVVRV9JTVBPUlRTIHsodG9Kc29uIChlbnYuaGVhZGVyLm1vZHVsZU5hbWVzLm1hcCBOYW1lLnRvU3RyaW5nKSkuY29tcHJlc3N9IgogIGxldCBtb2R1bGVOYW1lIDo9IGBJbWJhbGFuY2VkQ2hlbi5QMldpbm5lcjlGaW5pdGVNb21lbnRLZXJuZWwKICBsZXQgc29tZSBpZHggOj0gZW52LmdldE1vZHVsZUlkeD8gbW9kdWxlTmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgdGFyZ2V0IG1vZHVsZSIKICBsZXQgbmFtZXMgOj0gZW52LmNvbnN0Mk1vZElkeC5mb2xkIChpbml0IDo9ICgjW10gOiBBcnJheSBOYW1lKSkgZnVuIG5zIG4gaSA9PgogICAgaWYgaSA9PSBpZHggJiYgKGVudi5maW5kPyBuKS5pc1NvbWUgdGhlbiBucy5wdXNoIG4gZWxzZSBucwogIGxldCBtdXQgc2VyaWFsaXplZCA6IEFycmF5IE5hbWUgOj0gI1tdCiAgbGV0IG11dCBmb3VuZCA6PSBmYWxzZQogIGZvciBpIGluIExpc3QucmFuZ2UgZW52LmhlYWRlci5tb2R1bGVzLnNpemUgZG8KICAgIGxldCBpbXBvcnRlZCA6PSBlbnYuaGVhZGVyLm1vZHVsZXNbaV0hCiAgICBpZiBpbXBvcnRlZC5tb2R1bGUgPT0gbW9kdWxlTmFtZSB0aGVuCiAgICAgIGlmIGZvdW5kIHRoZW4gdGhyb3dFcnJvciAiRHVwbGljYXRlIG1vZHVsZSIKICAgICAgZm91bmQgOj0gdHJ1ZQogICAgICBsZXQgZGF0YSA6PSBlbnYuaGVhZGVyLm1vZHVsZURhdGFbaV0hCiAgICAgIGlmIGRhdGEuaXNNb2R1bGUgfHwgIWltcG9ydGVkLmltcG9ydEFsbCB8fCAhaW1wb3J0ZWQuaGFzRGF0YSB0aGVuCiAgICAgICAgdGhyb3dFcnJvciAiSW5jb21wbGV0ZSBpbXBvcnRlZCBsZWdhY3kgZGF0YSIKICAgICAgc2VyaWFsaXplZCA6PSBkYXRhLmNvbnN0TmFtZXMKICB1bmxlc3MgZm91bmQgJiYgbmFtZXMuc2l6ZSA+IDAgJiYgbmFtZXMucXNvcnQgTmFtZS5sdCA9PSBzZXJpYWxpemVkLnFzb3J0IE5hbWUubHQgZG8KICAgIHRocm93RXJyb3IgIkNvbXBsZXRlIHNlcmlhbGl6ZWQvZW52aXJvbm1lbnQgaW52ZW50b3J5IG1pc21hdGNoIgogIGxpZnRJTyA8fCBJTy5wcmludGxuIHMhIlAwX1FVRVVFX0lOVkVOVE9SWSB7KEpzb24ubWtPYmogWygibW9kdWxlIiwgdG9Kc29uIG1vZHVsZU5hbWUudG9TdHJpbmcpLCAoInNlcmlhbGl6ZWQiLCB0b0pzb24gKHNlcmlhbGl6ZWQubWFwIE5hbWUudG9TdHJpbmcpKSwgKCJlbnZpcm9ubWVudCIsIHRvSnNvbiAobmFtZXMubWFwIE5hbWUudG9TdHJpbmcpKV0pLmNvbXByZXNzfSIKICBmb3IgbmFtZSBpbiBuYW1lcy5xc29ydCBOYW1lLmx0IGRvCiAgICBsZXQgc29tZSBpbmZvIDo9IGVudi5maW5kPyBuYW1lIHwgdGhyb3dFcnJvciAiTWlzc2luZyBpbnZlbnRvcmllZCBkZWNsYXJhdGlvbiIKICAgIGlmIGluZm8uaXNVbnNhZmUgfHwgaW5mby5pc1BhcnRpYWwgfHwgaW5mby5pc0F4aW9tIHRoZW4gdGhyb3dFcnJvciAiVW5zYWZlL3BhcnRpYWwvYXhpb20gdGFyZ2V0IgogICAgbGV0IGF4aW9tcyDihpAgY29sbGVjdEF4aW9tcyBuYW1lCiAgICBmb3IgYXggaW4gYXhpb21zIGRvCiAgICAgIHVubGVzcyAjW2Bwcm9wZXh0LCBgQ2xhc3NpY2FsLmNob2ljZSwgYFF1b3Quc291bmRdLmNvbnRhaW5zIGF4IGRvCiAgICAgICAgdGhyb3dFcnJvciAiRm9yYmlkZGVuIHRyYW5zaXRpdmUgYXhpb20ge2F4fSIKICAgIGxldCB0eXBlIOKGkCBsaWZ0VGVybUVsYWJNIGRvIHJldHVybiAo4oaQIE1ldGEucHBFeHByIGluZm8udHlwZSkucHJldHR5CiAgICBpZiB0eXBlLmNvbnRhaW5zICfii68nIHRoZW4gdGhyb3dFcnJvciAiVHJ1bmNhdGVkIHR5cGUiCiAgICBsZXQgcmVjb3JkIDo9IEpzb24ubWtPYmogWygibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksCiAgICAgICgidW5zYWZlIiwgdG9Kc29uIGluZm8uaXNVbnNhZmUpLCAoInBhcnRpYWwiLCB0b0pzb24gaW5mby5pc1BhcnRpYWwpLCAoImF4aW9tIiwgdG9Kc29uIGluZm8uaXNBeGlvbSksCiAgICAgICgidHlwZSIsIHRvSnNvbiB0eXBlKSwgKCJheGlvbXMiLCB0b0pzb24gKGF4aW9tcy5tYXAgTmFtZS50b1N0cmluZykpXQogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDBfUVVFVUVfREVDTCB7cmVjb3JkLmNvbXByZXNzfSIKCg==", validate=True)
inspector_template = base64.b64decode("aW1wb3J0IEBRODBfTU9EVUxFQAppbXBvcnQgTGVhbgppbXBvcnQgTGVhbi5NZXRhLlN5bS5MaXRWYWx1ZXMKCm9wZW4gTGVhbiBFbGFiIENvbW1hbmQgaW4KcnVuX2NtZCBkbwogIGxldCBlbnYg4oaQIGdldEVudgogIGxldCBtb2R1bGVOYW1lIDo9IGBAUTgwX01PRFVMRUAKICBsZXQgc29tZSBvd25lciA6PSBlbnYuZ2V0TW9kdWxlSWR4PyBtb2R1bGVOYW1lCiAgICB8IHRocm93RXJyb3IgIk1pc3NpbmcgUTgwIGRpYWdub3N0aWMgbW9kdWxlIgogIGxldCBuYW1lcyA6PSBlbnYuY29uc3QyTW9kSWR4LmZvbGQgKGluaXQgOj0gKCNbXSA6IEFycmF5IE5hbWUpKSBmdW4gbnMgbiBpID0+CiAgICBpZiBpID09IG93bmVyICYmIChlbnYuZmluZD8gbikuaXNTb21lIHRoZW4gbnMucHVzaCBuIGVsc2UgbnMKICBsZXQgcmVzb2x2ZSA6PSBmdW4gd2FudGVkID0+IG5hbWVzLmZpbHRlciBmdW4gbiA9PiBwcml2YXRlVG9Vc2VyTmFtZSBuID09IHdhbnRlZAogIGxldCBzb3VyY2VOYW1lcyA6PSByZXNvbHZlCiAgICBgUDI0UTgwTm9kZVByb29mQmxvY2tzLkltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxDb21wYWN0UTgwRW5jbG9zZXJTb3VyY2VPbmx5LnNvdXJjZVN0YXRlCiAgbGV0IGFsaWFzTmFtZXMgOj0gcmVzb2x2ZQogICAgYFAyNFE4ME5vZGVQcm9vZkJsb2Nrcy5JbWJhbGFuY2VkQ2hlbi5QMk9yaWdpbmFsQ29tcGFjdFE4MEVuY2xvc2VyU291cmNlT25seS5Ob2RlCiAgbGV0IG5vZGVOYW1lcyA6PSByZXNvbHZlCiAgICBgUDI0UTgwTm9kZVByb29mQmxvY2tzLkltYmFsYW5jZWRDaGVuLlAySGlzdG9yaWNTaWV2ZVRhYmxlU2VtYW50aWNzLkhpc3RvcmljTm9kZQogIGxldCBjdG9yTmFtZXMgOj0gcmVzb2x2ZQogICAgYFAyNFE4ME5vZGVQcm9vZkJsb2Nrcy5JbWJhbGFuY2VkQ2hlbi5QMkhpc3RvcmljU2lldmVUYWJsZVNlbWFudGljcy5IaXN0b3JpY05vZGUubWsKICBsZXQgZW50cnlOYW1lcyA6PSByZXNvbHZlIGBQMjRRODBOb2RlUHJvb2ZCbG9ja3MuTm9kZVN0ZXBQcm9vZi5maXJzdF90d29fcTgwX2Jsb2Nrc19wb3NpdGl2ZQogIHVubGVzcyBzb3VyY2VOYW1lcy5zaXplID09IDEgJiYgYWxpYXNOYW1lcy5zaXplID09IDEgJiYgbm9kZU5hbWVzLnNpemUgPT0gMSAmJgogICAgICBjdG9yTmFtZXMuc2l6ZSA9PSAxICYmIGVudHJ5TmFtZXMuc2l6ZSA9PSAxIGRvCiAgICB0aHJvd0Vycm9yICJDYW5ub3QgdW5pcXVlbHkgcmVzb2x2ZSB0aGUgZXhhY3QgUTgwIHNvdXJjZS9Ob2RlL2NvbnN0cnVjdG9yL3B1YmxpYyBlbnRyeSIKICBsZXQgc291cmNlTmFtZSA6PSBzb3VyY2VOYW1lc1swXSEKICBsZXQgYWxpYXNOYW1lIDo9IGFsaWFzTmFtZXNbMF0hCiAgbGV0IG5vZGVOYW1lIDo9IG5vZGVOYW1lc1swXSEKICBsZXQgY3Rvck5hbWUgOj0gY3Rvck5hbWVzWzBdIQogIGxldCBlbnRyeU5hbWUgOj0gZW50cnlOYW1lc1swXSEKICBsZXQgc29tZSBhbGlhc0luZm8gOj0gZW52LmZpbmQ/IGFsaWFzTmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgTm9kZSBhbGlhcyIKICAtLSBSZWFkIHRoZSBhbGlhcyBib2R5IG9ubHkuIE5vIGRlZmVxLCB3aG5mLCBvciBldmFsdWF0aW9uIG9mIGEgc291cmNlU3RhdGUgdGVybS4KICBsZXQgYWxpYXNJc0RpcmVjdCA6PSBtYXRjaCBhbGlhc0luZm8gd2l0aAogICAgfCAuZGVmbkluZm8gdmFsdWUgPT4gdmFsdWUudmFsdWUuY29uc3VtZU1EYXRhLmlzQ29uc3RPZiBub2RlTmFtZQogICAgfCBfID0+IGZhbHNlCiAgdW5sZXNzIGFsaWFzSXNEaXJlY3QgZG8KICAgIHRocm93RXJyb3IgIk5vZGUgaXMgbm90IHRoZSBleHBlY3RlZCBkaXJlY3QgSGlzdG9yaWNOb2RlIHR5cGUgYWxpYXMiCiAgbGV0IHNvbWUgZW50cnlJbmZvIDo9IGVudi5maW5kPyBlbnRyeU5hbWUgfCB0aHJvd0Vycm9yICJNaXNzaW5nIHB1YmxpYyBlbnRyeSIKICBsZXQgZW50cnlJc1RoZW9yZW0gOj0gbWF0Y2ggZW50cnlJbmZvIHdpdGgKICAgIHwgLnRobUluZm8gXyA9PiB0cnVlCiAgICB8IF8gPT4gZmFsc2UKICBsZXQgZW50cnlPSyA6PSAhaXNQcml2YXRlTmFtZSBlbnRyeU5hbWUgJiYgZW50cnlJc1RoZW9yZW0gJiYKICAgICFlbnRyeUluZm8uaXNVbnNhZmUgJiYgIWVudHJ5SW5mby5pc1BhcnRpYWwgJiYgIWVudHJ5SW5mby5pc0F4aW9tCiAgdW5sZXNzIGVudHJ5T0sgZG8KICAgIHRocm93RXJyb3IgIlRoZSBkaWFnbm9zdGljIGVudHJ5IGlzIG5vdCBhIHB1YmxpYyBzYWZlIG5vbnBhcnRpYWwgdGhlb3JlbSIKICBsZXQgYmxvY2tzIDo9IChuYW1lcy5maWx0ZXIgZnVuIG4gPT4KICAgIG4uYW55UyAoZnVuIHBhcnQgPT4gIl9xODBOb2RlUHJvb2ZCbG9jayIuaXNQcmVmaXhPZiBwYXJ0KSkucXNvcnQgTmFtZS5sdAoKICAtLSBPbmx5IGEgTmF0IGxpdGVyYWwgb3IgaXRzIGNhbm9uaWNhbCBPZk5hdCBOYXQgLyBpbnN0T2ZOYXROYXQgd3JhcHBlci4KICBsZXQgYXNOYXQ/IDogRXhwciDihpIgT3B0aW9uIE5hdCA6PSBmdW4gb3JpZ2luYWwgPT4KICAgIG1hdGNoIG9yaWdpbmFsLmNvbnN1bWVNRGF0YSB3aXRoCiAgICB8IC5saXQgKC5uYXRWYWwgbikgPT4gc29tZSBuCiAgICB8IC5hcHAgKC5hcHAgKC5hcHAgKC5jb25zdCBvZk5hdE5hbWUgXykgKC5jb25zdCBuYXROYW1lIFtdKSkKICAgICAgICAoLmxpdCAoLm5hdFZhbCBuKSkpICguYXBwICguY29uc3QgaW5zdE5hbWUgW10pICgubGl0ICgubmF0VmFsIG0pKSkgPT4KICAgICAgICBpZiBvZk5hdE5hbWUgPT0gYGBPZk5hdC5vZk5hdCAmJiBuYXROYW1lID09IGBgTmF0ICYmCiAgICAgICAgICAgIGluc3ROYW1lID09IGBgaW5zdE9mTmF0TmF0ICYmIG4gPT0gbSB0aGVuIHNvbWUgbiBlbHNlIG5vbmUKICAgIHwgXyA9PiBub25lCiAgLS0gS2VlcCB0aGUgb3JpZ2luYWwgU3ltIGxpdGVyYWwgZm9ybXMsIHBsdXMgZXhhY3QgSW50IGNvbnN0cnVjdG9ycyBvbiB0aGUKICAtLSByZWNvZ25pemVkIE5hdCBzeW50YXguIG5lZ1N1Y2MgbiBkZW5vdGVzIC0obisxKSwgbm90IC1uLgogIGxldCBhc0ludD8gOiBFeHByIOKGkiBPcHRpb24gSW50IDo9IGZ1biBvcmlnaW5hbCA9PgogICAgbGV0IGUgOj0gb3JpZ2luYWwuY29uc3VtZU1EYXRhCiAgICBtYXRjaCBlIHdpdGgKICAgIHwgLmFwcCAoLmNvbnN0IGN0b3IgW10pIG4gPT4KICAgICAgICBpZiBjdG9yID09IGBgSW50Lm9mTmF0IHRoZW4gKGFzTmF0PyBuKS5tYXAgSW50Lm9mTmF0CiAgICAgICAgZWxzZSBpZiBjdG9yID09IGBgSW50Lm5lZ1N1Y2MgdGhlbiAoYXNOYXQ/IG4pLm1hcCBJbnQubmVnU3VjYwogICAgICAgIGVsc2Ugbm9uZQogICAgfCBfID0+IExlYW4uTWV0YS5TeW0uZ2V0SW50VmFsdWU/IGUKCiAgbGV0IG11dCBhbGxPSyA6PSBibG9ja3Muc2l6ZSA9PSAyCiAgbGV0IG11dCBhbGxJbmRpY2VzIDogQXJyYXkgTmF0IDo9ICNbXQogIGxldCBtdXQgdG90YWxUeXBlTm9kZXMgOj0gMAogIGZvciBuYW1lIGluIGJsb2NrcyBkbwogICAgbGV0IHNvbWUgaW5mbyA6PSBlbnYuZmluZD8gbmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgZ2VuZXJhdGVkIFE4MCBibG9jayIKICAgIGxldCBpc1RoZW9yZW0gOj0gbWF0Y2ggaW5mbyB3aXRoCiAgICAgIHwgLnRobUluZm8gXyA9PiB0cnVlCiAgICAgIHwgXyA9PiBmYWxzZQogICAgbGV0IHR5cGUgOj0gaW5mby50eXBlLmNvbnN1bWVNRGF0YQogICAgbGV0IG11dCBmYWN0cyA6IEFycmF5IEV4cHIgOj0gI1t0eXBlXQogICAgbGV0IG11dCBiYWxhbmNlZCA6PSB0cnVlCiAgICBmb3IgXyBpbiBbOjZdIGRvCiAgICAgIGxldCBtdXQgbmV4dCA6IEFycmF5IEV4cHIgOj0gI1tdCiAgICAgIGZvciBvcmlnaW5hbCBpbiBmYWN0cyBkbwogICAgICAgIGxldCB0ZXJtIDo9IG9yaWdpbmFsLmNvbnN1bWVNRGF0YQogICAgICAgIGlmIHRlcm0uaXNBcHBPZkFyaXR5IGBgQW5kIDIgdGhlbgogICAgICAgICAgbGV0IGFyZ3MgOj0gdGVybS5nZXRBcHBBcmdzCiAgICAgICAgICBuZXh0IDo9IG5leHQucHVzaCBhcmdzWzBdIQogICAgICAgICAgbmV4dCA6PSBuZXh0LnB1c2ggYXJnc1sxXSEKICAgICAgICBlbHNlCiAgICAgICAgICBiYWxhbmNlZCA6PSBmYWxzZQogICAgICBmYWN0cyA6PSBuZXh0CiAgICBiYWxhbmNlZCA6PSBiYWxhbmNlZCAmJiBmYWN0cy5zaXplID09IDY0CiAgICBsZXQgbXV0IGJsb2NrT0sgOj0gaXNQcml2YXRlTmFtZSBuYW1lICYmIGlzVGhlb3JlbSAmJgogICAgICAhaW5mby5pc1Vuc2FmZSAmJiAhaW5mby5pc1BhcnRpYWwgJiYgIWluZm8uaXNBeGlvbSAmJgogICAgICAhdHlwZS5oYXNGVmFyICYmICF0eXBlLmhhc01WYXIgJiYgYmFsYW5jZWQKICAgIGxldCBtdXQgaW5kaWNlcyA6IEFycmF5IE5hdCA6PSAjW10KICAgIGxldCBtdXQgZmFjdFJlY29yZHMgOiBBcnJheSBKc29uIDo9ICNbXQogICAgZm9yIG9yaWdpbmFsRmFjdCBpbiBmYWN0cyBkbwogICAgICBsZXQgZmFjdCA6PSBvcmlnaW5hbEZhY3QuY29uc3VtZU1EYXRhCiAgICAgIGxldCBtdXQgZmFjdE9LIDo9IGZhbHNlCiAgICAgIGxldCBtdXQgaW5kZXggOiBPcHRpb24gTmF0IDo9IG5vbmUKICAgICAgbGV0IG11dCBncmlkIDogT3B0aW9uIE5hdCA6PSBub25lCiAgICAgIGxldCBtdXQgY29tcGxldGVkIDogT3B0aW9uIE5hdCA6PSBub25lCiAgICAgIGxldCBtdXQgdmFsdWVzIDogQXJyYXkgKE9wdGlvbiBJbnQpIDo9ICNbXQogICAgICBpZiBmYWN0LmlzQXBwT2ZBcml0eSBgYEVxIDMgdGhlbgogICAgICAgIGxldCBlcXVhbGl0eSA6PSBmYWN0LmdldEFwcEFyZ3MKICAgICAgICBsZXQgY2FycmllciA6PSBlcXVhbGl0eVswXSEuY29uc3VtZU1EYXRhCiAgICAgICAgbGV0IGxocyA6PSBlcXVhbGl0eVsxXSEuY29uc3VtZU1EYXRhCiAgICAgICAgbGV0IHJocyA6PSBlcXVhbGl0eVsyXSEuY29uc3VtZU1EYXRhCiAgICAgICAgaWYgKGNhcnJpZXIuaXNDb25zdE9mIGFsaWFzTmFtZSB8fCBjYXJyaWVyLmlzQ29uc3RPZiBub2RlTmFtZSkgJiYKICAgICAgICAgICAgbGhzLmlzQXBwT2ZBcml0eSBzb3VyY2VOYW1lIDMgJiYgcmhzLmlzQXBwT2ZBcml0eSBjdG9yTmFtZSA0IHRoZW4KICAgICAgICAgIGxldCBzb3VyY2VBcmdzIDo9IGxocy5nZXRBcHBBcmdzCiAgICAgICAgICBncmlkIDo9IGFzTmF0PyBzb3VyY2VBcmdzWzBdIQogICAgICAgICAgY29tcGxldGVkIDo9IGFzTmF0PyBzb3VyY2VBcmdzWzFdIQogICAgICAgICAgaW5kZXggOj0gYXNOYXQ/IHNvdXJjZUFyZ3NbMl0hCiAgICAgICAgICB2YWx1ZXMgOj0gcmhzLmdldEFwcEFyZ3MubWFwIGFzSW50PwogICAgICAgICAgZmFjdE9LIDo9IGdyaWQgPT0gc29tZSAxNjM4NCAmJiBpbmRleC5pc1NvbWUgJiYKICAgICAgICAgICAgY29tcGxldGVkID09IGluZGV4ICYmIHZhbHVlcy5hbGwgT3B0aW9uLmlzU29tZQogICAgICBpZiBsZXQgc29tZSBpIDo9IGluZGV4IHRoZW4gaW5kaWNlcyA6PSBpbmRpY2VzLnB1c2ggaQogICAgICBibG9ja09LIDo9IGJsb2NrT0sgJiYgZmFjdE9LCiAgICAgIC0tIERlY2ltYWwgc3RyaW5ncyBwcmVzZXJ2ZSB0aGUgZXhhY3QgUTgwIGludGVnZXJzIGluIEpTT04gY29uc3VtZXJzLgogICAgICBsZXQgZGVjaW1hbFZhbHVlcyA6PSB2YWx1ZXMubWFwIGZ1biB2YWx1ZSA9PiB2YWx1ZS5tYXAgdG9TdHJpbmcKICAgICAgZmFjdFJlY29yZHMgOj0gZmFjdFJlY29yZHMucHVzaCA8fCBKc29uLm1rT2JqIFsKICAgICAgICAoImdyaWQiLCB0b0pzb24gZ3JpZCksICgiY29tcGxldGVkIiwgdG9Kc29uIGNvbXBsZXRlZCksICgiaW5kZXgiLCB0b0pzb24gaW5kZXgpLAogICAgICAgICgiZm91cl9pbnRfbm9ybWFsX2Zvcm1fZGVjaW1hbCIsIHRvSnNvbiBkZWNpbWFsVmFsdWVzKSwKICAgICAgICAoImV4YWN0X3NvdXJjZV9ub2RlX2VxdWFsaXR5IiwgdG9Kc29uIGZhY3RPSyldCiAgICBsZXQgZmlyc3QgOj0gKExpc3QucmFuZ2UgNjQpLnRvQXJyYXkubWFwIGZ1biBpID0+IDMyNzY5ICsgaQogICAgbGV0IHNlY29uZCA6PSAoTGlzdC5yYW5nZSA2NCkudG9BcnJheS5tYXAgZnVuIGkgPT4gMzI4MzMgKyBpCiAgICBibG9ja09LIDo9IGJsb2NrT0sgJiYgKGluZGljZXMgPT0gZmlyc3QgfHwgaW5kaWNlcyA9PSBzZWNvbmQpCiAgICBhbGxPSyA6PSBhbGxPSyAmJiBibG9ja09LCiAgICBhbGxJbmRpY2VzIDo9IGFsbEluZGljZXMgKysgaW5kaWNlcwogICAgbGV0IG5vZGVzIDo9IGluZm8udHlwZS5zaXplV2l0aG91dFNoYXJpbmcKICAgIHRvdGFsVHlwZU5vZGVzIDo9IHRvdGFsVHlwZU5vZGVzICsgbm9kZXMKICAgIGxldCByZWNvcmQgOj0gSnNvbi5ta09iaiBbCiAgICAgICgibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJwcml2YXRlIiwgdG9Kc29uIChpc1ByaXZhdGVOYW1lIG5hbWUpKSwKICAgICAgKCJ0aGVvcmVtIiwgdG9Kc29uIGlzVGhlb3JlbSksICgidW5zYWZlIiwgdG9Kc29uIGluZm8uaXNVbnNhZmUpLAogICAgICAoInBhcnRpYWwiLCB0b0pzb24gaW5mby5pc1BhcnRpYWwpLCAoImF4aW9tIiwgdG9Kc29uIGluZm8uaXNBeGlvbSksCiAgICAgICgiYmFsYW5jZWRfYW5kX2RlcHRoIiwgdG9Kc29uICg2IDogTmF0KSksCiAgICAgICgic2l4dHlfZm91cl9mYWN0X2JhbGFuY2VkX2FuZCIsIHRvSnNvbiBiYWxhbmNlZCksCiAgICAgICgiZmFjdF9jb3VudCIsIHRvSnNvbiBmYWN0cy5zaXplKSwgKCJpbmRpY2VzIiwgdG9Kc29uIGluZGljZXMpLCAoImZhY3RzIiwgdG9Kc29uIGZhY3RSZWNvcmRzKSwKICAgICAgKCJ0eXBlX2V4cHJfbm9kZXNfd2l0aG91dF9zaGFyaW5nIiwgdG9Kc29uIG5vZGVzKSwKICAgICAgKCJzaGFwZV9jaGVja3NfcGFzc2VkIiwgdG9Kc29uIGJsb2NrT0spXQogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X1E4MF9CTE9DSyB7cmVjb3JkLmNvbXByZXNzfSIKICBhbGxPSyA6PSBhbGxPSyAmJgogICAgYWxsSW5kaWNlcy5xc29ydCAowrcgPCDCtykgPT0gKExpc3QucmFuZ2UgMTI4KS50b0FycmF5Lm1hcCAoZnVuIGkgPT4gMzI3NjkgKyBpKQogIGxldCBzdW1tYXJ5IDo9IEpzb24ubWtPYmogWwogICAgKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksICgiZGlhZ25vc3RpY19vbmx5IiwgdG9Kc29uIHRydWUpLAogICAgKCJwdWJsaWNfZW50cnlfbmFtZSIsIHRvSnNvbiBlbnRyeU5hbWUudG9TdHJpbmcpLCAoInB1YmxpY19lbnRyeV9jaGVja3NfcGFzc2VkIiwgdG9Kc29uIGVudHJ5T0spLAogICAgKCJub2RlX2FsaWFzX2RpcmVjdGx5X2VxdWFsc19oaXN0b3JpY19ub2RlIiwgdG9Kc29uIGFsaWFzSXNEaXJlY3QpLAogICAgKCJvd25lZF9ibG9ja19jb3VudCIsIHRvSnNvbiBibG9ja3Muc2l6ZSksICgidG90YWxfZmFjdF9jb3VudCIsIHRvSnNvbiBhbGxJbmRpY2VzLnNpemUpLAogICAgKCJ0b3RhbF90eXBlX2V4cHJfbm9kZXNfd2l0aG91dF9zaGFyaW5nIiwgdG9Kc29uIHRvdGFsVHlwZU5vZGVzKSwKICAgICgiaW5kaWNlcyIsIHRvSnNvbiBhbGxJbmRpY2VzKSwgKCJzaGFwZV9jaGVja3NfcGFzc2VkIiwgdG9Kc29uIGFsbE9LKSwKICAgICgiUDJfYWNjZXB0YW5jZV9jcmVkaXQiLCB0b0pzb24gZmFsc2UpXQogIGxpZnRJTyA8fCBJTy5wcmludGxuIHMhIlAyNF9RODBfQkxPQ0tfU1VNTUFSWSB7c3VtbWFyeS5jb21wcmVzc30iCiAgdW5sZXNzIGFsbE9LIGRvCiAgICB0aHJvd0Vycm9yICJRODAgYmxvY2sgc2hhcGUgZGlhZ25vc3RpY3MgZmFpbGVkIgo=", validate=True)

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
    "scope": "independent replay and complete owned audit of the successful first-128 original-Q80 diagnostic module only",
    "target_module": target, "source_attempt": str(old),
    "source_sha256": EXPECTED_SOURCE_SHA256,
    "source_object_sha256": before["source_attempt_files"]["Blocks.olean"],
    "source_object_bytes": (old / "Blocks.olean").stat().st_size,
    "source_bytes": (old / "Blocks.lean").stat().st_size,
    "successful_compilation_task": "d7e40f1c3ed1476ea8cb838d0dba2d0e",
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

def run_stage(stage, command, timeout=120):
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
    blocks = records_with_prefix(inspect_raw, "P24_Q80_BLOCK ")
    summaries = records_with_prefix(inspect_raw, "P24_Q80_BLOCK_SUMMARY ")
    require(len(summaries) == 1 and summaries[0].get("module") == target, "Missing block summary")
    require(len(blocks) == 2 and summaries[0].get("owned_block_count") == 2 and
            summaries[0].get("shape_checks_passed") is True, "Incorrect block inventory/shape")
    require(summaries[0].get("public_entry_checks_passed") is True and
            summaries[0].get("node_alias_directly_equals_historic_node") is True and
            summaries[0].get("total_fact_count") == 128,
            "Incorrect public entry/carrier/total fact count")
    require(sorted(summaries[0].get("indices", [])) == list(range(32769, 32897)),
            "Q80 block indices do not cover the exact original first-128 prefix")
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
    print(json.dumps(result, ensure_ascii=False), flush=True)
raise SystemExit(0 if result["diagnostic_passed"] else 1)
PY

