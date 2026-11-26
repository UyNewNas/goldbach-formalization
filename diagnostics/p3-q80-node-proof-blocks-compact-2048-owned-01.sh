set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 -B - <<'PY'
import base64, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path

# Frozen successful Q80 diagnostic fa34b07b43b443c38d4ab199956d9443.
# Any future attempt must independently pass compilation and match its exact source hash.
SOURCE_ATTEMPT = "attempt-001"
EXPECTED_SOURCE_SHA256 = "3e8bbb0eecf9417da11931c859cdc304b5f45b549bbbe2c34fa7d7208e820669"

root = Path("/workspace")
family = "p24-q80-node-proof-blocks-compact-2048-20261126"
old = root / family / SOURCE_ATTEMPT
out = root / "p24-q80-node-proof-blocks-compact-2048-owned-20261126" / "attempt-001"
lean = Path("/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean")
leanchecker = lean.with_name("leanchecker")
expected_lean_hash = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
template_hash = "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b"
template = base64.b64decode("aW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyV2lubmVyOUZpbml0ZU1vbWVudEtlcm5lbAppbXBvcnQgTGVhbi5VdGlsLkNvbGxlY3RBeGlvbXMKc2V0X29wdGlvbiBwcC5hbGwgdHJ1ZQpzZXRfb3B0aW9uIHBwLnByb29mcyB0cnVlCnNldF9vcHRpb24gcHAuZGVlcFRlcm1zIHRydWUKc2V0X29wdGlvbiBwcC51bml2ZXJzZXMgdHJ1ZQpzZXRfb3B0aW9uIHBwLmV4cGxpY2l0IHRydWUKc2V0X29wdGlvbiBwcC5mdWxsTmFtZXMgdHJ1ZQpzZXRfb3B0aW9uIHBwLnByaXZhdGVOYW1lcyB0cnVlCnNldF9vcHRpb24gcHAubWF4U3RlcHMgMTAwMDAwMApvcGVuIExlYW4gRWxhYiBDb21tYW5kIGluCnJ1bl9jbWQgZG8KICBsZXQgZW52IOKGkCBnZXRFbnYKICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMF9RVUVVRV9JTVBPUlRTIHsodG9Kc29uIChlbnYuaGVhZGVyLm1vZHVsZU5hbWVzLm1hcCBOYW1lLnRvU3RyaW5nKSkuY29tcHJlc3N9IgogIGxldCBtb2R1bGVOYW1lIDo9IGBJbWJhbGFuY2VkQ2hlbi5QMldpbm5lcjlGaW5pdGVNb21lbnRLZXJuZWwKICBsZXQgc29tZSBpZHggOj0gZW52LmdldE1vZHVsZUlkeD8gbW9kdWxlTmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgdGFyZ2V0IG1vZHVsZSIKICBsZXQgbmFtZXMgOj0gZW52LmNvbnN0Mk1vZElkeC5mb2xkIChpbml0IDo9ICgjW10gOiBBcnJheSBOYW1lKSkgZnVuIG5zIG4gaSA9PgogICAgaWYgaSA9PSBpZHggJiYgKGVudi5maW5kPyBuKS5pc1NvbWUgdGhlbiBucy5wdXNoIG4gZWxzZSBucwogIGxldCBtdXQgc2VyaWFsaXplZCA6IEFycmF5IE5hbWUgOj0gI1tdCiAgbGV0IG11dCBmb3VuZCA6PSBmYWxzZQogIGZvciBpIGluIExpc3QucmFuZ2UgZW52LmhlYWRlci5tb2R1bGVzLnNpemUgZG8KICAgIGxldCBpbXBvcnRlZCA6PSBlbnYuaGVhZGVyLm1vZHVsZXNbaV0hCiAgICBpZiBpbXBvcnRlZC5tb2R1bGUgPT0gbW9kdWxlTmFtZSB0aGVuCiAgICAgIGlmIGZvdW5kIHRoZW4gdGhyb3dFcnJvciAiRHVwbGljYXRlIG1vZHVsZSIKICAgICAgZm91bmQgOj0gdHJ1ZQogICAgICBsZXQgZGF0YSA6PSBlbnYuaGVhZGVyLm1vZHVsZURhdGFbaV0hCiAgICAgIGlmIGRhdGEuaXNNb2R1bGUgfHwgIWltcG9ydGVkLmltcG9ydEFsbCB8fCAhaW1wb3J0ZWQuaGFzRGF0YSB0aGVuCiAgICAgICAgdGhyb3dFcnJvciAiSW5jb21wbGV0ZSBpbXBvcnRlZCBsZWdhY3kgZGF0YSIKICAgICAgc2VyaWFsaXplZCA6PSBkYXRhLmNvbnN0TmFtZXMKICB1bmxlc3MgZm91bmQgJiYgbmFtZXMuc2l6ZSA+IDAgJiYgbmFtZXMucXNvcnQgTmFtZS5sdCA9PSBzZXJpYWxpemVkLnFzb3J0IE5hbWUubHQgZG8KICAgIHRocm93RXJyb3IgIkNvbXBsZXRlIHNlcmlhbGl6ZWQvZW52aXJvbm1lbnQgaW52ZW50b3J5IG1pc21hdGNoIgogIGxpZnRJTyA8fCBJTy5wcmludGxuIHMhIlAwX1FVRVVFX0lOVkVOVE9SWSB7KEpzb24ubWtPYmogWygibW9kdWxlIiwgdG9Kc29uIG1vZHVsZU5hbWUudG9TdHJpbmcpLCAoInNlcmlhbGl6ZWQiLCB0b0pzb24gKHNlcmlhbGl6ZWQubWFwIE5hbWUudG9TdHJpbmcpKSwgKCJlbnZpcm9ubWVudCIsIHRvSnNvbiAobmFtZXMubWFwIE5hbWUudG9TdHJpbmcpKV0pLmNvbXByZXNzfSIKICBmb3IgbmFtZSBpbiBuYW1lcy5xc29ydCBOYW1lLmx0IGRvCiAgICBsZXQgc29tZSBpbmZvIDo9IGVudi5maW5kPyBuYW1lIHwgdGhyb3dFcnJvciAiTWlzc2luZyBpbnZlbnRvcmllZCBkZWNsYXJhdGlvbiIKICAgIGlmIGluZm8uaXNVbnNhZmUgfHwgaW5mby5pc1BhcnRpYWwgfHwgaW5mby5pc0F4aW9tIHRoZW4gdGhyb3dFcnJvciAiVW5zYWZlL3BhcnRpYWwvYXhpb20gdGFyZ2V0IgogICAgbGV0IGF4aW9tcyDihpAgY29sbGVjdEF4aW9tcyBuYW1lCiAgICBmb3IgYXggaW4gYXhpb21zIGRvCiAgICAgIHVubGVzcyAjW2Bwcm9wZXh0LCBgQ2xhc3NpY2FsLmNob2ljZSwgYFF1b3Quc291bmRdLmNvbnRhaW5zIGF4IGRvCiAgICAgICAgdGhyb3dFcnJvciAiRm9yYmlkZGVuIHRyYW5zaXRpdmUgYXhpb20ge2F4fSIKICAgIGxldCB0eXBlIOKGkCBsaWZ0VGVybUVsYWJNIGRvIHJldHVybiAo4oaQIE1ldGEucHBFeHByIGluZm8udHlwZSkucHJldHR5CiAgICBpZiB0eXBlLmNvbnRhaW5zICfii68nIHRoZW4gdGhyb3dFcnJvciAiVHJ1bmNhdGVkIHR5cGUiCiAgICBsZXQgcmVjb3JkIDo9IEpzb24ubWtPYmogWygibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksCiAgICAgICgidW5zYWZlIiwgdG9Kc29uIGluZm8uaXNVbnNhZmUpLCAoInBhcnRpYWwiLCB0b0pzb24gaW5mby5pc1BhcnRpYWwpLCAoImF4aW9tIiwgdG9Kc29uIGluZm8uaXNBeGlvbSksCiAgICAgICgidHlwZSIsIHRvSnNvbiB0eXBlKSwgKCJheGlvbXMiLCB0b0pzb24gKGF4aW9tcy5tYXAgTmFtZS50b1N0cmluZykpXQogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDBfUVVFVUVfREVDTCB7cmVjb3JkLmNvbXByZXNzfSIKCg==", validate=True)
inspector_template = base64.b64decode("aW1wb3J0IEBRODBfTU9EVUxFQAppbXBvcnQgTGVhbgppbXBvcnQgTGVhbi5NZXRhLlN5bS5MaXRWYWx1ZXMKCm9wZW4gTGVhbiBFbGFiIENvbW1hbmQgaW4KcnVuX2NtZCBkbwogIGxldCBlbnYg4oaQIGdldEVudgogIGxldCBtb2R1bGVOYW1lIDo9IGBAUTgwX01PRFVMRUAKICBsZXQgc29tZSBvd25lciA6PSBlbnYuZ2V0TW9kdWxlSWR4PyBtb2R1bGVOYW1lCiAgICB8IHRocm93RXJyb3IgIk1pc3NpbmcgUTgwIGRpYWdub3N0aWMgbW9kdWxlIgogIGxldCBuYW1lcyA6PSBlbnYuY29uc3QyTW9kSWR4LmZvbGQgKGluaXQgOj0gKCNbXSA6IEFycmF5IE5hbWUpKSBmdW4gbnMgbiBpID0+CiAgICBpZiBpID09IG93bmVyICYmIChlbnYuZmluZD8gbikuaXNTb21lIHRoZW4gbnMucHVzaCBuIGVsc2UgbnMKICBsZXQgcmVzb2x2ZSA6PSBmdW4gd2FudGVkID0+IG5hbWVzLmZpbHRlciBmdW4gbiA9PiBwcml2YXRlVG9Vc2VyTmFtZSBuID09IHdhbnRlZAogIGxldCBzb3VyY2VOYW1lcyA6PSByZXNvbHZlCiAgICBgUDI0UTgwTm9kZVByb29mQmxvY2tzLkltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxDb21wYWN0UTgwRW5jbG9zZXJTb3VyY2VPbmx5LnNvdXJjZVN0YXRlCiAgbGV0IGFsaWFzTmFtZXMgOj0gcmVzb2x2ZQogICAgYFAyNFE4ME5vZGVQcm9vZkJsb2Nrcy5JbWJhbGFuY2VkQ2hlbi5QMk9yaWdpbmFsQ29tcGFjdFE4MEVuY2xvc2VyU291cmNlT25seS5Ob2RlCiAgbGV0IG5vZGVOYW1lcyA6PSByZXNvbHZlCiAgICBgUDI0UTgwTm9kZVByb29mQmxvY2tzLkltYmFsYW5jZWRDaGVuLlAySGlzdG9yaWNTaWV2ZVRhYmxlU2VtYW50aWNzLkhpc3RvcmljTm9kZQogIGxldCBjdG9yTmFtZXMgOj0gcmVzb2x2ZQogICAgYFAyNFE4ME5vZGVQcm9vZkJsb2Nrcy5JbWJhbGFuY2VkQ2hlbi5QMkhpc3RvcmljU2lldmVUYWJsZVNlbWFudGljcy5IaXN0b3JpY05vZGUubWsKICBsZXQgZW50cnlOYW1lcyA6PSByZXNvbHZlIGBQMjRRODBOb2RlUHJvb2ZCbG9ja3MuTm9kZVN0ZXBQcm9vZi5wcmVmaXhfMjA0OF9xODBfYmxvY2tzX3Bvc2l0aXZlCiAgdW5sZXNzIHNvdXJjZU5hbWVzLnNpemUgPT0gMSAmJiBhbGlhc05hbWVzLnNpemUgPT0gMSAmJiBub2RlTmFtZXMuc2l6ZSA9PSAxICYmCiAgICAgIGN0b3JOYW1lcy5zaXplID09IDEgJiYgZW50cnlOYW1lcy5zaXplID09IDEgZG8KICAgIHRocm93RXJyb3IgIkNhbm5vdCB1bmlxdWVseSByZXNvbHZlIHRoZSBleGFjdCBRODAgc291cmNlL05vZGUvY29uc3RydWN0b3IvcHVibGljIGVudHJ5IgogIGxldCBzb3VyY2VOYW1lIDo9IHNvdXJjZU5hbWVzWzBdIQogIGxldCBhbGlhc05hbWUgOj0gYWxpYXNOYW1lc1swXSEKICBsZXQgbm9kZU5hbWUgOj0gbm9kZU5hbWVzWzBdIQogIGxldCBjdG9yTmFtZSA6PSBjdG9yTmFtZXNbMF0hCiAgbGV0IGVudHJ5TmFtZSA6PSBlbnRyeU5hbWVzWzBdIQogIGxldCBzb21lIGFsaWFzSW5mbyA6PSBlbnYuZmluZD8gYWxpYXNOYW1lIHwgdGhyb3dFcnJvciAiTWlzc2luZyBOb2RlIGFsaWFzIgogIC0tIFJlYWQgdGhlIGFsaWFzIGJvZHkgb25seS4gTm8gZGVmZXEsIHdobmYsIG9yIGV2YWx1YXRpb24gb2YgYSBzb3VyY2VTdGF0ZSB0ZXJtLgogIGxldCBhbGlhc0lzRGlyZWN0IDo9IG1hdGNoIGFsaWFzSW5mbyB3aXRoCiAgICB8IC5kZWZuSW5mbyB2YWx1ZSA9PiB2YWx1ZS52YWx1ZS5jb25zdW1lTURhdGEuaXNDb25zdE9mIG5vZGVOYW1lCiAgICB8IF8gPT4gZmFsc2UKICB1bmxlc3MgYWxpYXNJc0RpcmVjdCBkbwogICAgdGhyb3dFcnJvciAiTm9kZSBpcyBub3QgdGhlIGV4cGVjdGVkIGRpcmVjdCBIaXN0b3JpY05vZGUgdHlwZSBhbGlhcyIKICBsZXQgc29tZSBlbnRyeUluZm8gOj0gZW52LmZpbmQ/IGVudHJ5TmFtZSB8IHRocm93RXJyb3IgIk1pc3NpbmcgcHVibGljIGVudHJ5IgogIGxldCBlbnRyeUlzVGhlb3JlbSA6PSBtYXRjaCBlbnRyeUluZm8gd2l0aAogICAgfCAudGhtSW5mbyBfID0+IHRydWUKICAgIHwgXyA9PiBmYWxzZQogIGxldCBlbnRyeU9LIDo9ICFpc1ByaXZhdGVOYW1lIGVudHJ5TmFtZSAmJiBlbnRyeUlzVGhlb3JlbSAmJgogICAgIWVudHJ5SW5mby5pc1Vuc2FmZSAmJiAhZW50cnlJbmZvLmlzUGFydGlhbCAmJiAhZW50cnlJbmZvLmlzQXhpb20KICB1bmxlc3MgZW50cnlPSyBkbwogICAgdGhyb3dFcnJvciAiVGhlIGRpYWdub3N0aWMgZW50cnkgaXMgbm90IGEgcHVibGljIHNhZmUgbm9ucGFydGlhbCB0aGVvcmVtIgogIGxldCBibG9ja3MgOj0gKG5hbWVzLmZpbHRlciBmdW4gbiA9PgogICAgbi5hbnlTIChmdW4gcGFydCA9PiAiX3E4ME5vZGVQcm9vZkJsb2NrIi5pc1ByZWZpeE9mIHBhcnQpKS5xc29ydCBOYW1lLmx0CgogIC0tIE9ubHkgYSBOYXQgbGl0ZXJhbCBvciBpdHMgY2Fub25pY2FsIE9mTmF0IE5hdCAvIGluc3RPZk5hdE5hdCB3cmFwcGVyLgogIGxldCBhc05hdD8gOiBFeHByIOKGkiBPcHRpb24gTmF0IDo9IGZ1biBvcmlnaW5hbCA9PgogICAgbWF0Y2ggb3JpZ2luYWwuY29uc3VtZU1EYXRhIHdpdGgKICAgIHwgLmxpdCAoLm5hdFZhbCBuKSA9PiBzb21lIG4KICAgIHwgLmFwcCAoLmFwcCAoLmFwcCAoLmNvbnN0IG9mTmF0TmFtZSBfKSAoLmNvbnN0IG5hdE5hbWUgW10pKQogICAgICAgICgubGl0ICgubmF0VmFsIG4pKSkgKC5hcHAgKC5jb25zdCBpbnN0TmFtZSBbXSkgKC5saXQgKC5uYXRWYWwgbSkpKSA9PgogICAgICAgIGlmIG9mTmF0TmFtZSA9PSBgYE9mTmF0Lm9mTmF0ICYmIG5hdE5hbWUgPT0gYGBOYXQgJiYKICAgICAgICAgICAgaW5zdE5hbWUgPT0gYGBpbnN0T2ZOYXROYXQgJiYgbiA9PSBtIHRoZW4gc29tZSBuIGVsc2Ugbm9uZQogICAgfCBfID0+IG5vbmUKICAtLSBLZWVwIHRoZSBvcmlnaW5hbCBTeW0gbGl0ZXJhbCBmb3JtcywgcGx1cyBleGFjdCBJbnQgY29uc3RydWN0b3JzIG9uIHRoZQogIC0tIHJlY29nbml6ZWQgTmF0IHN5bnRheC4gbmVnU3VjYyBuIGRlbm90ZXMgLShuKzEpLCBub3QgLW4uCiAgbGV0IGFzSW50PyA6IEV4cHIg4oaSIE9wdGlvbiBJbnQgOj0gZnVuIG9yaWdpbmFsID0+CiAgICBsZXQgZSA6PSBvcmlnaW5hbC5jb25zdW1lTURhdGEKICAgIG1hdGNoIGUgd2l0aAogICAgfCAuYXBwICguY29uc3QgY3RvciBbXSkgbiA9PgogICAgICAgIGlmIGN0b3IgPT0gYGBJbnQub2ZOYXQgdGhlbiAoYXNOYXQ/IG4pLm1hcCBJbnQub2ZOYXQKICAgICAgICBlbHNlIGlmIGN0b3IgPT0gYGBJbnQubmVnU3VjYyB0aGVuIChhc05hdD8gbikubWFwIEludC5uZWdTdWNjCiAgICAgICAgZWxzZSBub25lCiAgICB8IF8gPT4gTGVhbi5NZXRhLlN5bS5nZXRJbnRWYWx1ZT8gZQoKICBsZXQgbXV0IGFsbE9LIDo9IGJsb2Nrcy5zaXplID09IDIwNDgKICBsZXQgbXV0IGFsbEluZGljZXMgOiBBcnJheSBOYXQgOj0gI1tdCiAgbGV0IG11dCB0b3RhbFR5cGVOb2RlcyA6PSAwCiAgZm9yIG5hbWUgaW4gYmxvY2tzIGRvCiAgICBsZXQgc29tZSBpbmZvIDo9IGVudi5maW5kPyBuYW1lIHwgdGhyb3dFcnJvciAiTWlzc2luZyBnZW5lcmF0ZWQgUTgwIGJsb2NrIgogICAgbGV0IGlzVGhlb3JlbSA6PSBtYXRjaCBpbmZvIHdpdGgKICAgICAgfCAudGhtSW5mbyBfID0+IHRydWUKICAgICAgfCBfID0+IGZhbHNlCiAgICBsZXQgdHlwZSA6PSBpbmZvLnR5cGUuY29uc3VtZU1EYXRhCiAgICBsZXQgbXV0IGZhY3RzIDogQXJyYXkgRXhwciA6PSAjW3R5cGVdCiAgICBsZXQgbXV0IGJhbGFuY2VkIDo9IHRydWUKICAgIGZvciBfIGluIFs6Nl0gZG8KICAgICAgbGV0IG11dCBuZXh0IDogQXJyYXkgRXhwciA6PSAjW10KICAgICAgZm9yIG9yaWdpbmFsIGluIGZhY3RzIGRvCiAgICAgICAgbGV0IHRlcm0gOj0gb3JpZ2luYWwuY29uc3VtZU1EYXRhCiAgICAgICAgaWYgdGVybS5pc0FwcE9mQXJpdHkgYGBBbmQgMiB0aGVuCiAgICAgICAgICBsZXQgYXJncyA6PSB0ZXJtLmdldEFwcEFyZ3MKICAgICAgICAgIG5leHQgOj0gbmV4dC5wdXNoIGFyZ3NbMF0hCiAgICAgICAgICBuZXh0IDo9IG5leHQucHVzaCBhcmdzWzFdIQogICAgICAgIGVsc2UKICAgICAgICAgIGJhbGFuY2VkIDo9IGZhbHNlCiAgICAgIGZhY3RzIDo9IG5leHQKICAgIGJhbGFuY2VkIDo9IGJhbGFuY2VkICYmIGZhY3RzLnNpemUgPT0gNjQKICAgIGxldCBtdXQgYmxvY2tPSyA6PSBpc1ByaXZhdGVOYW1lIG5hbWUgJiYgaXNUaGVvcmVtICYmCiAgICAgICFpbmZvLmlzVW5zYWZlICYmICFpbmZvLmlzUGFydGlhbCAmJiAhaW5mby5pc0F4aW9tICYmCiAgICAgICF0eXBlLmhhc0ZWYXIgJiYgIXR5cGUuaGFzTVZhciAmJiBiYWxhbmNlZAogICAgbGV0IG11dCBpbmRpY2VzIDogQXJyYXkgTmF0IDo9ICNbXQogICAgbGV0IG11dCBmYWN0UmVjb3JkcyA6IEFycmF5IEpzb24gOj0gI1tdCiAgICBmb3Igb3JpZ2luYWxGYWN0IGluIGZhY3RzIGRvCiAgICAgIGxldCBmYWN0IDo9IG9yaWdpbmFsRmFjdC5jb25zdW1lTURhdGEKICAgICAgbGV0IG11dCBmYWN0T0sgOj0gZmFsc2UKICAgICAgbGV0IG11dCBpbmRleCA6IE9wdGlvbiBOYXQgOj0gbm9uZQogICAgICBsZXQgbXV0IGdyaWQgOiBPcHRpb24gTmF0IDo9IG5vbmUKICAgICAgbGV0IG11dCBjb21wbGV0ZWQgOiBPcHRpb24gTmF0IDo9IG5vbmUKICAgICAgbGV0IG11dCB2YWx1ZXMgOiBBcnJheSAoT3B0aW9uIEludCkgOj0gI1tdCiAgICAgIGlmIGZhY3QuaXNBcHBPZkFyaXR5IGBgRXEgMyB0aGVuCiAgICAgICAgbGV0IGVxdWFsaXR5IDo9IGZhY3QuZ2V0QXBwQXJncwogICAgICAgIGxldCBjYXJyaWVyIDo9IGVxdWFsaXR5WzBdIS5jb25zdW1lTURhdGEKICAgICAgICBsZXQgbGhzIDo9IGVxdWFsaXR5WzFdIS5jb25zdW1lTURhdGEKICAgICAgICBsZXQgcmhzIDo9IGVxdWFsaXR5WzJdIS5jb25zdW1lTURhdGEKICAgICAgICBpZiAoY2Fycmllci5pc0NvbnN0T2YgYWxpYXNOYW1lIHx8IGNhcnJpZXIuaXNDb25zdE9mIG5vZGVOYW1lKSAmJgogICAgICAgICAgICBsaHMuaXNBcHBPZkFyaXR5IHNvdXJjZU5hbWUgMyAmJiByaHMuaXNBcHBPZkFyaXR5IGN0b3JOYW1lIDQgdGhlbgogICAgICAgICAgbGV0IHNvdXJjZUFyZ3MgOj0gbGhzLmdldEFwcEFyZ3MKICAgICAgICAgIGdyaWQgOj0gYXNOYXQ/IHNvdXJjZUFyZ3NbMF0hCiAgICAgICAgICBjb21wbGV0ZWQgOj0gYXNOYXQ/IHNvdXJjZUFyZ3NbMV0hCiAgICAgICAgICBpbmRleCA6PSBhc05hdD8gc291cmNlQXJnc1syXSEKICAgICAgICAgIHZhbHVlcyA6PSByaHMuZ2V0QXBwQXJncy5tYXAgYXNJbnQ/CiAgICAgICAgICBmYWN0T0sgOj0gZ3JpZCA9PSBzb21lIDE2Mzg0ICYmIGluZGV4LmlzU29tZSAmJgogICAgICAgICAgICBjb21wbGV0ZWQgPT0gaW5kZXggJiYgdmFsdWVzLmFsbCBPcHRpb24uaXNTb21lCiAgICAgIGlmIGxldCBzb21lIGkgOj0gaW5kZXggdGhlbiBpbmRpY2VzIDo9IGluZGljZXMucHVzaCBpCiAgICAgIGJsb2NrT0sgOj0gYmxvY2tPSyAmJiBmYWN0T0sKICAgICAgLS0gRGVjaW1hbCBzdHJpbmdzIHByZXNlcnZlIHRoZSBleGFjdCBRODAgaW50ZWdlcnMgaW4gSlNPTiBjb25zdW1lcnMuCiAgICAgIGxldCBkZWNpbWFsVmFsdWVzIDo9IHZhbHVlcy5tYXAgZnVuIHZhbHVlID0+IHZhbHVlLm1hcCB0b1N0cmluZwogICAgICBmYWN0UmVjb3JkcyA6PSBmYWN0UmVjb3Jkcy5wdXNoIDx8IEpzb24ubWtPYmogWwogICAgICAgICgiZ3JpZCIsIHRvSnNvbiBncmlkKSwgKCJjb21wbGV0ZWQiLCB0b0pzb24gY29tcGxldGVkKSwgKCJpbmRleCIsIHRvSnNvbiBpbmRleCksCiAgICAgICAgKCJmb3VyX2ludF9ub3JtYWxfZm9ybV9kZWNpbWFsIiwgdG9Kc29uIGRlY2ltYWxWYWx1ZXMpLAogICAgICAgICgiZXhhY3Rfc291cmNlX25vZGVfZXF1YWxpdHkiLCB0b0pzb24gZmFjdE9LKV0KICAgIGxldCBmaXJzdCA6PSAoaW5kaWNlc1swXT8pLmdldEQgMAogICAgbGV0IGV4cGVjdGVkIDo9IChMaXN0LnJhbmdlIDY0KS50b0FycmF5Lm1hcCBmdW4gaSA9PiBmaXJzdCArIGkKICAgIGxldCBhbGlnbmVkIDo9IGRlY2lkZSAoMzI3Njkg4omkIGZpcnN0IOKIpyBmaXJzdCDiiaQgMTYzNzc3KSAmJgogICAgICAoZmlyc3QgLSAzMjc2OSkgJSA2NCA9PSAwCiAgICBibG9ja09LIDo9IGJsb2NrT0sgJiYgYWxpZ25lZCAmJiBpbmRpY2VzID09IGV4cGVjdGVkCiAgICBhbGxPSyA6PSBhbGxPSyAmJiBibG9ja09LCiAgICBhbGxJbmRpY2VzIDo9IGFsbEluZGljZXMgKysgaW5kaWNlcwogICAgbGV0IG5vZGVzIDo9IGluZm8udHlwZS5zaXplV2l0aG91dFNoYXJpbmcKICAgIHRvdGFsVHlwZU5vZGVzIDo9IHRvdGFsVHlwZU5vZGVzICsgbm9kZXMKICAgIGxldCByZWNvcmQgOj0gSnNvbi5ta09iaiBbCiAgICAgICgibmFtZSIsIHRvSnNvbiBuYW1lLnRvU3RyaW5nKSwgKCJwcml2YXRlIiwgdG9Kc29uIChpc1ByaXZhdGVOYW1lIG5hbWUpKSwKICAgICAgKCJ0aGVvcmVtIiwgdG9Kc29uIGlzVGhlb3JlbSksICgidW5zYWZlIiwgdG9Kc29uIGluZm8uaXNVbnNhZmUpLAogICAgICAoInBhcnRpYWwiLCB0b0pzb24gaW5mby5pc1BhcnRpYWwpLCAoImF4aW9tIiwgdG9Kc29uIGluZm8uaXNBeGlvbSksCiAgICAgICgiYmFsYW5jZWRfYW5kX2RlcHRoIiwgdG9Kc29uICg2IDogTmF0KSksCiAgICAgICgic2l4dHlfZm91cl9mYWN0X2JhbGFuY2VkX2FuZCIsIHRvSnNvbiBiYWxhbmNlZCksCiAgICAgICgiZmFjdF9jb3VudCIsIHRvSnNvbiBmYWN0cy5zaXplKSwgKCJpbmRpY2VzIiwgdG9Kc29uIGluZGljZXMpLCAoImZhY3RzIiwgdG9Kc29uIGZhY3RSZWNvcmRzKSwKICAgICAgKCJ0eXBlX2V4cHJfbm9kZXNfd2l0aG91dF9zaGFyaW5nIiwgdG9Kc29uIG5vZGVzKSwKICAgICAgKCJzaGFwZV9jaGVja3NfcGFzc2VkIiwgdG9Kc29uIGJsb2NrT0spXQogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X1E4MF9CTE9DSyB7cmVjb3JkLmNvbXByZXNzfSIKICBhbGxPSyA6PSBhbGxPSyAmJgogICAgYWxsSW5kaWNlcy5xc29ydCAowrcgPCDCtykgPT0gKExpc3QucmFuZ2UgMTMxMDcyKS50b0FycmF5Lm1hcCAoZnVuIGkgPT4gMzI3NjkgKyBpKQogIGxldCBzdW1tYXJ5IDo9IEpzb24ubWtPYmogWwogICAgKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksICgiZGlhZ25vc3RpY19vbmx5IiwgdG9Kc29uIHRydWUpLAogICAgKCJwdWJsaWNfZW50cnlfbmFtZSIsIHRvSnNvbiBlbnRyeU5hbWUudG9TdHJpbmcpLCAoInB1YmxpY19lbnRyeV9jaGVja3NfcGFzc2VkIiwgdG9Kc29uIGVudHJ5T0spLAogICAgKCJub2RlX2FsaWFzX2RpcmVjdGx5X2VxdWFsc19oaXN0b3JpY19ub2RlIiwgdG9Kc29uIGFsaWFzSXNEaXJlY3QpLAogICAgKCJvd25lZF9ibG9ja19jb3VudCIsIHRvSnNvbiBibG9ja3Muc2l6ZSksICgidG90YWxfZmFjdF9jb3VudCIsIHRvSnNvbiBhbGxJbmRpY2VzLnNpemUpLAogICAgKCJ0b3RhbF90eXBlX2V4cHJfbm9kZXNfd2l0aG91dF9zaGFyaW5nIiwgdG9Kc29uIHRvdGFsVHlwZU5vZGVzKSwKICAgICgiaW5kaWNlcyIsIHRvSnNvbiBhbGxJbmRpY2VzKSwgKCJzaGFwZV9jaGVja3NfcGFzc2VkIiwgdG9Kc29uIGFsbE9LKSwKICAgICgiUDJfYWNjZXB0YW5jZV9jcmVkaXQiLCB0b0pzb24gZmFsc2UpXQogIGxpZnRJTyA8fCBJTy5wcmludGxuIHMhIlAyNF9RODBfQkxPQ0tfU1VNTUFSWSB7c3VtbWFyeS5jb21wcmVzc30iCiAgdW5sZXNzIGFsbE9LIGRvCiAgICB0aHJvd0Vycm9yICJRODAgYmxvY2sgc2hhcGUgZGlhZ25vc3RpY3MgZmFpbGVkIgo=", validate=True)

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
flags = ["-t0", "-j1", "-M11264", "-DwarningAsError=true",
         "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
result = {
    "diagnostic_only": True, "compile_credit": False, "kernel_credit": False,
    "acceptance_credit": False, "finite_A_credit": False, "full_owned_audit_credit": False,
    "scope": "independent replay and complete owned audit of the successful first-131072 original-Q80 diagnostic module only",
    "target_module": target, "source_attempt": str(old),
    "source_sha256": EXPECTED_SOURCE_SHA256,
    "source_object_sha256": before["source_attempt_files"]["Blocks.olean"],
    "source_object_bytes": (old / "Blocks.olean").stat().st_size,
    "source_bytes": (old / "Blocks.lean").stat().st_size,
    "successful_compilation_task": "fa34b07b43b443c38d4ab199956d9443",
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

def run_stage(stage, command, timeout=3000):
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
    require(len(blocks) == 2048 and summaries[0].get("owned_block_count") == 2048 and
            summaries[0].get("shape_checks_passed") is True, "Incorrect block inventory/shape")
    require(summaries[0].get("public_entry_checks_passed") is True and
            summaries[0].get("node_alias_directly_equals_historic_node") is True and
            summaries[0].get("total_fact_count") == 131072,
            "Incorrect public entry/carrier/total fact count")
    require(sorted(summaries[0].get("indices", [])) == list(range(32769, 163841)),
            "Q80 block indices do not cover the exact original first-131072 prefix")
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
