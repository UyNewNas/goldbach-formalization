# Generic-M published-source extraction ledger

Authority: root's authorized candidate-only extraction task, 2026-11-23.

Specification: copy already-published generic-M proof code into one independent
extension; preserve old cap100 providers, four external suppliers, all pins,
and the original consumer's complete 4333 bytes; do not run Lean or edit live
source trees. Hand candidate and provenance to build_workflow for adoption.

Ruling: the explicitly requested independent artifact directory is the isolated
workspace. No Git worktree or live-source mutation is needed.

Ruling: verification here is static byte identity and scope checking only.
The explicit no-Lean instruction takes precedence over generic workflow advice
to run a repository suite. No compiler success will be claimed.

Pre-flight: the extension imports the existing cap100 Uniform provider. Its
published new proofs require six old private helpers, copied privately because
cross-module private aliases are unavailable. Those six are included in the
seven-private total; the seventh is the published new coarse derivative helper.

Tasks: static verifier RED; exact source extraction; static verifier GREEN;
handoff with explicit compiler/receipt limits.

Static verifier RED: exit 1, missing candidate manifest (expected).
Extraction complete: 18 contiguous published slices, no proof edits; all six old private helper slices also match current old providers.

Static verifier GREEN: PYTHONDONTWRITEBYTECODE=1 python3 verify_static.py, exit 0.
Evidence: 18 exact declaration/header/body source slices; 11public/7private; no copied proof references omitted Abel_unrestricted; old providers/external suppliers/pins unchanged; original 4333 consumer bytes retained; forbidden tokens absent.
Handoff: full manifest, overlay, source snapshots and SOURCE_REUSE.md sent to build_workflow for fresh independent static review and authorized guarded local validation. No compiler result claimed.
