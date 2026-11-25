# P2.10 Public Transport Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans to implement the assigned task. Preserve the file ownership below.

**Goal:** Deliver the already completed numerical certificates through the observed 512 MiB download limit without repeating proofs or bootstrap reception.

**Architecture:** A transport-only GitHub job verifies the complete original collection and emits its unchanged index and 36 block ZIPs. A receiver combines those bytes with its existing exact bootstrap, then invokes the original importer once.

**Tech Stack:** Python standard library, GitHub Actions, existing original importer.

**Spec:** `docs/superpowers/specs/2026-11-26-p210-public-transport-design.md`.

## Global Constraints

- Proof producer remains commit `94c7c507ab747cf4e05a4f19d8d4507cedfede38`, run `45611402948`, attempt 1.
- Preserve every immutable source anchor and the exact `tail.json` interface in the spec.
- No Lean compilation, stock replay, private export or repeated successful proof task.
- Preserve original C/A/E, importer and resume-plan bytes.
- Disable the original numerical push trigger before publishing new task-branch changes.
- Keep `terminal_integrated=false`; numerical transport does not close the final theorem.

## Review Focus

- Wrong source artifact bytes or producer must be rejected before delivery.
- Missing, duplicate, extra or unsafe ZIP names must be rejected.
- Index, block or omitted-bootstrap hash mismatch must be rejected.
- Existing receiving cache, receipt and registry must remain unchanged before original import.
- A queued expired URL must stop before any receiver mutation; a later failure must retain inputs.

## Task 1: Transport producer (certificate-performance agent)

**Files:** Create `verification/part2/transport_winner9_collection.py`, `verification/part2/test_transport_winner9_collection.py`, and `.github/workflows/p210-public-transport.yml`.

**Interface:** Consume the pinned public artifact and original plan; produce the exact 37 files and `tail.json` contract in the spec.

- [ ] Add small archive tests covering faithful byte transfer, wrong ZIP/index/bootstrap binding, and missing/duplicate/extra/unsafe members. Use fixture data, never rerun proof gates.
- [ ] Implement metadata/ZIP/member verification and byte-preserving delivery using only the standard library and existing `gh` access pattern.
- [ ] Add one transport-only job with read-only contents/actions permissions, pinned existing action revisions, scoped push paths, and manual dispatch. Upload only the delivery directory.
- [ ] Run focused tests, syntax/YAML checks, and report exact changed files. Do not commit or trigger a run.

## Task 2: Receiver adaptation (existing-evidence agent)

**File:** Create a V4 operational wrapper under local diagnostics, based on reviewed V3; do not change the repository importer.

**Interface:** Consume the transport artifact metadata and manifest, source index anchor, and previously verified local bootstrap; produce the exact incoming directory and original importer receipt.

- [ ] Preserve V3's early URL expiry guard, HEAD/source/plan/bootstrap-receipt/93-record checks, and exclusive staging rules.
- [ ] Verify transport provenance and all 37 files; reuse the existing tar by a verified hardlink or existing exclusive-copy helper.
- [ ] Call the original importer once. Preserve 592/6/1/0 origin accounting, 597 new accepted audits, exact 691-module cache boundary, and zero new proof credit.
- [ ] Check Bash and embedded Python syntax, report the delta and SHA, and submit no remote job.

## Task 3: Review, publication and actual reception (root plus scope reviewer)

- [ ] Review the producer and receiver deltas for the spec's invariants and public/private boundary.
- [ ] Remove only the original numerical workflow's two push-trigger lines; verify original proof inputs and job bodies are unchanged.
- [ ] Check current branch head and open PRs, then publish the transport-only commit with a compare-and-swap ref update.
- [ ] Observe only the new transport job; verify its actual artifact metadata and original source anchors.
- [ ] In an executable receiver window, obtain the smaller artifact URL and submit one receiver invocation.
- [ ] Verify actual importer/receipt output, then finalize the public acceptance report. Record any still-blocked P2 final integration honestly.
