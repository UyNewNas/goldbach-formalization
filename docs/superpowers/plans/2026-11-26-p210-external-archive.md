# P2.10 external archive implementation plan

Design: `docs/superpowers/specs/2026-11-26-p210-external-archive-design.md`.
Existing isolated branch: `codex-p210-complete-20261125`.
Base publication: `390a3669a26b8a635f3be43f3dcdff03a4bc4e95`.
Required receiver worktree (W1): `7c6fe1e249ffdbdf9b76b166022fc2236b2c69fb`.
Original numerical source: `94c7c507ab747cf4e05a4f19d8d4507cedfede38`.

This work is part of the user's existing instruction to finish P2.10 and commit
its code. It adds necessary storage support; it does not authorize new theorem
scope or repeat any successful proof.

## 1. Storage adapter

Owner: the evidence/receiver implementer.

- Add one separately pinned adapter and focused small-fixture tests.
- Require the explicit external archive mode; leave the original importer and
  its normal entry point unchanged.
- Freeze the binding schema before the final-gate consumer is implemented.
- Reuse all original validation and transfer helpers that apply.
- Preserve the full old registry, exact merged bytes, local old-registry copy,
  local original import receipt, exclusive destinations and commit-last behavior.
- Verify rollback before commit and preservation after commit, including a real
  cross-filesystem fixture where supported. Run no mathematical proof gate.
- Keep `SOURCE_COMMIT` and every numerical provenance field at the original 94
  source. Require a clean W1 `WORKTREE_COMMIT` independently; test clean W1,
  old 94 and dirty W1 without rerunning unchanged storage transaction fixtures.

## 2. Final-gate adaptation

Owner: the independent scope reviewer after the binding schema is fixed.

- Derive the next operational final-stage template from the existing v2.
- Keep the original root-only path reader and every C/A/E condition.
- Add only the pinned external binding and its single external archive reader.
- Bind both original local copies and the complete original external archive.
- Freeze all new pins until an actual successful storage receipt supplies them.
- Review changes independently of the adapter implementation.

## 3. Publication and actual reception

Owner: root.

- Review the adapter, fixtures and final-gate delta against the design.
- Publish only public source/design/tests with a branch lease and exact tree
  comparison. Check for an open PR and unintended workflow triggers.
- Obtain the published adapter by its independent commit and SHA without
  changing the fixed W1 proof worktree or original I/C/A/E/plan files. The
  original importer arguments and storage binding retain the numerical source 94.
- Use actual preparation results and both volumes' available space. Preserve
  the full public cohort and use fresh supported transport URLs at execution.
- Run original validation once and the split storage transaction once. Retain
  failure evidence; do not rerun accepted work or overwrite partial results.

## 4. Complete the original mathematical goal

Owner: root with independent evidence review.

- Reuse the accepted historical prefix, six preparation results and imported
  numerical cohort.
- Fill the final-stage pins from actual complete evidence.
- Execute only missing final compilations and their required audits/exports.
- Report the exact final mathematical statement and its original manuscript
  correspondence only after all required gates pass.
- Publish a minimal public acceptance summary. Keep private environment records
  and complete private exports local.
