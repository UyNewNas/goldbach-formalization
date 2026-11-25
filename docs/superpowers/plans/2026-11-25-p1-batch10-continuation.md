# P1 Batch10 continuation implementation plan

> **For agentic workers:** Execute the existing P1 continuation; use the existing source partition and acceptance machinery. User authorization includes implementation and GitHub publication. Do not pause for another design approval.

**Goal:** Resume the already published P1 dependencies from `99c1f8ba1dc453b21f47e30b667db0de93d73387` without repeating accepted work or confusing source publication with proof acceptance.

**Architecture:** Preserve the 22 ordinary source repairs/donors and the 53 Higher compilation units. Add only the missing source-gated continuation driver around existing guards, lane serializer and full-owned acceptance runner. Never replace the original four terminal theorem contracts.

**Tech stack:** Python standard library; existing Lean `v4.33.0-rc1` cloud project; pinned Mathlib and existing cloud receipts.

**Spec:** `docs/p1/20261124/batch10-source-update/SOURCE_UPDATE.json`, `docs/p1/20261124/batch10-higher-partition/COMPILE_PLAN.json`, and their READMEs.

## Global constraints

- Follow the 20261106 manuscript, pinned at `a988cba584d803ae2856a0de50efb582f4f3dd6a`.
- Reuse accepted results before scheduling new work; the newest accepted batch has 12 modules and 426 owned declarations, not a whole-project total.
- Use P1 Private Compiler 32GB `6b053c6d`, project `/workspace/blue-member-build` and its original runtime guards. Preserve its dirty source repository.
- Do not change Lean sources, theorem statements, assumptions, constants, compiler limits, accepted checkers, or completed receipts for this orchestration change.
- Higher order: Core, then the 51 proof units, then the original facade. No cold parallel dependency fan-out.
- Higher acceptance must include all 53 owners. Probe receipts cannot be reassigned to the new owners.
- A normal build, a generated audit plan, a Python test, and a static hash comparison are distinct from normal/kernel/full-owned Lean acceptance.
- Do not turn the four original terminal files green until their actual dependency closure and original statements pass the required checks. Their theorem explicitly leaves the compiled density and signed-PP obligations separate.

## Review focus

- Unknown cloud source or mismatched payload: reject before any project source write.
- New Higher providers: actual absence and exact existing postimage are the only allowed starting states.
- Interrupted execution: preserve completed normal receipts, do not silently repeat them, and do not trust changed dependency or output fingerprints.
- Resource isolation: use the existing serializer and explicit single-module build targets; never infer one proof's peak memory from a two-lane job peak.
- Audit scope: invoke only populated lanes and retain complete owner inventories, including private and generated declarations.

## Task 1: Add the missing Batch10 continuation

**Files:** Add the driver, focused tests and usage notes under `docs/p1/20261125/batch10-resume/`. Read the pinned older helpers; do not edit them.

**Interfaces:** Consume the published ordinary and Higher manifests, exact source bytes, and existing cloud source/artifact state. Produce immutable execution receipts, exact normal logs and a pending or executed acceptance plan using the unchanged acceptance runner.

- [ ] Write focused tests for preimage rejection, absent providers, exact-postimage no-ops, interrupted normal reuse, and sequential Higher order; observe their failure before implementation.
- [ ] Implement read-only preflight and guarded installation. Adapt the ordinary manifest schema in the caller and handle new provider creation separately.
- [ ] Implement sequential explicit-target normal execution with trustworthy resume and distinguish all result states.
- [ ] Reuse the original full-owned audit runner or generate its exact pending plan from actual normal evidence; never fabricate successful compiler results.
- [ ] Run local Python tests, actual published-source checks and `git diff --check`.
- [ ] Obtain independent code review, fix material findings and publish the continuation commit.

## Task 2: Execute on the specified compiler when reachable

- [ ] Read fresh cloud state and current source hashes before applying updates.
- [ ] Run the new continuation on the existing cache; inspect each failure and corresponding manuscript passage before changing a proof.
- [ ] Run independent kernel and all-owned audits for successful new owners and preserve receipts.
- [ ] Continue the original terminal chain only when prerequisites are actually ready.

**Connection history:** The specified compiler initially returned HTTP 429 at the MCP probe, including for `pwd`. It recovered during this session. Fresh cloud preflight task `job_a47fc62e71774c99a87cc2f05e30c36c` exited 0: all 75 preimages match, none has a target object, and the existing audit12 receipt is unchanged. Local tests and source checks still must not be reported as Lean verification.

## Decisions

- Preserve the latest existing proofs rather than invent mathematical replacements for a recorded interpreter memory exception.
- Do not change the dashboard from its 2026-11-23 snapshot using uncompiled 2026-11-24 sources.
- Keep the pending compiler execution explicit if the external connection remains unavailable; source readiness is not P1 completion.
