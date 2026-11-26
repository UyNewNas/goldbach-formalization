# P2 Round 4 Resume Implementation Plan

> **For agentic workers:** Use the approved delegated implementation approach. The coordinator reviews this package before installing the sources or running the wrapper.

**Goal:** Resume the existing P2 analytic checks with eight reviewed source repairs and the current qualified cache.

**Architecture:** A small wrapper imports the exact original round-2 helpers without calling their main function. The unchanged compile and audit drivers retain responsibility for source, dependency, object, toolchain and external-context qualification. Historical repairs are reused as source bytes; their old objects are not imported.

**Tech stack:** Python standard library and existing pinned Lean verification drivers.

**Spec:** The coordinator's approved design and `SOURCE_SELECTION.json` in this package.

## Global constraints

- Keep the same five roots, 377 source modules, 69 audit targets and original gate hashes.
- Preserve the 325 normal successes and 38 accepted owned audits as historical inputs; only the drivers decide which remain reusable.
- Keep one worker, one thread, 11264 MiB Lean heap, the 1400-second compile budget and the original 1 GiB disk minimum.
- Preserve the prior attempts, exact round-3 result, original records and audit summary before the new checkout.
- Change exactly the selected eight source hashes, with unchanged import lists. Only four selected modules belong to the unchanged 69-target audit scope.
- Run no cloud job and change no production source while preparing this package.

## Review focus

Scope drift must fail before compilation. A source or import mismatch must fail before compilation. An existing attempt directory or audit-summary basename must never be overwritten. Old historical receipts must retain their source origin. Full acceptance still requires 377 successful modules and 69 accepted audits.

## Implementation

- [x] Review all eight complete original failure logs and bind them to recorded source hashes.
- [x] Select the four exact historical compiled repairs and the four existing draft repairs, completing only the unused-simp removals newly visible in the H5/H7 log.
- [x] Add focused tests for graph scope, source/import identity, audit ordering and previous-result counts; observe missing-wrapper failures.
- [x] Create `docs/verification/20261126-p2-5-resumed/run_p2_round4.py` with pure validation functions and a sequential resume main.
- [x] Run the focused tests and Python syntax checks. Inspect the complete patch and preserve all original driver bytes.
- [ ] Hand the package and wrapper to the coordinator for independent review, installation, cloud execution and publication.

The wrapper is not a replacement audit implementation. Its only acceptance predicate is the original helper's predicate plus preserved source, gate, external-context, checkout and historical-file checks. `P2_5_proved` remains false.
