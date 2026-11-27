# Classical support verification attempts

All source was authored locally. Cloud commands transferred exact local scripts
or checked out immutable published commits, then compiled and collected evidence.
The three failed attempts below accepted no new declarations.

## R1: package integrity failure before Lean

Task `job_4dcd780ba30e4a12be47e0c54ae48be9` used source
`4c213f5d6477aa30e1d4636d5c4fb9d01cf8e188`, tree
`3a5e0b7edb7132f2f7d49d596fc9b81086cbc344`. The pinned goldbach package in
`/workspace/blue-member-build/.lake/packages` referred to a missing Git alternate
object directory. Its clean-checkout check failed before Lean could run.

The exact failure archive is `environment-failure-r1.zip`, 21,439 bytes,
SHA-256 `7b966e1eacea3965f1b060709681f61096c7d4f1af10091d924944b65d9f2d16`.

The read-only diagnosis is preserved in `package-diagnostics.log`.
`verification/prepare_p34_classical_packages.py` prepared a new owned package
view using clean checkouts at the same pinned commits. It did not repair or edit
shared packages. Ten healthy package roots were linked; the package without a
built object directory, Cli, was independently cloned locally at its pinned
commit, with an empty ignored object directory. Missing imported objects would
still fail the normal import gate. `environment-preparation.json` records donor
and destination identities and their unchanged clean statuses.

## R2: providers compiled; consumer proof-expression failure

Task `job_06ec1824ecd94a2ca48dd69aee427317` used the same source and tree with
the healthy package view. It completed all 56 provider compilations, including
the strict P3.1 common Poisson core, then failed the 57th module's strict compile.
The run took 242.947 seconds and sampled a peak of 4,073,148,416 bytes.

The exact archive is `proof-expression-failure-r2.zip`, 109,995 bytes,
SHA-256 `6bc71fbd4b154117078db9c73d954156ca96125e0278b33005472f68831134bb`.
Its 170 manifest members were checked by length and SHA-256. The report records
153 stages, exactly one failed final consumer stage, 56 project object bindings,
and 67 directly imported external object bindings. The launcher completed its
final clean HEAD/tree check despite the gate failure.

The first diagnostic leaves the natural-number base of `pow_pos` underconstrained.
The second fails to close real interval inequalities by `linarith` despite the
available lower and upper bounds. The two subsequent repairs make the natural
base explicit and normalize the real casts. Their complete before/after proof
bodies are recorded in `SOURCE_INTAKE.json`; no theorem statement changed.

## Incremental continuation protocol

The new gate authenticates the fixed R2 archive, checks every prior stage log,
and rechecks the entire old source/configuration, tool, package, direct external
object and project object state. It permits reuse only for the exact 56 unchanged
provider sources and import graph. A fresh destination checkout must start with
no project objects. All imports are resolved again; each authenticated object
part is copied to a separate regular file and hashed again. The old object root
is never added as a fallback search path.

Only the repaired consumer is compiled anew. Its two-module target scope must
then pass both bundled kernel replays, boundary examples, complete owner/type/
axiom inventory, and final source/object invariants. Counts distinguish reused
and fresh compiles. The inherited set of all 67 external bindings remains in
the final check. No success is inferred from the cached providers alone.

## R3: target strict compile and both replays pass; boundary cast failure

Task `job_0d37906fca0440888dd22fbff9cbc687` verified source `fbbe02c3c7bcd821670ca3a331fbff5383691a96`, tree `bb3e3e636b19cec92c4703fbdd095ba92abadff1`. It authenticated and reused all 56 R2 provider objects, strictly compiled the repaired consumer, and completed both selected kernel replays. The boundary stage then reported a type mismatch between a natural-number one cast to the real/complex field and the literal field one. The same theorem application is retained, with `simpa only [Nat.cast_one]` replacing `exact` in the example proof. No consumer source changed.

The exact failure archive is `boundary-cast-failure-r3.zip`, 86,312 bytes, SHA-256 `0ed24f4baef0311425fafeaa096a1b2a1377823091dbe5c7ebc6201e05e2e578`. All 122 manifest members were checked. The run recorded 105 stages, took 29.314 seconds and sampled a 4,048,633,856-byte peak. It did not reach owner inventory or final acceptance. The next complete run uses the already reviewed R2 incremental protocol; only the selected consumer and acceptance stages rerun, with all 56 provider compilations still reused.

## R4: complete finite-scope acceptance

Task `job_52c313847b3f46a29ffdfe2ce49b6339` accepted source `6bafadff2427616abaa8159797b87b816af76d63`, tree `3c1c5b3d2c83a036643833e2197289e54ddbdf5f`, with all 146 stages passing. The 56 provider objects were authenticated and copied again without recompilation. The selected consumer strict compile, both target replays, the corrected boundary example, full owner inventory and final source/object checks all passed. Runtime was 240.596 seconds; sampled peak was 4,033,740,800 bytes. The complete report and original 110,278-byte archive are linked from ../ACCEPTANCE.md. Four original explicit declarations are accepted; full P3.4 remains open.
