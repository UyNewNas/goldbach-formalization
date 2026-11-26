# Independent artifact transport review

Reviewer: `/root/p36_artifact_transport_review`.
Reviewed script: `execution/transport_group_artifacts.py` in this increment.

**Final scoped verdict: passed, with no remaining blocking finding.**
Final reviewed script SHA-256:
`7652ccfee12b1496928d0ff68c28ba68929195ec1201b60f0a9cadf5aaa1c4ee`.

The review was read-only. It used temporary local bare repositories and did
not modify the transport script, invoke P1 or another cloud compiler, or push
to an external service. This record describes those independent local checks;
the controller's actual transport records establish any later P1 execution.

## Initial finding and reproduction

The initial script SHA-256 was
`43597d75a5d53f92d3d25995bf32cac25b21dd6c354b93fd2f8b492e553d0766`.
Its `read_refs` function used `git ls-remote origin`, while publication used
`git push origin`. Git can use a distinct `remote.origin.pushurl` for the
latter, including multiple push destinations.

An independent local reproduction configured the read remote with the expected
work and artifact prerequisites, then configured another bare repository as
the push URL. Publication passed its initial checks and wrote the artifact
commit to the second repository. Only the subsequent readback of the first
repository detected a mismatch and reported failure. Thus the initial guard
did not bind the external write to the destination it had checked.

A second local reproduction moved the work ref between the prerequisite
read and the artifact push. The artifact was written, then the changed work
ref was detected during readback. This established that the two ref checks
are snapshots, not an atomic lock across refs; an error after an attempted
push cannot be interpreted as proof that no external write occurred.

## Final destination-locking design

The revised script first obtains Git's resolved push destinations using
`remote get-url --push --all origin` and requires exactly one. Production
validation permits only HTTPS for the repository
`github.com/UyNewNas/goldbach-formalization`, with optional `.git` suffix and
the default HTTPS port. Other hosts, repositories, protocols, ports, query
strings and fragments are rejected.

The checked destination is stored in a temporary independent bare repository.
The prerequisite read, ordinary artifact push and readback all use the same
temporary repository and the same fixed remote. Subsequent changes to the
original repository's remote configuration do not retarget those operations.

Effective HTTP, credential and askpass settings are copied so that existing
authentication can be used. URL rewrite and include directives are not copied.
The isolated invocations remove environment `GIT_CONFIG*` injection, disable
system configuration and substitute an empty global configuration. This
prevents the checked URL from being rewritten again by repository, global or
environment settings. Both generic and URL-specific redirect settings are
excluded from the copied configuration, and HTTP redirects are explicitly
disabled.

Authentication is written only after the temporary configuration is set to
mode `0600`; the enclosing temporary directory has mode `0700`. Trace and
curl-verbose environment settings are removed, Git errors do not echo remote
diagnostics that may contain authenticated URLs, and the temporary context is
removed on exit.

The work ref checks retain their snapshot semantics. Post-push errors now
explicitly state that the artifact ref may already have changed and identify
the intended commit for recovery. The new `readback` action reads both refs
without changing them and reports the artifact and work comparisons separately.

## Independent checks of the final script

Both focused local check runs exited successfully.

| Check | Observed result |
| --- | --- |
| Production destination allowlist | Three allowed HTTPS forms passed; eight invalid targets were rejected. |
| Wrong and multiple push URLs | Rejected before yielding a usable locked transport context. |
| Two-stage URL rewrite | An original alias resolved to the permitted GitHub URL; the temporary carrier did not apply a second rewrite. |
| Global and environment configuration | Neither could change the carrier's fixed remote destination. |
| Original push URL changed after locking | The carrier's destination remained unchanged. |
| Included authentication settings | Effective HTTP, credential and askpass sentinel settings were retained without retaining include or rewrite directives. |
| Redirects | The isolated effective `http.followRedirects` value was false. |
| Temporary permissions and cleanup | Configuration mode was `0600`, directory mode was `0700`, and the carrier was removed after its context ended. |
| Read/push/readback identity | All three operations used one carrier, one destination and isolated Git configuration. |
| Five-file local Git round trip | Every recovered file matched the pinned original bytes. |
| Repeat publication | The already-published exact artifact commit was handled idempotently. |
| Work ref changed during push | The error explicitly acknowledged a possible completed artifact write and directed recovery to `readback`. |
| Read-only recovery | `readback` reported the artifact at the intended commit and the moved work ref; the local remote's refs were identical before and after the readback call. |

The earlier local checks also confirmed the fixed direct artifact parent,
preservation of all six existing tree paths, exactly five regular-file
additions, SHA-256 and byte-count verification, and refusal to replace a
same-named destination file containing different bytes.

## Verification limits

The real Git round trip used local bare repositories. Only within that test
process, the production URL validator was replaced with a check for the one
intended local repository path. The production HTTPS allowlist was tested
separately without modification. No actual P1 network authentication or GitHub
publication was tested by this reviewer.

The transport binds exact file bytes to the controller's independently captured
pins. It does not replace the group exporter's mathematical, original-run,
source, runtime, inventory or historical-lineage validation. The actual five
files must come from the successful original group and exporter, and the
recovered group must still pass the complete local evidence verifier.

The fixed work ref is checked before and after the artifact push; it is not
locked for the duration of that operation. An ambiguous push result requires
readback of the intended artifact commit before further publication decisions.
