# Original P2 owner cache byte transport

This route transports existing compiled bytes needed by the four original
owners and the Full87 bridge. It does not compile Lean, load an object, run a
kernel, qualify a cache, or establish a theorem. The user's private compilation
environment remains responsible for those steps.

## Existing work and the current transport boundary

The existing object artifact is still available. The GitHub connector rejects
its size because it exceeds 512 MiB, and the private workspace's existing `gh`
installation currently has no authenticated GitHub read session. This is a
transport problem, not absence of earlier proofs or compiled work.

| Original field | Fixed value |
|---|---|
| Repository | `UyNewNas/goldbach-formalization` |
| Run / attempt | `42753193835` / `1` |
| Producer commit | `cdc81d65ea82bd35ccc2ea19f916f65d84b7a3a1` |
| Artifact | `13749339878` |
| Artifact bytes | `3370363988` |
| Artifact SHA256 | `c506ac0c034e971c5554802a4e551762f122a42d25701b07a5a6c4c6471d4b7b` |
| Original checkpoint bytes | `67075207` |
| Original checkpoint SHA256 | `aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a` |
| Fixed native commit | `09b97db5764ade1246bfb77206baa1b124760958` |
| Fixed Mathlib commit | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| Fixed LeanArchitect commit | `78dd66840d3efe8c824c699fc03381cec817c271` |

The original small evidence artifact `13749294924` was downloaded and its
SHA256 verified as
`62279b4ccddb67d50ab458978900177f3e08638fb4fd7bab32008e19b9911d5d`.
It binds the large artifact and checkpoint identities above. Its original
runtime audit passed; its full target build failed and its proof acceptance is
false. Those statuses are retained.

`owner_native_cache_discovery.json` records the scoped search for existing small
carriers. It reuses the earlier 329-artifact survey, checks the latest artifacts
of 18 workflows from the 62 runs on November 23–24, and includes four freshly
downloaded small ZIP inventories. Each of those four contains 22 evidence
files and no object or nested object archive. The existing original102 and
Weil carriers have different finite source scopes. They do not contain this
required native cache.

## Request and scope

`inspect_winner9_owner_native.py` is the separate read-only source census. Its
SHA256 is fixed at
`9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d`.
It checks the matching four refactors and eleven definition cores, then reads
the actual import closure and the clean pinned native checkouts. It records
the SHA256 and Git blob identity of each source. This file has not been changed
by the cache-carrier implementation.

`winner9_native_cache_request.json` initially has status
`PENDING_ACTUAL_SOURCE_CENSUS`. It contains the known 21 direct native entry
points but no fabricated transitive selection. The workflow rejects this
status before downloading anything. Once the actual private census has
completed, prepare a new request with:

```sh
python3 verification/part2/repack_winner9_native_cache.py request \
  --census /absolute/path/to/owner-native-source-census.json \
  --template verification/part2/winner9_native_cache_request.json \
  --out /absolute/path/to/winner9-native-cache-request.final.json
```

The final request must be reviewed and installed at the committed request path.
The generator does not overwrite the old request. The completed request binds
the full source-census digest, the exact 247 project sources, all actually
needed native sources, and every locked package revision. Its import graph
must be closed and reachable from the four owners and bridge. Native sources
can include the necessary `MathlibNt`, `AnalyticNumberTheory`,
`PrimeNumberTheoremAnd`, and `Architect` dependencies. No `Goldbach` final
theorem or unrelated project module is admitted by the module-prefix policy.

Project cache candidates are included to preserve existing required work from
the original T01 package. Their source bytes must exactly match the current
census. Moved owners and changed source files therefore fail the source-match
selection. Equal source bytes alone do not qualify an object: changed imports
remain a separate mandatory check in the private environment.

## Original record formats and selection

Native candidates come from the unchanged checkpoint's
`all_guarded_package_compilations` collection. Project candidates come from
its `modules` collection. The export manifest retains each original collection
and row index, guarded commands, source/setup/facet records, import-map hash,
and classification. The complete original checkpoint is carried with its
original bytes rather than rewritten into a new historical receipt.

The usual original candidate classifications are:

- Native: `PACKAGE_COMPILE_CHECKPOINT_REQUIRES_VERIFIED_REBIND`.
- Project: `COMPILED_CHECKPOINT_ONLY_NOT_KERNEL_ACCEPTANCE`.

Other quarantined rows are listed as omitted. The one known
`Architect.Command` leaf can be carried with its original
`PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED` classification and an explicit
`separate_architect_leaf_qualification_required` flag. The carrier does not
apply or waive the separate original leaf rule. Its later qualification must
retain that boundary.

The script verifies the whole original archive SHA256 before and after
selection. It checks the exact checkpoint SHA256, original producer, locked
packages, every selected source's Git blob and import list, and every copied
payload's original member name, byte length, ZIP CRC, and SHA256. Selected
source/setup/trace/output records must agree with the checkpoint's global
file table. The source and all copied payloads remain unmodified. Compiled
system-native executable facets such as `.so`, `.a`, and `.o` are not carried.

## Packet format

Each inner ZIP is at most 399 MiB, leaving one MiB for the upload action's
single-file outer ZIP. Each upload is a separate artifact. The fixed workflow
has ten packet slots; the script rejects an export needing more slots.

`part-000.zip` contains:

- `CHECKPOINT.json`: the complete byte-exact original 67 MB checkpoint.
- `REQUEST.json`: the exact finalized request.
- `ORIGINAL_ARTIFACT_METADATA.json`: the normal authenticated GitHub response.
- `EXPORT_MANIFEST.json`: the finite selection, omissions, original statuses,
  payload-packet hashes, and explicit zero compile/kernel/cache credit.

`part-001.zip` and subsequent packets contain a `PACKET_INDEX.json` and a
deduplicated subset of unchanged original `objects/<sha256>` members. Source,
setup, trace, and portable output facets are original content-addressed
payloads. Their original installation paths remain in the original receipt;
the carrier does not install or rebase them. `SUMMARY.json` lists every packet
digest and is retained as a separate small artifact.

## Workflow and private-workspace transfer

The new `.github/workflows/p2-native-cache-repack.yml` reacts only to relevant
changes on `work/p2-formal-proof`. It uses the existing pinned checkout and
upload actions, `contents: read` and `actions: read`, a separate concurrency
group, no cancellation, and a 30-minute timeout. It uses the normal
`GITHUB_TOKEN` with `gh api` to read the one fixed artifact. It installs no
toolchain and has no Lean, Lake, native compiler, kernel, object-load, or cache
admission step. Existing CI files are unchanged.

For each small resulting artifact, the GitHub connector's
`download_workflow_artifact` returns
`structuredContent.file_uri.download_url`, along with `file_id`, `file_name`,
and `mime_type`. The returned HTTPS address exposes the original ZIP bytes for
a limited time and needs no GitHub authentication header. Normal HTTPS reads
of this field were tested locally on the small evidence archives. A private
workspace HTTPS read remains a separate transport check before relying on it
for large packets.

The owner can stream each returned URL directly into a new isolated
`/workspace` directory with `urllib.request.urlopen` and
`shutil.copyfileobj`, then verify the GitHub artifact digest and the nested
packet digest. The URL belongs only in the private transfer request, never in
a published source file or log. An expired file URL can be refreshed through
the same normal connector operation. Object bytes need not be encoded into
shell commands.

## Remaining acceptance boundary

Successful transport does not permit automatic adoption by the current
project-only private runner. The private restoration must verify the original
physical import parts, exact current source and object identities, and pinned
runtime. It must retain the original quarantine distinction and produce a
recursive native dependency signature plus a frozen source/object snapshot.
The owner compatibility compilation must bind that snapshot and its actual
Lean import roots before and after compilation. Historical project objects
without this native context binding cannot receive new compatibility credit
merely because their source hash matches.

The synthetic test suite exercises source mismatch, payload tampering,
conflicting original receipts, scope exclusion, quarantine preservation,
bounded packet/path failures, pending requests, changed artifact metadata, and
a byte-exact export round trip with zero proof credit:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 verification/part2/test_repack_winner9_native_cache.py
```

These are tests of the transport helper. They are not execution of the real
artifact export and do not change P2's mathematical completion status.
