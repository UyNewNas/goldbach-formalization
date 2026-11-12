This independent metadata erratum corrects two verified interfaces in the frozen source-selection proposal. Original Finev2, ca9d96ce and the frozen source/proof packets are unchanged. No materializer, stage, prepare or Lean/proof command ran.

The actual Finev2 materialize_record checks `get_origin(pre_input['origin'])` before applying a transform. The proposed72 Stored replacements lacked that nested origin. Each corrected pre_input now carries the corresponding original Fine source origin verbatim, alongside its exact original size/SHA/blob. All selected source/postimage/transform bytes are unchanged. This fixes the identified input lookup; it is not a claim that a complete successor driver is implemented or stage-tested.

The original proposal also copied Fine's old target record, including efca98's original source identity, followed by eight target-name strings. The corrected file has nine records with a uniform schema: primary_module, closure_modules, external_imports, unresolved_modules, source_identity_sha256 and source_and_git_blob_identity_sha256. Each closure was independently traversed through the actual selected imports, with missing sources/cycles rejected.

The compatible pair identity is SHA256 of UTF8 compact `json.dumps([[module,sha256] for module in sorted(actual_closure)],ensure_ascii=True,separators=(',',':'))`, without a trailing newline. Triple identities use exactly the same recipe with git_blob_sha1 as the third field. The historical efca98 value occurs only under explicitly historical metadata, never as an actual successor target identity.

| Actual scope | Project modules | Pair identity |
|---|---:|---|
| Fine after72 Stored reselections | 1808 | cbfab9b665a35824f1215eb96a19d0dcf4490471d8a462c0147c309191a27b71 |
| Fine + winner union | 1816 | 51e527a1da586b0d1e3ca2d3954f7da807f4adf47f9f4a9412b70c7d853ed385 |

The actual Fine triple identity is643ec0de6be762f54d44c92ca78ef02b374bfcbb0980fd487673119c8de2f91b. The union's original correct triple identity41ae7de0255d269011dc70ddb23fd1ba6092f394b17bd98b9cda4d2306d3663d is retained separately. Winner target closure sizes, in module-name order, are1646/1577/1594/1641/843/1642/1644/1054; their pair/triple identities are individually bound in METADATA_DELTA and the corrected proposal.

All1816 source rows compare equal to the frozen proposal after removing only the72 newly added pre_input origins. In particular the new071 candidate bytes remain41c5a10b, unvalidated. Project/native/module counts and every proof-acceptance status are unchanged.

The existing stage program still has its original Fine-only guards and receipt convention. A future combined driver must explicitly bind the all-project union identity separately from each target's closure identity; target0 correctly describes Fine1808, not the1816 union. This erratum does not silently parameterize that runtime or make it driver-ready.
