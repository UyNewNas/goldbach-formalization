# Independent review of the group evidence adapter

Reviewer: `/root/p36_group_export_review`. Reviewed source SHA-256:
`a0c69d1d95ea78029aee8fbddfb693438ceb90dbc7655e9d9c42dd3389955fb7`.
The previous exporter remained exactly
`003d628292e0b1d067e9f87d3aad6b2c6f2a64db5b117e06cbe6bbf37743fcf5`.

No blocking defect was found. Review checked the exact ordered eight-owner
manifest; source/commit/report/manifest bindings; original runtime capture;
raw base receipt and archive hashes; the preservation of all previous strict,
replay, inventory, graph, historical-lineage and unpacking checks; and the
explicit separation between the base unknown-runtime slot and outer original
group-runtime evidence. Both whole-node flags remain false.

The reviewer independently ran all five focused tests (exit 0, 5.028 seconds)
and compared runtime-tool derivation against the actual previously accepted
pair-normalized receipt and original runtime capture. All six original paths
and before/after digests agreed; changed compiler identity was rejected.

The classical-six regression fixture reuses the actual 85 declaration records,
10,125 graph nodes, 37,857 snapshots and original logs. Its inherited fixture
reconstructs missing prior-report bytes and changes conflicting legacy date
paths to 2025. Accordingly it exercises multi-owner validation and rejects a
missing replay, but does not validate all historical report bytes as originally
captured and is not a successful export/verify of the new eight-owner group.
Recovery and full local verification of that actual group remain required.

No additional legacy-report allowance was approved by this review. Any newly
encountered unpinned historical writer must still be independently identified
and separately reviewed before a narrow provenance extension can be accepted.
