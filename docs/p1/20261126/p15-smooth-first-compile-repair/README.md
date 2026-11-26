# SmoothLicence first-compilation repair and original U acceptances

The original U commit is `2779eb7b2b0433bea10d523ef976317893f8429d`.
The manuscript remains frozen at 1106. Whole P1.5 is not complete.

## Actual compiler results

| Owner | Original task and run | Normal / kernel | Owned / public |
| --- | --- | --- | --- |
| WordDictionary | `job_9eeb0db5123a4283ad6a18864bdc342b`, U run 0 | 0 / 0; original final stock 0 | 15 / 15 |
| AllGroupHBDiscrepancy | `job_78ea387bf32d4c57b60346dcf7451e50`, U run 1 | 0 / 0 | 15 / 15 |

The U run 1 batch reused Word, accepted AllGroup, then failed at SmoothLicence's
first normal compilation. Seven following targets were not started. That batch
remains a partial failure without a final stock check. AllGroup's own normal and
full-owned kernel acceptance remains valid; Word retains its first run identity.

`collect_u_acceptance.py` actually ran as `job_8f2104e8832b46fe900bfa3b5c829886`
and exited 0. It revalidated the unchanged U reader, both original run records,
all six owner receipts, source plus five outputs, and all 21 artifact slots.
Its joint current read is 139 sources / 137 preserved dependencies. The two
owner closures are 77 and 139; the original run scopes are 77 and 157.
No compiler or stock command was rerun for an accepted owner.

## Narrow proof repair

The canonical SmoothLicence source changes only five recorded proof spans:
pointwise reduction in two negative-N branches, the current iff API for
`Real.contDiffAt_log`, the field-notation newline, and explicit types/constants
for the original local smooth product. Nine declaration headers, all imports,
and every theorem assumption are unchanged. No axiom, sorry, admit, unsafe,
or native-decision shortcut is introduced.

The first no-output probe (`job_df9b16a8ee92404a8e55403d318ae8f1`) exposed the
unconstrained local `have` placeholders. Its failure record is retained.
The final whole-module probe (`job_73a4c21270084d40b7e5c0ed397bdea4`) exited 0.
It used the original serializer and guard with `lake --no-build env lean`,
requested no output object, and preserved all 360 source slots, 160 modules'
3360 artifact slots, the U/S/Q evidence trees, runtime and Git state.
This probe is not a normal/kernel acceptance.

The following entrypoint publication must bind this repair as its source anchor,
retain the two original U owners as historical priors, archive the exact failed
SmoothLicence setup before removal, and install only the recorded source change.
The original eight prior identities and the 19 P3 dependency holds remain.

## Proof boundary

The native two-long bridge published with this repair is source-only. Its static
review does not give Lean or kernel acceptance and does not close the Fourier
integral, tail, or outer atlas obligations. The exact original FixedM source and
the P3 receiver acceptance boundary remain unresolved. No complete P1.5 claim is
made, and closed Draft PR #10 is not extended.
