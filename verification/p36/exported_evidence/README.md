# Complete exported-owned evidence verifier

The exact local verification code used for the accepted warm/common archive is
preserved here. It reads a separately pinned profile, checks every archived
payload and original command, reconstructs the original recursive import
signatures and mirror mappings, and validates the original complete owned
inventory. It does not run Lean or grant new dependency acceptance.

The captured warm/common profile and terminal/transport summaries are under
`docs/part3-distribution/continuation-20261126-p36/accepted-warm-common/validation/`.
Their original runtime paths and bytes are intentionally preserved. Reproducing
the additional transport check requires the original stdout pages from the
listed export tasks, placed beside the profile with their recorded names; those
intermediate pages are not duplicated in this repository. `decode_transport.py`
reconstructs the receipt/archive from them before `verify_and_install.py` runs.
The formal archive itself is independently pinned by its receipt and archive SHA.

The profile is a trusted, reviewed input: choose its expected source commit,
scope, hashes and counts independently of the receipt. A new project location,
formal task, scope, or transport protocol requires a new reviewed profile.
Unpacked dependency objects absent from the archive remain bound by the original
runner snapshots; the local report does not claim a new local kernel replay.
