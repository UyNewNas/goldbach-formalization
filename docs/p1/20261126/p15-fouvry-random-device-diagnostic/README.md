# Fouvry receiver: observed random-device failure, read-only boundary retained

The exact original checker requery `job_b79d9178a4cb441695d601062c52cc26` remained HOLD: the first receiver depHash query exited 134 before a valid depHash was obtained. No donor cache was adopted.

The independently reviewed diagnostic `diagnose_fouvry_random_device.py` was then executed as `job_d200653d78284b62a04f126bc02f01fd`. Its exact result is `ACTUAL_DEVICE_DIAGNOSTIC_RESULT.json`, 10,817 bytes, SHA256 `a5915dbf034f351f3900ef8e4e9edfc37a2260fb10e8ef06bf15b8cba8c24fa1`. The script did not run Lake or change any guard, serializer, source, artifact, trace, configuration or runtime.

Actual bubblewrap version: 0.12.0. Outside the original read-only namespace, `/dev/urandom` was a character device (1,9) mounted `rw,nosuid`, with `nodev=false`; a one-byte read succeeded. Inside the unchanged original namespace, the same inode/device was mounted `ro,nosuid,nodev`; opening it failed with errno 13. Both phases only report the success/length or error and discard the random byte. The original fourteen protected paths remained read-only, every non-owned mount remained read-only, and the owned temporary directory remained writable.

The dispatcher and worker independently verified equal before/after source/artifact/configuration/runtime and Git snapshots. Both recorded state SHA256 `c27b068aad8caf3e5aa90a1bb83a035a54fb191838b426589d78c7ceac25f425`.

The observed nodev mount explains the device access failure. The original checker and its failed receipts are retained. Receiver readiness and P3 cache adoption remain HOLD; the environment owner must provide a usable device/tool environment consistent with the existing read-only contract. This packet makes no new Lean acceptance or cache-equivalence claim.
