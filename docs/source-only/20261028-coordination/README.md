# Root source coordination and compiler-owner handoff

This directory contains time-stamped working inventories and root publication receipts for the manuscript-internal 1+1.748 source work. Every original broad target remains OPEN. All new files are uncompiled source proposals; no numerical replay, kernel acceptance or formal credit is claimed.

SOURCE_BATCHES.json separates frozen published batches from local in-progress bytes. NEXT_ACTIONS.json records the thirty assigned next steps and remaining obligations, including user-owned compiler work. Per-batch frozen ROOT_ACCEPTANCE/reviews/IMPORT_MAP files are authoritative for their narrow accepted source scope. Root working inventories can be newer than the live Site; SITE_PUBLICATION.json identifies the exact deployed source commit and snapshot scope.

PUBLICATION.json records proof-bundle commits verified at the remote branch; later metadata commits may follow. Exact source bytes are preserved by batch .gitattributes and checked against SOURCE_MANIFEST.json. No production import root is changed. freeze_batch.py uses path-only commits and verifies unrelated staged state is preserved. It never invokes a compiler.

INTAKE_MANIFEST/REPORT, when present, are proposed module/source mappings only, not installation or recursive import/axiom closure receipts. Missing package bytes and ambiguous targets must remain explicit for the compiler owner.
