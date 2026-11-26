# CachedRun recursion repair evidence

Base production source is 6e616f4e0372555f7a78bcdba3e198d0e277eec8.
The first direct SourceTree.rec attempt and its actual code-generation failure were already published in 7e87d9a1116d68abf8dfd35788e1db1d79a1b826.

Local draft snapshots attempt-002/003/004 were not independently submitted as full modules.
Pre-fold tasks cc40413f9b874d2da1e83d8b81c4f225 and d441d428bab541e39baa62144ec1c525 failed on the exact saved proof normalization errors.
Pre-fold task c021128ad8164bf29ba7731fb6fbe290 passed compile/replay only while deliberately retaining the two original tree recursions. It has no complete-owned credit.
Full-001 task b209a31634a94428b6ff33b214c1d523 failed because the treeFold callback needed an explicit List Bool → List Scheduled type; subsequent sorry/unused-simp diagnostics were consequences of this elaboration error, not authored sorry.
Full-002 adds exactly that type annotation. Task af16794dc5d34e17b425b4556fca60ca passed compile 10.464163s, independent replay 6.343587s, and original full owned audit 5.687911s, with all postchecks unchanged.

The complete full-002 audit is 445597 bytes and covers exactly 99 owned declarations and 151313 UTF-8 type bytes. All are safe, nonpartial, nonaxiom and depend only on allowed Classical.choice/propext/Quot.sound axioms. No _unsafe_rec remains.
The full-002 production source SHA256 is 80aab3eb9bda4146fa09ab0245a5bf93114dbf3f788175fb5ed868bfa8a330d4. Its 16 exact source substitutions invert to the original b97e7cf8d0be80ccc693db96497250223c7f3a8256726311a457c1be84ccd9b0; all 27 original theorem headers are unchanged. Eight definitions preserve the original branches, order, serial progression, failure/terminal states and fuel guard behavior.

Full tests prepend only diagnostic import TreeFoldCandidate and the SHA-bound, independently audited helper library. Their lower project modules are the existing 6e sources. Joint compilation with the other eight proposed production repairs remains to be run by the unchanged original 321 gate. Candidate pass is not a promoted canonical receipt or A/B/W acceptance.

A full-001 command was rejected by the submission API before any task existed. Its exact body and returned rejection are retained. Compressing the embedded JSON payload losslessly allowed submission with identical source, resources and checks; no Lean failure is inferred from transport rejection.
