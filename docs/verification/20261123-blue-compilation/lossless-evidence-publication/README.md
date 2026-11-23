Lossless publication of large verified evidence

Status: candidate code and isolated fixtures only, pending independent review. Production publisher60ae is unchanged. No production batch56 artifact was compressed/copied/read, no main publication/catalog update occurred, and no Lean/kernel/audit/numerical replay ran for this task. The only large inputs exercised were synthetic temporary evidence just over50MiB. Production compression ratios have not been measured.

Scope

Only exact basenames OWNED_EXPORTS.json, PUBLIC_EXPORTS.json and types-axioms.log with rawsize>50MiB become filename+'.gz'. At exactly50MiB they remain ordinary exactcopies. Sources/.lean, manifests, proofoutputs, normal/kernel logs and every other basename keep the original copy behavior and strict SHA checks. A carrier exceeding100MiB is rejected, rather than silently changing formats. Source/raw manifests/evidence are never rewritten, truncated, parsed into substitutes or deleted.

The candidate preserves the original finalizer whitelist and late stdout binding gate, source+fiveoutputs checks, acceptance/ownedcounts and sourceoverride/catalog logic. Existing sha/read/write/_require/_relative_record/_late_finalizer_record functions are byte-identical. STRUCTURAL_COMPARISON.json removes exactly7carrier changes and reconstructs the entire60ae publisher bytes. Helperbytes/SHA are pinned inside the candidate. Root must adopt both candidate and its sibling restore_lossless_evidence.py together after review, not just the publisher. The production publisher path remains untouched by this packet.

Carrier identities and repository layout

GzipFile uses filename='',mtime=0,compresslevel9. Originalbytes are hashed/count-checked while streaming; the gzip writer is closed, then gzip is independently decoded in boundedchunks and the originalbytecount/SHA and CRC are checked before the carrier is atomically installed. Existing identical valid carriers are retained, differing/corrupt carriers reject, and an existing large raw destination is refused without deletion. No source preimage/evidence record is replaced with a carrier hash.

Original PUBLICATION_FILES.json remains byteexact and still lists RAW identities. Those3raw files are NOT claimed to exist at their original Git repository paths. LOSSLESS_ARTIFACTS.json maps each rawrelativepath/count/SHA to the actual.gz path/count/SHA, and includes the exact recoveryhelper identity. PUBLICATION_INTEGRITY.json retains the raw inventory but explicitly marks that raw paths require restoration and records the actual Git files (smallcopies, carriers, losslessledger and recoveryhelper). There is no new proof or theorem credit from this representation change.

Recovery

The publisher copies the small standalone restore_lossless_evidence.py into the published batch directory. From a clean Git checkout, for example:

    python3 docs/verification/20261123-blue-compilation/member-repair-batch56/restore_lossless_evidence.py --manifest docs/verification/20261123-blue-compilation/member-repair-batch56/LOSSLESS_ARTIFACTS.json --output-dir /tmp/NEW-batch56-raw-evidence --max-total-bytes 2147483648

This restores ONLY the compressed raw evidence, at originalrelativepaths under a NEW directory. Other smallsource/evidence files remain in the checked-out batch directory; a complete rawpacket may be assembled in another new directory using those unchanged files plus the recoveredraw paths. The helper does not implement a general project materializer or run formaltools. The original raw manifest becomes verifiable against that assembled rawlayout, not against the Gitdirectory containing.gz carriers alone.

Recovery validates both compressed and decompressed size/SHA, the exactwhitelist/mapping/header and gzipCRC. It rejects traversal/noncanonical/absolute paths, unsupportednames/small-carrier claims, duplicateoutputs, existingoutputdirectories/files, symlinkfiles/parents and nonregularinputs. Directory/file operations use pinned dirfds,O_NOFOLLOW and exclusive atomiclinks; no clobber is allowed. Decompressedreads stop at declaredexpectedbytes+1; declaredaggregate must fit --max-total-bytes (default2GiB). Carrierinput is bounded to100MiB and mappingmetadata to1MiB. Partial invalid outputfiles are never installed. An optionalbackup or specialformattable is not inferred or recomputed.

Executed isolated validation

The preserved initial fixture failed against baseline for missingcarrier support (FIXTURES_RED.log), then its roundtrip passed. The final suite ran71tests, allPASS:33synthetic carrier/restoration tests plus38unchanged original late-finalizer fixtures with only their SCRIPTconstant pointing to this isolated candidate. The synthetic rawfile is slightly>50MiB; no production payload is used. Coverage includes deterministicroundtrip/header, both size/hash layers, corruptCRC/truncatedgzip, wrongrawhash/expectedcount, output/metadata/streamlimits, escapes/symlinks/FIFO/existingpaths/collisions, unsupportednames, retainedidenticalcarrier, smallcopies and strictoriginalrawhash/late semantics.

To repeat only these isolated tests:

    python3 -m unittest discover -s /workspace/p1-complete-proof/lossless-large-evidence-publication -p 'test_*.py' -v

This does not invoke publisher.main. Production invocation is intentionally not part of these fixtures and must wait for rootreview and the authorized publication step. No productioncompression-size claim or newLean acceptance is supplied here.
