# Reconstruct the unchanged main evidence archive

The 37 files `part-000.bin` through `part-036.bin` are consecutive raw byte
ranges of one xz archive. They are not separate xz streams. Their individual
hashes and immutable Git blob identifiers are in `../MAIN_ARCHIVE_PARTS.json`.

From the repository root:

```sh
cat docs/verification/20261125-p2-resume/main-evidence-parts/part-*.bin > docs/verification/20261125-p2-resume/evidence-resume-main-20261125.slim.tar.xz
sha256sum docs/verification/20261125-p2-resume/evidence-resume-main-20261125.slim.tar.xz
python3 verification/part2/repack_winner9_private_evidence.py verify docs/verification/20261125-p2-resume/evidence-resume-main-20261125.slim.tar.xz --repo .
```

The reconstructed size must be **44,304,524 bytes** and SHA256 must be
`92c1067a1694ea74af4d15ee841199ab72094f2147b7651e77cf21f60e68faf4`.
The unchanged original verifier checks the preserved members and their exact
repository source references. The original archive is a local reconstruction
target; Git publishes the parts once, rather than also storing a second copy
of the complete archive. Byte transport and verification add no Lean proof
credit.
