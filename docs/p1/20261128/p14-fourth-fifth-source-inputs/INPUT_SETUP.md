# Reuse the original fourth input

The input is already tracked at `proof-continuation-data/fourth-original/FourthRows17LE.bin`; its SHA256 is `561f5dc9ff2f6d64ba739de830511f6f68bf1f7be0c724655a8435c7edb914da` (62885159 bytes). The unchanged include reader expects `ImbalancedChen/provenance/original-fourth/FourthRows17LE.bin`.

From the repository root run:

```sh
python3 docs/p1/20261128/p15-fourth-fifth-source-inputs/prepare_input.py --repository .
```

The script verifies an existing input, otherwise copies the tracked input or retrieves its existing Git blob and materializes the verified reader alias. It refuses a mismatched existing file. For an isolated source tree, `--source` may point to the same hash-verified original file. This setup creates a generated input alias; it runs no Lean command. The sealed archive includes the isolated selected input.

Acceptance covers total decoding, unsigned wire ranges, exact ordered reencoding and explicit geometry admission, with original fifth archive source bindings. Wire-list multiplicity and policy Finset semantics are distinct as defined in the source. All-row geometry truth, analytic H/h licence, complete sixth/87 association and global PP/M are outside this owner.
