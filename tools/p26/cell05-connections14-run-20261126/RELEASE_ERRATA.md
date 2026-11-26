# Frozen v1 documentation correction

The frozen v1 `INPUT_CONTRACT.md` calls the original baseline evidence
“156-step baseline control evidence.” This means **156 files**: 154 capsule
files and two controls. The underlying accepted baseline contains 18 proof
steps and the raw05 kernel addendum. The validator implements the original
evidence checks and does not interpret the file count as a proof-step count.

The new Cell05 scope remains exactly 14 owners and 42 planned new proof steps.
The old fields73 chain remains 219 accepted steps. No old proof is executed.

The source archive and frozen workflow are unchanged by this documentation
correction: `cell05-connections14-source-v1.tar.xz`, 145492 bytes, SHA-256
`3334435ea38770c5361d56c52b2595696d2072d55e1e22b0132d81acd03f6188`.
