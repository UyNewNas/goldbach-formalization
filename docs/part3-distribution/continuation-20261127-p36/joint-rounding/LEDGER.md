# Joint coefficient and wall-payment compiler ledger

The predecessor is the accepted joint-marked group, published at
`41847b68d10c2d7805b2c4441a96f22e3c315b86`. Its original 333 dependencies
and two accepted owners give the exact 335-entry pool for this group.

| Attempt | Original task | Observed result |
|---|---|---|
| 001 | `job_ee8831d72deb49e7a59bff6e8156a76d` | The raw-value equality required matching the actual proposition across two different decidability instances. |
| 002 | `job_bbce3b33120842c88c74b629809d3d06` | Its two explicit branches also needed simplification of the right-hand conditional's proposition. |
| 003 | `job_acc9d4b3a23d46d9ad5edd98c6c81e5f` | JointCellCoefficient and JointBetaAttachment passed strict compilation. PhysicalRawRank needed an explicit equality between the owner-based and coordinate-based spelling of the same physical policy. |
| 004 | `job_a96f79002ce54eab9513cf7502838a22` | The first three owners passed strict compilation. JointPrimeWallPayment needed the prime-label function expanded explicitly before rewriting its mapped word. |
| 005 | `job_798e166bda5845d2a7c4513e5fc43b8d` | All five strict compilations, all five exact kernel replays and the complete 83-declaration defining-module inventory passed. The 630,072-byte original output and its 459,684-byte evidence archive were retrieved losslessly and independently verified locally. |

Each failed attempt preserves the original terminal, complete stdout and
submitted source pins. These are elaboration repairs with unchanged
declaration contracts. The latest full-group strict compilation, kernel
replay, complete inventory and local original-archive verification must
all succeeded for attempt 005. This group receives five new proof owners
and 83 declarations. The cumulative unique P3.6 scope is 57 owners and
1,095 declarations; whole P3.6 remains open.

The original verification ID is `c1625dc484464467b58e5684ef09d4ab`.
The accepted report SHA-256 is
`77693f8568e2ed0d056044f99bb9ad5864f199b10be9654cb41da4edf569dcac`.
The original output SHA-256 is
`e7422fece7c63a9e511b57487ff344dc30d6d34a42dd4d9022cfd428cf720eee`;
the archive SHA-256 is
`8a061430e03d041049ec96730df22856c436fae27c3f7de257c419b3e1b4e91c`.
All observed transitive axioms are exactly `Classical.choice`, `Quot.sound`
and `propext`. The detailed original outputs, declaration types, source and
object hashes, and local validator receipt are preserved in `accepted/`.
