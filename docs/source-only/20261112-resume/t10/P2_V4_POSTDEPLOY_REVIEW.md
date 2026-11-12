# P2 v4 driver publication review

The 26 reviewed payloads total 274,854 bytes. I recomputed the raw blob identities from the deployed copies, matched every destination to the independent configuration allowlist, and reconstructed the entire root tree from the seven-workflow parent by applying exactly those 26 paths. The local and downloaded Git commit identities agree.

| Object | Verified identity |
|---|---|
| Branch | `ci/p2-integer-mass-r3-20261112` |
| Commit | `dfda53cc0d9eceeb413a7f0c1ef5045ddd35c206` |
| Sole parent | `356c3782e9428098a2fcbfb18c689bef264d84fa` |
| Root tree | `e961315a6e8a73ac637636c2a091355f9cd1de15` |
| Independent 26-file allowlist SHA-256 | `bda1d144e29601f4e1b1ee1b219cd326798b75b19484e2aa56b40dac21d04830` |
| Published receipt SHA-256 | `34732a8bf732cf2c4cae249f613ea15e03a755ff2321b30138f2fdb97096bc08` |

All three downloaded subtree responses are complete. Every prospective destination has the recorded path, mode 100644, size and Git blob. Six inherited workflow blobs match the parent byte for byte. The seventh carries the reviewed one-line branch exclusion. The eighth is the isolated P2 push workflow.

The recorded initial response contains exactly one run at this head, [43186809155](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43186809155), on the intended push branch. The response records its status as in progress. The proof gates for the 102 modules require the terminal run evidence. This review covers publication identity and initial dispatch only.
