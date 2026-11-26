# Actual explicit-field attempt005 failure

Task `202af6f52a5c405eaa74fe1f00906a75` tested the exact published source
at `b667409e7e7f23094637dfccfdceec6e6d34ee68`. Its normal stage reported only
`(kernel) excessive memory consumption detected` at `rawRoot_decoded`.
No unsolved-goal diagnostic was emitted. This is not kernel acceptance.

The complete result is 4,822,231 bytes with SHA256
`812f43171da6572a897020df007846c3dfd4776253c4e851824b91536380f716`.
`ACTUAL_EVIDENCE.json.xz` preserves that result and the exact logs in an
XZ-compressed JSON array. Each entry contains its path, size, SHA256, and exact
UTF-8 content. The 192-byte normal log SHA256 is
`03ffeec727d76201990021b3d6e14110fb04a81b944685d0c3a995e19c28cc35`.

The next source candidate moves the existing composition calculation into a
private theorem over symbolic values, then instantiates its nineteen premises.
Sixteen certificates come from accepted imported owners; the other three are
the unchanged first three theorem commands in this still-unaccepted owner.
The private theorem and every public theorem must pass the same normal,
independent replay, and complete owned-declaration checks. No successful
receipt may be inferred from this failed attempt.
