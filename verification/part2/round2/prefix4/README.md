# Actual paired-v2 E0 prefix: completed component acceptance

`receipt.json` binds three new production sources to their successful strict
compiles and original bundled `leanchecker` replays. `compiler-types.json`
contains the complete, untruncated compiler-printed types and axiom dependencies
of all **309 declarations in nine Part 2 production modules**, including private
and generated declarations. The 253 previously accepted declarations are also
equal, record by record, to the archived P0 compiler inventories.

## Certified object

The original zero-based JSON rows are `0, 1, 2, 3`, all E0, with grid indices
`(422,510)`, `(422,511)`, `(423,509)`, `(423,510)`. The second row has `u_r = h`;
the proved open-support geometry permits this boundary equality. The source
file is the frozen same-mask-v2 witness from manuscript commit
`ba6ec11d800eccc54406490631895e174de85766`, SHA256
`f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`.
The selected row stream SHA256 is
`96df956686f3617d69cb0f72e510258991e7f21d10c36c635915f8cc0a573235`.

The certified finite sum is exactly

```text
(K/80) * sum(i = 0..3)
  integral(t_l(i)..t_r(i), integral(u_l(i)..u_r(i),
    integral(a..Z(i), integral(a..z, 1/(t*u*z^2*w) dw) dz) du) dt),
K = 8452171/1250000, a = 417/5000.
```

Its rational lower and upper bounds are respectively
`12676565261567/100000000000000000000` and
`12676572571081/100000000000000000000`.
Every certificate check is a proved Lean theorem. The accepted generic checker
and the actual-object semantic equality then imply the integral bound.
Stored Q160 endpoints are not premises in this proof.

The prefix includes the previously certified first row; these contributions
must not be added again. This finite-sum theorem has no remaining hypothesis.
Identification with a single union integral or the historical arithmetic
parent is a separate pending interface. It does not certify all 17,572 rows,
the E1 saved-floor semantics, the complete error ledger, or the final `K/c`.

## Actual gates

| New production module | Strict trust-zero compile | Original kernel replay | Owned declarations |
|---|---:|---:|---:|
| `PairedV2Geometry` | PASS, 4.919 s | PASS, 3.160 s | 10 |
| `PairedV2Prefix4Data` | PASS, 3.696 s | PASS, 3.105 s | 11 |
| `PairedV2Prefix4` | PASS, 7.675 s | PASS, 3.496 s | 35 |

The combined nine-module audit passed in 62.203 s. Its implementation was
strictly compiled and executed; it is not listed as a production-module
kernel replay. The only transitive axioms were `propext`, `Classical.choice`,
and `Quot.sound`; owned unsafe declarations and new axiom declarations were zero.

The six existing modules reuse the exact-source P0 compile/replay receipts in
`../upstream/`. This round did not rebuild or replay those six sources. Their
accepted objects were copied into the receiving object's root with matching
SHA256, and the new combined audit recorded exactly those six objects plus
the three new outputs.

The local runtime entry was the unmodified pinned Lake invoking the official
`Lean.Elab.runFrontend`, with `trustLevel=0`, `warningAsError=true`, and
`metadata_adapter=false`; see `../runtime/`. Only one Lean process ran at once.
This is not a claim that ordinary `lake build`, full-root CI, or `--fresh`
replay of every dependency succeeded locally.

`attempts/` retains the two failed elaborations and the generated pre-repair
prefix source. Geometry needed explicit rational-to-real casts; the prefix
needed forward unfolding of the sum definition. Final source hashes and the
later successful gates are distinct and are the ones accepted.

## Evidence and receiving checks

- `gates/`: original execution receipts and raw logs, without path or newline rewriting.
- `compiler-types.json`: all 309 explicit and readable compiler types.
- `compiler-readable-types.txt`: the same readable types, with every declaration included.
- `key-theorem-types.txt`: exact readable-type fields for the main integration interfaces.
- `generated-report.json`: deterministic source import and suggested rational endpoints.
- `receiving-checks/`: actual decoding and upstream-reception outputs; these are not Lean gates.
- `parent-source-guard.json`: comparison to the existing P2 parent, including the preserved core workflow.

Run from the repository root:

```sh
python3 verification/part2/round2/upstream/verify_upstream_acceptance.py
python3 verification/part2/round2/prefix4/verify_acceptance.py
python3 verification/part2/generate_paired_prefix.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --count 4 --check-generated ImbalancedChen/Certificates
```

These commands verify recorded acceptance and deterministic source identity.
To obtain fresh build, strict elaboration, replay, and census executions with
the unchanged locked dependencies on a normally supported environment, run
`bash verification/part2/check.sh`. The Part 2 workflow explicitly lists and
checks all nine production modules; full-root status remains separate.
