# P2.4 kernel memory diagnosis and early symbolic audit

Recorded 2026-11-26 08:30 UTC. Production P2 remains pinned at
`909214bbfb5ca9caa74fcc1b6f95b469bf43e125`; the later publication commits contain
documentation and diagnostic sources only. No finite acceptance is granted here.

## Accepted boundary

The original compiler gate has accepted the same 321 symbolic modules. The complete
scope remains 324 modules with ordered fingerprint
`c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f`.
A remains unaccepted; B and W have not run. The full 324 owned audit is incomplete.
The numerical target, original source computation, two-million-split schedule,
all-leaf accounting and strict cutoff have not changed.

## Directly observed kernel failure

| Diagnostic | Task | Lean child result | Child seconds |
|---|---|---|---:|
| Original full map, raw exception | `548f0b1357034b6e8c16afe4aef9d1a5` | exit 1, kernel excessive memory consumption | 80.958 |
| Prefix map, raw exception | `423c0bbff0a54baea7e078a19d3f0c23` | exit 1, kernel excessive memory consumption | 169.200 |

Both outer wrappers exited 0 only because they successfully preserved diagnostic
results. Both proof children failed. The raw tactic retains the official
`mkDecideProof → mkAuxLemma` kernel path and propagates the original exception
instead of replacing it with the ordinary decide fallback message.

Each run used the original `-M11264` Lean budget. The production A source remained
`f3b608cd96e21bd7bc425526d3731f86ed2440874a00ff61f14f3cfeb77e0e54`; the registry
remained `0858a9bea92e7c436382ae96fcd63dc709b73f5b346d93e6980c0389d7718e5a`.
The canonical A object remained absent and the qualified native binding compared
equal before and after. These observations identify a Lean kernel memory-limit
exception in these diagnostics, not an operating-system OOM and not the unknown
masked exception from original A02.

The prefix candidate SHA256 was
`1b284797644b124a7864a6fa952ce1d10ce0686aad82d955e5296f5bdddd6800`.
Its generic and exact-source Q80 adapters had passed isolated checks, but the
complete closed proof failed. It is retained as evidence and has not replaced
the production source.

- [Raw full-map result](p2-finite-a-kernel-raw-05-summary.json)
- [Raw full-map exact log](p2-finite-a-kernel-raw-05.log)
- [Prefix full-proof result](p2-finite-a-map-prefix-06-summary.json)
- [Prefix full-proof exact log](p2-finite-a-map-prefix-06.log)

## Original exporter preflight

Task `31d2dbedc14d4731a3213ed93041ad09` ran the unchanged exporter on the complete
ordered 324-module list under the original project lock and source pin. It
completed in 5.924 seconds, with no compile-registry change.

The actual selection was:

- Selected valid owned audit receipts: **0**.
- Unselected modules: **324**.
- Eligible independently compiled symbolic modules needing audit: **321**.
- Duplicate owned declarations: **none**.
- Manifest SHA256: `43b5f8366283883a81766b6ccb16f9f2c12dc70d59f54bc5f26b9a18e42428c1`.

Exporter exit 0 here is a successful partial preflight, not full-scope acceptance.
The next original-runner batch contains the first ten missing symbolic modules
in dependency order. The qualified external snapshot, original independent
leanchecker, complete-owned template and all type/safety/axiom rules remain
unchanged. After A/B/W pass, final selection must still cover every one of the
324 modules, with no unselected modules or duplicate declarations. The exporter's
separate `full_p2_complete: false` boundary remains unchanged.

- [Preflight selection summary](p2-symbolic-audit-preflight-01-summary.json)
- [Preflight exact log](p2-symbolic-audit-preflight-01.log)

## Bounded proof experiment

The independently reviewed fallback checks small blocks of source-node equality
proofs, retaining numerical normal forms only in checked propositions, proof
terms and temporary generator expressions. It never installs a computed table
or output as an evaluator definition. Each block must pass synchronous kernel
checking before its facts enter the temporary committed cache; generated
declarations remain private and subject to the same owned audit.

The first two failed toy runs are retained:

- Attempt01: missing Inhabited instances at partial accesses to certificate and
  value arrays; repaired by checked optional accesses.
- Attempt02: failed Decidable synthesis for a manually constructed raw Nat.le
  proposition; repaired at two sites using the official Meta.mkLe builder.
- Attempt03: advanced to block insertion, then failed because an explicitly
  selected helper name violated the active theorem's declaration-prefix
  restriction. Attempt04 removes only the old helper's naming override and uses
  the active private theorem's auxiliary-name context.

Attempt04 compiled successfully as `job_de405edd247f4590bdec36ab01cdd24b`:
source SHA256 `abe0febe06463b70f979d4ab911c837ef24c2dc02054bc553f98ce9758f89fae`,
child 3.340108807 seconds. It checked two four-node blocks and the transported
query; the final theorem's axioms were `propext, Quot.sound`.

The subsequent original-rule owned diagnostic
`job_0951a4af739b413e972f4fe9d7b836d5` **did not pass**. The independent
leanchecker replay succeeded in 17.477722986 seconds with unchanged inputs.
The original template then confirmed the complete 126-declaration serialized
and environment inventories, but rejected a declaration on its original safety
rule after printing 81 records. Later type/axiom records and the extra block
shape stage were not completed.

A separate read-only flag enumeration, `job_81364bcf894e4c9694e65e0746158b29`,
identified exactly one flagged declaration: `draftBlock._unsafe_rec`, whose
actual flags are **partial=true, unsafe=false, axiom=false**. The name alone
must not be treated as evidence of unsafe=true. The source/object/compile-log/
receipt hashes stayed unchanged. The repair in progress replaces the named
recursive generator with direct `Nat.rec`, preserving the proof-let scope and
all kernel, private, safety and audit checks. No audit exception is introduced.

- [Toy04 compilation](p1-node-proof-blocks-toy-04-summary.json)
- [Actual replay and owned failure](p1-node-proof-blocks-toy-owned-01-summary.json)
- [Complete actual owned diagnostic log](p1-node-proof-blocks-toy-owned-01.log)
- [Exact failed declaration flags](p1-toy-safety-inspect-01-summary.json)

No failed object is eligible for the independent replay or owned audit. Printing
sorryAx during compiler error recovery does not create a passing proof. The
successful toy must undergo the pinned independent checker and complete owned
inventory/safety/axiom/full-type review before the full Q80 implementation is
considered.

The exact original Q80 recurrence factorization passed separately as
`job_7006b0d3c9724f71bd377d22f58bf026`, source SHA256
`2f2e00982c0e28a4e93187106df1d0eed5d0912aec2b6473c0737689ac9c2a48`, child
1.328505157 seconds. The eight printed axiom sets are allowed subsets; its
mechanical nodeUpdate factorization has no axioms. This isolated module uses
byte-exact frozen arithmetic fragments and contains no output table or block
generator. Production adoption still requires the unchanged numerical
endpoint and original A/B/W gates; neither a toy pass nor a diagnostic pass can
grant those credits.

## Active original audit batch

The first ten symbolic targets were submitted using the unchanged original
runner as P2 task `b7a273f404aa417cac93ae283d07340c`. At the last log read it had
passed RationalLogCertificate (47 declarations) and PairedFibreIntegral
(13 declarations), and was auditing P2DirectedLogRounding. The complete batch
summary and normal source/registry/native postchecks have not yet returned,
so this progress is not the final batch acceptance record.
