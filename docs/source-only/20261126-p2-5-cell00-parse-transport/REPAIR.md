# OriginalParse symbolic transport repair

This is an uncompiled source candidate. The three public theorem statements,
three imports, original data, parser, decoder, finite definitions, and printed
public axiom queries are unchanged. Three private expression wrappers are the
only added declarations. Complete normal compilation, kernel replay, and the
existing full owned audit remain required before this owner is accepted.

## Observed failure and retained acceptance

Actual consumer attempt005 at publication
`be20f0b050bb787ecb98f9afdd9b6a386706f45a` has result SHA256
`bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88`.
The aggregate failed during OriginalParse's normal gate after 172.179 seconds,
with exit 1 and no timeout. Its complete 1,046-byte log has SHA256
`8c4de444dda9af81f3783f916be29440a89b465ac7096de0d7a5a51247f12d16`.
It reports kernel memory exhaustion at the first and second theorem declarations
and a downstream `No goals to be solved` error. The printed fallback axiom names
belong to this failed checking session; they supply no accepted proof or object.

The preceding Decoded owner passed normal compilation, replay, and the complete
owned audit. Its 16,208-byte object has SHA256
`f700e8e866da0192152040a0853e27eab857ee007c0076df61613e3a849e534f`.
Its four audited declarations comprise three public source declarations and the
generated `cell00_decode_success.match_1`. The four-consumer continuation reuses
that owner under this original publication and failed aggregate. It reruns none
of Decoded's gates and does not promote the failed aggregate to acceptance.

## Existing results and the missing expression interface

The accepted `SourceJsonFuelBridge` already provides generic parse-and-bind
success lemmas, including `parse_bind_ok_of_value_of_ofList_eq`. No new generic
Except-bind lemma is needed. The accepted `cell00_original_json` already packages
the exact original String binding, complete parser result, fuel, and tail checks.
The accepted `cell00_decode` supplies the unchanged typed decoder result.

The accepted FiniteCore defines `parsedCell`, `parsedCellSuccess`, and `archive`
but has no theorem transporting a supplied parse/decode success through those
three named definitions. FiniteArchive's all-cell `original_parse_success`
depends on its separate fourteen-cell closed guard and cannot serve as an input
to this cell's proof.

The new private wrappers use `congrArg` and equality transitivity to transport
the supplied certificates. They conclude exactly `parsedCell i = .ok decoded`,
`parsedCellSuccess i = true`, and `archive i = decoded`. Their cell index and
returned value remain variables while the kernel checks the conversions through
the existing definitions. A variable index cannot select a concrete entry of
the original fourteen-text vector, so the original parser has no closed String
to normalize in these conversions. The public theorems then instantiate the
opaque wrappers at zero; their conclusion heads match syntactically.

Using `congrArg` directly in the closed public theorems would leave the
definition-to-expression comparisons at index zero. This candidate places those
comparisons inside the private wrappers instead. The resource diagnosis concerns
proof expression and normalization; the failure log does not establish a missing
mathematical derivation. Actual strict gates must still establish that this proof
expression fits the available resources.

Every private premise is discharged in the closed target: the first wrapper uses
the two accepted certificates; the second and third use the preceding same-owner
`cell00_original_decode`. No public theorem gains a premise. The full audit must
include all three private wrappers and every generated declaration, with no
private-name exclusion or guessed final owned count.

## November 6 manuscript boundary

The inspected source is `paper/release-20261106/en/numerical-appendix.tex` in
`UyNewNas/chen-imbalanced-semiprimes` at frozen commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`, Git blob
`428e5fb4cd92b01b72119d795b8eeb01c67e3ccd`, SHA256
`bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.
The repository's `MANUSCRIPT_REUSE_AUDIT.json` records the release identity and
the separate Saving16 obligations.

The appendix requires exact correspondence between numerical objects, source
certificates, JSON pointers, and rational extraction formulas. It separately
requires vertex checks, original inequalities, face incidences, pulling
triangulation, and correctly directed integral enclosures. Positive savings use
the selected nonnegative subfamily. This repair supplies only the original-text
parse/decode/archive correspondence needed to refer to the existing cell data.
It does not prove those geometric obligations, the fourteen-cell guards, Q96,
or P2.5. No manuscript gap is inferred from this kernel resource failure.
