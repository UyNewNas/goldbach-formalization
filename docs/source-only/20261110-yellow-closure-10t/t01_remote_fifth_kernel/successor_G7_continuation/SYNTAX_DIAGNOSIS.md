# Namespace syntax supersession

The initial G7 candidates used `namespace S := …` as if Lean supported namespace aliases. That was an authoring error. T05 first identified it against the locally archived4.24 parser; the actual remote toolchain's `leanprover/lean4@v4.33.0-rc1` parser was then read independently. Its immutable Git blob593b92e505e09d437e0070bfd2af864709787de8 also defines the namespace command as `"namespace " >> checkColGt >> ident`.

The superseding files in `syntax_repairs/` remove those commands and expand all qualified uses to their full `ImbalancedChen.…` names. All initial11 and four geometry frozen byte receipts remain unchanged. The new, unfrozen CompactTrim was corrected directly. The declaration-name sequences were compared statically and match. No Lean parser, compiler or proof body was executed; exact syntax/elaboration remains a future remote gate.

FifthComparison additionally selects its separately registered explicit `B(t2)=W(t)` ring bridge. That change preserves its theorem statement and imports and is distinct from namespace spelling.

Primary parser source: [Lean4.33.0-rc1 Command.lean](https://github.com/leanprover/lean4/blob/v4.33.0-rc1/src/Lean/Parser/Command.lean). This is source inspection, not a runtime version probe.
