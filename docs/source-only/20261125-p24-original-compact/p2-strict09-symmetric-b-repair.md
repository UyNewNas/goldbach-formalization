# Strict09 symmetric B leaf repair

- Scope: `ImbalancedChen/ActualThirdOriginalP4ASymmetricBLeaf.lean` only; candidate is statically checked, not compiled.
- Actual input: `7acdbd5be3d84fd257d1c44561cccdb6ae76c8dd`; strict09 accepted 297/321 modules.
- Complete evidence: [p2-strict-symbolic-09.log](p2-strict-symbolic-09.log), 6,328 bytes, SHA256 `b4082cbcad8176446ced442a92979541b9381fc13176953d533d4025d10080f9`.
- Before source SHA256: `d1e8c33842c734ad9d7393036c313fb60e4c5173ea56817a0c49c366f35706f1`.
- Frozen candidate SHA256: `1ee853f50b228a2b573954721335cf40d71738f434711ffd914ad012ca8ab3a6` (25,507 bytes).

The actual line 322 error leaves the third projection of `![x,x,z]` unreduced: `change z≠0; exact hz.ne'` reuses the scalar conversion already accepted in SymmetricTentPrerequisites. At line 374, `linarith` does not normalize the coefficient `25/128` against the large cast denominator; the accepted OrdinaryBCandidateLeaf pattern multiplies the existing inequality by nonnegative 128, then closes the coefficient identity by `ring`. These are expression/algebra repairs; neither adds a mathematical premise or changes a guard.

Frozen 1106 correspondence was checked narrowly in `certify_extended_prefix.py` at commit `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` (producer SHA256 `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`): the B tuple `(153,0,0,-96,256)`, positive residual, exact OLD Fraction endpoints, original ordinary OLD mean and endpoint-query chord are unchanged. This is semantic correspondence, not a claim that the P160 historical producer is byte-identical to that frozen script. The original 256-term log, ratio/positivity requirements, symmetric half mass and final upward rounding are untouched.

The old source-specific `unnecessarySeqFocus` and `unusedVariables` exceptions cease to apply after this edit. Separately from the two actual diagnostics, the sole single-goal `field_simp <;> ring` becomes sequential, and three explicitly unused hypothesis names become underscore names: `symmetric_B_residual.hg → _hg`, `saved_B_source_guards.ha → _ha`, and `.hd → _hd`. Searches of production and source-only Lean files found only two positional calls to the first theorem and no calls to the second. No named-argument caller needs migration.

Mechanical comparison against the actual input found 20 theorem headers: 18 are byte-identical; two differ only by the three listed binder identifiers, with premise types, positions, counts and conclusions unchanged. All four complete computational definitions, both imports and options are byte-identical. `git diff --check` passed. No mathematical gap was identified in these two repairs; actual elaboration and strict-linter acceptance remain for the original checker. No compilation, remote task, index operation or other source edit was performed.
