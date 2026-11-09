# P1.4 — literal low-q primitive cost on the real first-disagreement and 87-Cell ledgers

## Recovery and immutable boundaries
Predecessor branch: `chatgpt/p1-full87-lowq-literal-abs-envelope-20261109`, actual HEAD `cf91cac500ee0386be09f70369cbe14b50431295`, prior source `d6b25738ebcb01d8f7419092020c4be1ec5e03d0`. Read predecessor full REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and complete 254-segment Lean source, the original PP cutoff and same-q physical/87-Cell ledger proof files, actual first-disagreement terminal L1 (blob `d467ce507bef3b0f150cac7ceab67583ebcaf880`), real signed helper and Chen prime supplier. No AGENTS.md at root, docs or docs/source-only (GitHub 404). GitHub branch head was rechecked immediately before writing; there was no other advance. Do not reset to `9649ab3`.

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, confirmed blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Constants c=49044063/25000000, K=8452171/1250000. Fixed Lean v4.33.0-rc1 / mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 / native 09b97db5764ade1246bfb77206baa1b124760958.

Independent task branch: `chatgpt/p1-full87-lowq-real-ledger-envelope-20261109`. New source commit `4ea12cd0c4a14c2729c24c2317181cd3e148f447` [skip ci]; source `docs/source-only/20261109-full87-lowq-real-ledger-envelope/P4AOriginalFull87LowQRealLedgerEnvelope.lean`, blob `947dcc5486202d8dee56005b04ed2d47a62c8503`, 226 newline-terminated lines, 2 public candidate theorem bodies, 1 private proof, and 1 explicitly defined actual source charge. The source commit was written by Git data tree/commit and moved to the new branch with a non-force expected-HEAD update.

## Substantive internal result
The prior LOW complete-q complementary primitive bound was
`|E_low| <= 2 T_W * Σ_(q<=X) |rho_RAW(q)-rho_LICENSED(q)|`.
Previously the fallback `Σ|Δrho|<=2 card(Q_low)` did not reflect common history.

Define the explicit **actual** same-q quantity `B(q)`: one genuine stopped first-disagreement terminal L1 at the unchanged shared rank-four source, plus the original RAW-outside invoice, the complete 87-Cell producer three-class leaf invoice, and LICENSED-outside invoice, ALL probed at `qProbe q` with `X=0`. No redefined policy or substitute Cell is involved. The existing pointwise same-q proof and positivity of each actual complete modulus imply the new local finite variation estimate

`Σ_(q∈Q_low) |rho_RAW(q)-rho_LICENSED(q)| <= Σ_(q∈Q_low) B(q).`

The new public candidate then composes this with the original primitive source-mass bound, with `T_W = Σ_(p∈chenPrimePrefix(N+D)) |W(p)|`:

`|E_low| <= 2 T_W Σ_(q∈Q_low) B(q).`

The second public candidate substitutes the SAME, non-duplicated low-q charge into the preexisting full-rho / strict-high-q transfer:

`|E_high| <= |E_full| + 2 T_W Σ_(q∈Q_low) B(q).`

Here `E_full` is the original full complete-q **paired signed** primitive discrepancy; `Q_low={q ∈ M_RAW∪M_LICENSED : q <= X}`, so q=X is LOW. These are alternate structural invoices replacing the coarse coefficient-variation/cardinality bound, NOT additive amounts on top of it. All original signed Rosser beta, small factors, occurrence multiplicities, genuine fifth/sixth admission gates, shared fourth history and physical q survive the reuse of existing actual source lemmas.

The structural charge is potentially VERY LARGE. No bound relative to the same H_N was proved, no actual saved87 affine witness or raw/finite/filtered signed gain was authenticated, and no valid Gevrey W_N or PP integer X was certified. The result is a finite candidate ledger adaptation, not an asymptotic PP estimate or a yellow-node closure.

## Checks actually performed
- Remote file/commit base read; fixed manuscript blob verified. The new Git source blob returned `947dcc5486202d8dee56005b04ed2d47a62c8503`, and fetching the Git blob returned the complete 9581-character source.
- Static source check: 226 newline-terminated lines; balanced (), [], {}; forbidden proof escape scan negative. This is not Lean parsing or compilation.
- Independent exact Python Fraction synthetic model: 1000 trials, 14816 common-prefix signed occurrences cancelled before absolute values, 4160 nonzero low-q discrepancy modulus cases, 233 q=X cases; zero inequality counterexamples. Random true RAW-only/LICENSED-only stopped lists, independently signed RAW/Cell/LICENSED frontier populations (87 Cell groups), source-mass bound and full/high/low partition. This is algebra testing only, not original saved87 numerical evaluation.
- Actual current local commands `lean --version`, `lake --version`, `elan --version` each exit 127 (command not found). 5.8 GiB available runtime, no pinned toolchain/mathlib/native artifacts. **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**, not kernel-replayed, transitive-axiom checked or independently verified.
- No triggered CI, Codex call, main/master write, force push, new cloud resource, pin change or external analytic proof.

## Exact open obligations / next concrete action
1. Prove a genuine same-H_N asymptotic upper bound for `Σ_(q<=X) B(q)` with the original one-sided fifth/sixth terminal source, SAME actual parent, signed affine history and 87-Cell saved geometry; otherwise `2 T_W` makes this invoice unsuitable for asymptotic payment. In particular do not treat geometric null sets as zero arithmetic charge and do not pay both the cardinality and structural invoices.
2. Verify original Gevrey W_N, fixed-before-N family permissions, the full-q PP integer cutoff X and the external singleton input's exact applicability. External PP remains REGISTERED_NOT_PROVED / NOT_CALLED.
3. Authenticate all original 87 saved witnesses, real N-dependent parent/common history, actual Source membership, selected ordinary/residual integrals and signed gain, including raw/finite/filtered loss.
4. Keep five eighth-frontier classes, endpoints, centre, primitive discrepancy, modulus factors, rank9, changed/tagged and separate compiler/density reserves on one H_N ledger.
5. When the exact pinned build already exists in an authorized environment, stage source-only imports at actual `ImbalancedChen` paths, run targeted `lake env lean`, fix elaboration failures and only then label COMPILED. Independently record kernel replay and axiom audit.

P1.4 parent status: YELLOW.
