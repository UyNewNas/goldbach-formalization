# P2 strict04 policy proof repairs and existing dictionary reuse

Actual input source: `f5d007b8fd4c3a288ca23444c6d8a4e7f6bd8a07`.
Original P2 task: `1cd8f8cb588f4df1a9a9007c22fe7314`.
Complete log: `p2-strict-symbolic-04.log`, 20768 bytes, SHA-256
`9e2e3ff4e18c6f1b2ee5f7e1efba1210a767aae9fe66b423913e65dbc7751096`.

The two own-cube branches first unfold their existing density and history-head
expressions, then apply `if_pos hc` or `if_neg hc` separately. The strict
own-cube test, inherited first cube, prefix mass, and both physical levels
are unchanged. This is an expression-rewriting repair for the residual
goals actually reported at lines 91 and 101.

The missing name at line 187 already has a proof in
`ActualOwnCubeTupleDictionary.lean`. Import that module without editing
or recreating its theorem. Its `hlen : history.length = k + 1` argument
specializes to the existing three-prime candidate exactly. This is the
frozen manuscript's same first-exit and own-cube density dictionary, not a
new estimate or an extra hypothesis.

## Scope and native inputs

The existing dictionary imports `PrimeHistoryLogCoordinates`. Neither
module was in the old complete 322-module closure. The repaired target
therefore has 321 symbolic modules plus two finite candidates and the
whole endpoint, 324 modules in total.

The unchanged original project/import parsers give the exact delta in
`p2-strict04-policy-import-scope.json`: only these two existing project
modules are added. Both the full external-direct-import set and the native
direct-import set are unchanged. The original qualified native snapshot,
mirror, verifier and valid project records remain the intended inputs.

The old ordered 322 list is recovered exactly by removing those two names
from the new list, retaining SHA-256
`aa8118eba4e9169e9ffc7c315bf9b31b1752537a454e8f2840d5a4ad0d663985`.
The new complete ordered list has SHA-256
`c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f`.

## Existing successful work

The already retained CI archive `p4-same-rho-api-44584300242.zip`
(run 44584300242, artifact 14567501347) reports both unchanged module
sources as successfully built. Its 22 members contain logs and source/object
identities, but no actual .olean payload. Its effective overlay source
bindings match the two modules and their direct dependencies; the complete
current ancestor environments do not match (26 changed ancestors for the
148-module Dictionary closure and 15 for the 38-module LogCoordinates
closure). A separate old PrimeHistory schema-3 object also has incompatible
recursive dependencies. These historical successes are preserved as evidence;
they cannot supply a current strict-cache record or a missing object.

No proof is re-authored for either existing module. The original checker
must decide reuse from actual current objects and full dependency bindings;
historical success logs are not manufactured into new records.

## Static review

The PolicySaving candidate retains all eight original theorem headers and
its sole computation definition. Only one existing import is added.
Independent read-only review found no static blocker in the two branch
rewrites or dictionary specialization. No checker option, assumption,
inequality, axiom, `sorry`, or native computation was added.

PolicySaving candidate SHA-256:
`f3ef25d04bbe22d7071957a6d586874919d031274e19200abc2211fc262c7f2c`.

Status: source candidate awaiting the original checker. No new compile,
finite-certificate or independent-audit acceptance is claimed.
