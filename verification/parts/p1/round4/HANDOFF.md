# P1 round 4 — inherited stored-cap check integration (pending runtime acceptance)

## Fixed identities
- Repository: UyNewNas/goldbach-formalization
- Branch: chatgpt/chen-p1-history
- Parent branch HEAD: e67570551e1da23e43f35652f793f674649f3eb6
- Common manuscript/proof baseline: ba6ec11d800eccc54406490631895e174de85766 / 1a80c1bcce67886f699d097fc37fd245cd3620bf
- P1 round 3 four source nodes and original verification receipts reused without modification.
- Source-independent previously claimed fifth-level candidate remains SOURCE_PENDING.

## New small leaf
`ImbalancedChen.HistoricalStoredCapBridge` receives THREE complete stored-mesh checks
over `D.cells3`, `D.cells4`, `D.cells5`, with exactly the inherited
`D.old`, `D.old4`, `D.old5` and the stored `D.cap3/4/5` values.
It projects the strict old < stored-new inequalities to the actual
`D.levelCheck` Boolean. The fourth and fifth old values are computed
by the previous chosen-or-fallback ancestor cells, not a root-only old.

The new independent `HistoricalStoredCapBridgeAudit` inventories
all declarations using *compiler defining-module origin*, including private
and generated declarations, printing each compiler type and all transitive
axioms and rejecting unsafe, axiom definitions or non-whitelisted axioms.

Both new Lean modules are imported by the P1 branch's `ImbalancedChen.lean`
root so the **pre-existing pinned core GitHub Actions gate** builds and
replays them without changing workflow files. Both files use
`set_option warningAsError true`; full acceptance additionally requires
fresh source-specific frontend trustLevel=0 and original leanchecker replay.

## Precise acceptance status
New source and audit are pending actual Lean execution; **no new declaration
is counted as proven until core CI succeeds and dedicated original-frontend
and original-checker results are collected**. The automation environment
lacks `lean`/`lake`/`elan` and outbound git network. Do not relabel
static source inspection or past round 3 receipts as a round 4 proof check.

The proof bridge is an implication from per-cell permit hypotheses;
the actual adopted mesh table (J/I/old/nu/cap and exact ancestor identities)
and certified Boolean evaluation are not provided by this leaf. No
numerical K/c, own-cube integral or prime-tuple end-to-end closure is claimed.

## Next smallest actions
1. Verify exact pushed HEAD and source hashes; inspect pre-existing core
   workflow results for that SHA; do not start duplicate build if still active.
2. Resolve any actual compiler or checker errors in the two new modules.
3. Produce complete proof/module object provenance, exported compiler types,
   transitive axiom census and original checker replay at the exact SHA.
4. Obtain the adopted manuscript table and independently certify each
   actual stored `D.cells3/4/5` gate; do not substitute P2 `exact_Z`.
