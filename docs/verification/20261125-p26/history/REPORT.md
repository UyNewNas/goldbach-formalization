# P2.6 history and Q96 endpoint candidate

## Delivery

This is a nine-file Lean source overlay against commit `298670f119d24874b719facb3ef756f1e01223a1`:
two new lightweight modules, six original modules with only approved declaration
moves/import changes, and `P2OriginalSaving19ActualEndpoint`.

The first completed overlay and its static audit were created before the executor
reset. This script reconstructs the same candidate from the tool record and the
restored P1 snapshot. No Lean compilation or remote job was started. These are
uncompiled candidates with no kernel acceptance credit.

## Preserved declarations

`P4AOriginalCommonArchiveScheduleData` keeps the original namespace and exact body
of `P4AOriginalCommonArchiveSchedule.fixedSchedule`.

`P4AOriginalArchiveFourteenData` keeps the original namespace and exact bodies of
`schedule`, `data`, `data_eq_original_heldData`, and `actual_fourth_geometry` from
`P4AOriginalArchiveFourteenPositivePresieve`.

The old owner modules import these definitions. `CompleteSixthChronology` and
`Full87SourceDispatch` import the actual-data module. `ActualCommonHistory` drops
its unused direct common-schedule consumer import. `NewFifthUnion` imports the
actual `P1HistoricalFifthCommonPolicyInputs` supplier directly.

Every unchanged declaration and proof body in the six old modules is compared
byte-for-byte after removing import lines and exactly the authorized moved blocks.
Original line endings are preserved.

## Saving19 glue

`q19` is exactly `283388722705335806564439 / 2^96`. The public results are:

- `original_cell_integral`;
- `selectedSaving_eq_original_cell_sum`;
- `original_q96_le_original_cell_sum`;
- `selectedSaving_le_full_source`;
- `original_q96_le_full_source`;
- `paper_saving_le_q19` and `paper_saving_le_selectedSaving`;
- `exists_ordinary_q96_gain`;
- `exists_positive_presieve_q96_gain`.

The private `source19` proof is reused byte-for-byte from `ArchivedIntegralRows`;
that heavy module is not imported. The original 28,918-row theorem supplies the
Q96 value. The thirteen-cell identity comes before inclusion in the nonnegative
full source sum. No other family numerical bound is used.

The ordinary and positive statements match `UnionActualGain` after only replacing
the full integral sum by `q19`, renaming the theorem, and shortening the opened
`physical` identifier. All target-independent choice quantifiers, beta conditions,
cutoffs, and actual policies are unchanged. Positive projection is still on one
complete new tree, with its same actual ordinary sixth parent.

## Dependency result

The pre-reset complete source graph, with no missing modules, gave:

| Root | Baseline | Candidate |
|---|---:|---:|
| ActualCommonHistory | 813 | 653 |
| UnionHistory | 953 | 737 |
| UnionActualGain | 955 | 739 |
| UnionActualGain plus Saving19OwnedIntegral | 959 | 757 |
| New actual endpoint including itself | — | 758 |
| Heavy ActualSavedEndpoint, not used | 1988 | 1794 |

`STATIC_AUDIT.json` separately reports the newly restored source graph and any
missing modules, so sparse-source counts cannot be mistaken for a complete graph.
The complete endpoint excludes Saving16OwnedIntegral/OriginalArchive,
Saving17DescendingIntegral, FirstIntegralEndpoint, CertificateBudgetAssembly,
Full87SavedGain, ActualSavedEndpoint, ArchivedIntegralRows and ArchiveSourceIndex.
The actual common-history and source-geometry suppliers remain.

## Manuscript and remaining gate

The 2026-11-06 manuscript source pin is
`a988cba584d803ae2856a0de50efb582f4f3dd6a`, under `paper/release-20261106/en/`.
`numerical-appendix.tex` label `num:simplex-moment` (line 188) gives the unchanged
moment law; slot 19 (line 270) gives `357686854 / 10^14`.
`argument.tex` label `eq:current-eighth-saving` supplies the unchanged current-parent
density semantics used by the existing analytic supplier.

This is a module-boundary change plus explicit source-index glue. The remaining
gate is actual Lean compilation together with the existing moment/ownership and
actual-history suppliers. Static checks and patch applicability are not kernel
proofs. `candidate.patch` is intended for the specified source snapshot; the main
worktree and all remote queues remain untouched by this script.

## Source SHA-256

Absolute paths and Git blob IDs are in `SOURCE_MANIFEST.json`.

| Source module | SHA-256 |
|---|---|
| `P4AOriginalCommonArchiveSchedule` | `686cbb4a435819025bf43446259b695a5ea95fa11485aeb90eefb2ebd8c79024` |
| `P4AOriginalArchiveFourteenPositivePresieve` | `ffa78a1c9331cc3d782d360d76aba438236672d42e98d43c36d7d30b437147e2` |
| `P4AOriginalCompleteSixthChronology` | `87a914ffd635d3318d2fe49c84f84bc4764f7242218120b996c2af0d6819c57a` |
| `P4AOriginalFull87SourceDispatch` | `c9d5c6e595968750a84125022904867120459606acd578cb1badf8ca6277ea51` |
| `P4AOriginalFull87ActualCommonHistory` | `3fe33184c97ded23c1ec2a1960bed5f1d1208bc8a33b6d5e42b030633137a992` |
| `P4AOriginalNewFifthUnion` | `38f3b4355416baf67f60ddd42ddb07d4770c192c550b529b6cf7a0d253ef0417` |
| `P4AOriginalFull87ArchivedIntegralRows` | `5d3a20c36737c730939794de9b3042055f410165820af17111243f8b351069ab` |
| `P4AOriginalFull87UnionActualGain` | `6f92a62137361cf77a5063f2f7c78c0df1288e891f9b90057aea31c712ed7c7c` |
| `P4AOriginalFull87SourcePrimeTests` | `6b9230180b554e9dbb7391aa0d50821fc29a8b674a893f42c5cb34a94df1a77d` |
| `P4AOriginalFull87SourceDictionary` | `623b24cec83e7a232dca41dbfcab3070866c7e5480e2d1ddb35efcd1d54a9803` |
| `P4AOriginalFull87EighthKernelControl` | `24520748bfe47ce533ea0c1f88d3c4e7f33db92d5c58c4aa9f7c9f493691406f` |
| `P2OriginalSaving19OwnedIntegral` | `ab58f4acc2a2ea93919d0ee37e5c63e1dba1f07fd704833fefc042d0bb61bafc` |
| `P2OriginalSaving19SourceMeasure` | `dcbbe12621b0f6973ee51734477996db8b1c27db813f5bb202ee20e4c77cfbe4` |
