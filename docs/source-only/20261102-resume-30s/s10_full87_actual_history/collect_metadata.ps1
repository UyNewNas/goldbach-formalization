# Text/byte metadata only. Does not execute Lean or mathematical producers.
$repo = 'E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation'
$scope = 'docs/source-only/20261102-resume-30s/s10_full87_actual_history'
function SourceMeta([string]$relative, [string]$purpose) {
  $absolute = [System.IO.Path]::GetFullPath((Join-Path $repo $relative))
  $item = Get-Item -LiteralPath $absolute
  $lines = @(Get-Content -LiteralPath $absolute)
  $module = $null
  $imports = @()
  $decls = @()
  if ($item.Extension -eq '.lean') {
    $module = 'ImbalancedChen.' + $item.BaseName
    $ns = $module
    for ($i=0; $i -lt $lines.Count; $i++) {
      if ($lines[$i] -match '^import\s+(.+)$') { $imports += $Matches[1] }
      if ($lines[$i] -match '^namespace\s+(ImbalancedChen\S+)$') { $ns = $Matches[1] }
      if ($lines[$i] -match '^(?:private\s+)?(theorem|def|abbrev|structure|inductive|lemma)\s+([A-Za-z0-9_]+)') {
        $decls += [ordered]@{name=($ns+'.'+$Matches[2]);kind=$Matches[1];line=($i+1)}
      }
    }
  }
  return [ordered]@{
    path=$relative; absolute_path=$absolute.Replace('\','/'); purpose=$purpose;
    sha256=(Get-FileHash -LiteralPath $absolute -Algorithm SHA256).Hash.ToLowerInvariant();
    bytes=$item.Length; line_count=$lines.Count; module=$module;
    imports=$imports; declarations=$decls
  }
}
$files = @(
  (SourceMeta "$scope/P4AOriginalFull87Ownership.lean" 'new actual original-source ownership'),
  (SourceMeta "$scope/P4AOriginalFull87SourceDispatch.lean" 'new own-prefix source dispatcher and local preservation')
)
$reused = @(
  (SourceMeta 'docs/source-only/20261102-resume-30r/full87_source_history/P4AOriginalFull87SourceDictionary.lean' 'direct import: all87 literal source dictionary'),
  (SourceMeta 'docs/source-only/20261102-resume-30r/full87_source_history/P4AOriginalH5H7SourceDispatch.lean' 'direct import: original first-failure priority'),
  (SourceMeta 'docs/source-only/20261102-resume-30r/full87_source_history/P4AOriginalFull87PrefixBinding.lean' 'direct import: own ancestors and actual prime frontier'),
  (SourceMeta 'docs/source-only/20261102-resume-30p/all22_common_history/P4AOriginalFiniteSignedHistoryRefinement.lean' 'direct import: finite exact occurrence-list refinement'),
  (SourceMeta 'docs/source-only/20261102-resume-30r/all22_actual_sources/P4AOriginalArchiveFourteenPositivePresieve.lean' 'direct import: concrete original four/five schedule'),
  (SourceMeta 'docs/source-only/20261102-resume-30r/full87_source_history/P4AOriginalRemainingEighthSources.lean' 'reused original whole-row semantics'),
  (SourceMeta 'docs/source-only/20261102-resume-30k/saving16_glue/P2OriginalSaving16HistoricalMesh.lean' 'prior actual14 own-prefix common mesh inspected; not generalized by assertion'),
  (SourceMeta 'docs/source-only/20261102-resume-30k/saving16_glue/P2OriginalSaving16CommonOldPolicy.lean' 'prior actual14 parent construction inspected'),
  (SourceMeta 'docs/source-only/20261102-resume-30q/fifth_parent/P1HistoricalFifthActualHistoryAdmission.lean' 'original thirdowner/Q3/Q4 same-q source inspected'),
  (SourceMeta 'docs/source-only/20261102-resume-30r/full87_source_history/REPORT.md' 'frozen R03 scope'),
  (SourceMeta 'docs/source-only/20261102-resume-30r/full87_source_history/REGISTRY.json' 'frozen R03 exact source pins'),
  (SourceMeta 'docs/source-only/20261102-resume-30r/reviews/r25_review_archive_history.md' 'independent R03 archive/history review'),
  (SourceMeta '../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex' 'fixed original manuscript'),
  (SourceMeta '../chen-imbalanced-semiprimes/proof-library/source/global-positive-upper-completion-20261010.txt' 'original chronology and common finite realization note'),
  (SourceMeta "$scope/REPORT.md" 'delivery scope and full-terminal premise delta'),
  (SourceMeta "$scope/collect_metadata.ps1" 'text and byte metadata generation only')
)
$registry = [ordered]@{
  schema='source-only-registry-v1'; packet='S10'; date='2026-11-02';
  yellow_node='完整87域的实际动态parent、共同历史与原策略成员供应';
  status='source-only partial checkpoint; uncompiled; no kernel credit';
  whole_assigned_yellow_scope_source_complete=$false; kernel_verified=$false;
  formal_credit=0; finite_proof_bodies='UNEVALUATED';
  source_parent_commit='e2a05f73d5f169fff847d72dcfcc66ec54ad4f87';
  source_parent_tree='43e3384e7178e05b66ac347c7f6321d89679dc45';
  lean='leanprover/lean4:v4.33.0-rc1'; mathlib='e4c91783ca8e6a7c693ae624ade32fd22d4e43c1';
  native_upstream='subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958';
  frozen_r_manifest_sha256='cdfc42fe572d5ef5c006b6885f02a3960f3eb88433c032d3d136982744b37ab7';
  files=$files; reused_sources=$reused;
  removed_premises=@(
    'All87 original-source ownership/disjointness is derived from exact source rows.',
    'Selected source membership and own-rank8 frozen cap are derived, not supplied.',
    'Selected cap positivity and cap < 153/256 follow from original source rows.',
    'Local eighth changes preserve supplied parent continuation outside their source and commute.',
    'The common finite raw-source partition preserves every occurrence-list sum exactly.'
  );
  remaining_mathematical_premises_or_constructions=@(
    'Instantiate concrete S09 complete sixth/current-parent bound and discharge original supported-third premise on the same common finite realization.',
    'All87 common compact/proper-wall-trim finite realization with actual thirdowner/Q3/Q4 and own-prefix true histories.',
    'Concrete all87 chronological final policy and exact same-policy original14/original13 signed continuations.',
    'S14 actual finite buffered cap realization, changed-set coverage and separately paid compiler reserve.',
    'Reliable same-source remote Lean/kernel and axiom evidence for the full closure.'
  );
  new_axioms=@(); target_equivalent_hypotheses=@(); invented_lambda6_fields=@();
  constants=[ordered]@{c='49044063/25000000';K='8452171/1250000';mu='25/128';source_cap_buffer='1/1000000';source_floor='53/13824';selected_cap_ceiling='153/256'};
  quantifier_alignment='Raw source dispatch is for arbitrary N and source tuples; required full finite realization must first choose compact supports/proper-wall trims, e/chi/common q and finite policy before N.';
  original_paragraphs=@('manuscript-body.tex:371-375','manuscript-body.tex:435-449','manuscript-body.tex:453-509','global-positive-upper-completion-20261010.txt sections2-4, finite realization lines205-216');
  independent_review='S26 read Ownership and SourceDispatch as narrow facts; full actual policy/common buffered realization remains open.';
  remote_target=@('ImbalancedChen.P4AOriginalFull87Ownership','ImbalancedChen.P4AOriginalFull87SourceDispatch');
  remote_axiom_targets=@('source_subset_dictionary','same_kind_separator','source_owner_unique','sourceOwner_some_iff','selectedExponent_bounds','localPolicy_commute','one_common_source_partition');
  remote_check_plan='Root materializes exact frozen direct/transitive source closure; checks modules with pinned Lean/mathlib and prints axioms. Narrow-module success alone does not close the full assigned yellow.';
  transitive_import_closure_verified=$false; prohibited_operations_performed=@()
}
$target = Join-Path $repo "$scope/REGISTRY.json"
$json = $registry | ConvertTo-Json -Depth 12
[System.IO.File]::WriteAllText($target, $json + [Environment]::NewLine, [System.Text.UTF8Encoding]::new($false))
foreach ($entry in $files) { Write-Output ($entry.path + ' ' + $entry.sha256) }
Get-FileHash -LiteralPath (Join-Path $repo "$scope/REPORT.md"), $target -Algorithm SHA256 | Select-Object Path, Hash
