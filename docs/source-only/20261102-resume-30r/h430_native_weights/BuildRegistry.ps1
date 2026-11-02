# Static source metadata only. No Lean, guard, numerical or Git execution.
$ErrorActionPreference = 'Stop'
$r15Root = 'E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation'
$r15Scope = 'docs/source-only/20261102-resume-30r/h430_native_weights'
$r15Mathlib = '//wsl.localhost/Debian/home/slava/codex-lean-ve/native-packages/mathlib/'

function Get-R15Pin($path, $module, $status, $used, $allDeclarations = $false) {
  $abs = if ([IO.Path]::IsPathRooted($path)) { $path } else { Join-Path $r15Root $path }
  $lines = [IO.File]::ReadAllLines($abs)
  $ns = ($lines | Where-Object { $_ -match '^namespace ' } | Select-Object -First 1) -replace '^namespace ',''
  $declarations = @()
  for ($i = 0; $i -lt $lines.Length; $i++) {
    if ($lines[$i] -match '^(?:@\[[^\]]+\]\s*)?(private\s+)?(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s(:]+)') {
      $declarations += [ordered]@{
        source_name=$Matches[3]; kind=$Matches[2]; line=($i+1)
        visibility=$(if ($Matches[1]) {'private'} else {'public'})
        public_qualified_name=$(if ($Matches[1] -or $status -eq 'mathlib_api_source') {$null} else {$ns+'.'+$Matches[3]})
        compiled=$false; kernel_verified=$false
      }
    }
  }
  $selected = if ($allDeclarations) {$declarations} else {@($declarations | Where-Object {$used -contains $_.source_name})}
  $missing = @($used | Where-Object { $_ -notin @($selected | ForEach-Object {$_.source_name}) })
  if ($missing.Count -gt 0) {throw ('Declaration location mismatch: '+$path+': '+($missing -join ', '))}
  [ordered]@{
    path=$path; module=$module; bytes=(Get-Item -LiteralPath $abs).Length
    sha256=(Get-FileHash -LiteralPath $abs -Algorithm SHA256).Hash.ToLowerInvariant()
    first_namespace=$ns
    direct_imports=@($lines | Where-Object {$_ -match '^(public )?import '} | ForEach-Object {$_ -replace '^(public )?import ',''})
    declarations=$selected; status=$status
  }
}

$new = @(
  Get-R15Pin "$r15Scope/Part5OriginalH430NativeBuchstabMeasure.lean" 'ImbalancedChen.Part5OriginalH430NativeBuchstabMeasure' 'new_source_only_uninstalled' @() $true
  Get-R15Pin "$r15Scope/Part5OriginalH430FullRootAmplitude.lean" 'ImbalancedChen.Part5OriginalH430FullRootAmplitude' 'new_source_only_uninstalled' @() $true
)

# Each row is an exact local path and selected reused declaration names.
$reuseRows = @'
docs/source-only/20261102-resume-30q/h430_descendants/Part5OriginalH430BuchstabPhysicalBudget.lean|buchstabShape,directionGuard,physicalStart,physicalStart_ge_one,buchstabPoint,buchstabPoint_query,physicalAtomPullback_eq,actual_buchstab_Jacobian,coefficient,coefficient_difference_le,frozenDescendant_physicalStart_tendsto
docs/source-only/20261102-resume-30q/h430_descendants/Part5OriginalH430DescendantLimits.lean|idealDescendant,frozenDescendant,frozenDescendant_ceiling,frozenDescendant_residual_tendsto,idealDescendant_residual_pos,idealDescendant_ceiling_pos,frozenDescendant_weight_tendsto
docs/source-only/20261102-resume-30p/h430_smooth_causal_boxes/Part5OriginalH430MovingBuchstabAtoms.lean|startAtomDensity,startAtomDensity_integrable
docs/source-only/20261102-resume-30p/h430_frozen_q/Part5OriginalH430FrozenTableRootMass.lean|idealQuery,frozenQuery,idealQuery_measurable,frozenQuery_measurable,ideal_clamp_preserved,frozenQuery_tendsto,ae_frozen_H430_tendsto
docs/source-only/20261102-resume-30o/h430_frozen_q/Part5OriginalH430PhysicalMassPerturbation.lean|physicalWeight,frozenRootWeight,frozenRootWeight_eq,rootWeightConstant,rootWeight_error,rootBand_volume_lt_top
docs/source-only/20261102-resume-30o/h430_frozen_q/Part5OriginalH430FrozenRootMass.lean|sourceResidual_measurable,frozenRootWeight_measurable,sourceWeight_measurable,rootBand_measurable,weightEnvelope,weight_bound,finiteTau,finiteTau_pos,finiteTau_le,levelError_finiteTau_tendsto
docs/source-only/20261102-resume-30o/h430_frozen_q/Part5OriginalH430FrozenPerturbation.lean|meshError
docs/source-only/20261102-resume-30m/h430_common_approximation/Part5OriginalH430PhysicalRoots.lean|Root,rootBand,sourceResidual,sourceRoot,rootBand_subset,sourceResidual_bounds,sourceRoot_argument
docs/source-only/20261102-resume-30m/h430_common_approximation/Part5OriginalH430FrozenRootRefinement.lean|frozenLevel,frozenLevel_bounds,root_total_bounds,frozenRoot,frozenRoot_residual_bounds
ImbalancedChen/Part5OriginalU34H430Integrable.lean|upperAmplitude,continuousOn_upperAmplitude,rootArgument,branchWeight,branchCoefficient,U3H430Coefficient,U4H430Coefficient
ImbalancedChen/Part5UpperTableLookup.lean|upperRoot,H430,measurable_H430,norm_H430_le
ImbalancedChen/P2EnhancedLowerPhysicalNode.lean|PhysicalNode,word,residual
ImbalancedChen/P2EnhancedLowerPhysicalTransition.lean|StepShape,buchstabArgument,perform,OneGate,LocalDomain
ImbalancedChen/P2EnhancedLowerFinitePhysicalGraph.lean|Program,Coordinates,Member
ImbalancedChen/P5OriginalActionMassBound.lean|buchstabAmbient,buchstabKernel,buchstabKernel_continuous,buchstabUpperDomain,buchstabLowerDomain
ImbalancedChen/P5OriginalFeedbackTableKernels.lean|tableAtomSet,measurableSet_tableAtomSet
'@
$reuse = @($reuseRows -split '\r?\n' | ForEach-Object {
  $parts = $_ -split '\|'
  $module = 'ImbalancedChen.'+[IO.Path]::GetFileNameWithoutExtension($parts[0])
  $status = if ($parts[0].StartsWith('ImbalancedChen/')) {'existing_production_source_read_only'} else {'source_only_dependency_not_installed'}
  Get-R15Pin $parts[0] $module $status ($parts[1] -split ',')
})
$api = @(
  Get-R15Pin ($r15Mathlib+'Mathlib/MeasureTheory/Function/JacobianOneDim.lean') 'Mathlib.MeasureTheory.Function.JacobianOneDim' 'mathlib_api_source' @('integrableOn_image_iff_integrableOn_abs_deriv_smul','integral_image_eq_integral_abs_deriv_smul')
  Get-R15Pin ($r15Mathlib+'Mathlib/Analysis/Calculus/Deriv/Inv.lean') 'Mathlib.Analysis.Calculus.Deriv.Inv' 'mathlib_api_source' @('HasDerivAt.div')
  Get-R15Pin ($r15Mathlib+'Mathlib/MeasureTheory/Integral/DominatedConvergence.lean') 'Mathlib.MeasureTheory.Integral.DominatedConvergence' 'mathlib_api_source' @('tendsto_integral_of_dominated_convergence')
  Get-R15Pin ($r15Mathlib+'Mathlib/MeasureTheory/Integral/Bochner/Set.lean') 'Mathlib.MeasureTheory.Integral.Bochner.Set' 'mathlib_api_source' @('integral_Icc_eq_integral_Ico')
  Get-R15Pin ($r15Mathlib+'Mathlib/Topology/ContinuousOn.lean') 'Mathlib.Topology.ContinuousOn' 'mathlib_api_source' @('continuousOn_univ','ContinuousOn.comp')
  Get-R15Pin ($r15Mathlib+'Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean') 'Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable' 'mathlib_api_source' @('congr')
)
$evidencePaths = @(
  'docs/source-only/20261102-resume-30r/BRIEF.md'
  'docs/source-only/20261102-resume-30r/DISPATCH.json'
  'docs/source-only/20261102-resume-30q/q03_original_gap_triage/NEXT_DIRECT_PROOF_REVIEW.md'
  'docs/source-only/20261102-resume-30q/h430_descendants/REPORT.md'
  'docs/source-only/20261102-resume-30q/h430_descendants/REGISTRY.json'
  'docs/source-only/20261102-resume-30q/reviews/q26_review_h430.md'
  'docs/source-only/20261102-resume-30p/h430_frozen_q/REPORT.md'
  'docs/source-only/20261102-resume-30p/h430_frozen_q/REGISTRY.json'
  'docs/source-only/20261102-resume-30j/h34/Part5OriginalU34ClampIntegral.lean'
  '.lake/proof-continuation/source-reviews/drafts/20261024z-P5/same-strategy-dictionary/Part5OriginalU34H430Integrable.lean'
  '.lake/proof-continuation/source-reviews/drafts/20261024zz-GitSourceCheckpoint/batch2/snapshot/ImbalancedChen/Part5OriginalU34H430Integrable.lean'
  '.lake/proof-continuation/source-reviews/drafts/20261024zz-GitSourceCheckpoint/batch3/snapshot/ImbalancedChen/Part5OriginalU34H430Integrable.lean'
  '.lake/proof-continuation/source-reviews/drafts/20261024zz-GitSourceCheckpoint/batch4/snapshot/ImbalancedChen/Part5OriginalU34H430Integrable.lean'
  '../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex'
  '../chen-imbalanced-semiprimes/paper/source/modules/global-chen-lower-completion-20261010.txt'
  "$r15Scope/REPORT.md"
  "$r15Scope/BuildRegistry.ps1"
)
$evidence = @($evidencePaths | ForEach-Object {
  $p = Join-Path $r15Root $_
  [ordered]@{path=$_;bytes=(Get-Item -LiteralPath $p).Length;sha256=(Get-FileHash -LiteralPath $p -Algorithm SHA256).Hash.ToLowerInvariant()}
})
$registry = [ordered]@{
  schema_version=1; batch='20261102-resume-30r'; task_number=15; proof_plan_item='D13'
  author_agent='/root/r15_h430_native_weights'; write_scope=$r15Scope
  status='PARTIAL_SOURCE_INCREMENT'; full_target_status='OPEN'; task_complete=$false; local_delivery_complete=$true
  compiled=$false; kernel_verified=$false; formal_credit=0; ready_to_install=$false; finite_guards='UNEVALUATED'
  new_sources=$new; reused_sources=$reuse; mathlib_api_source_pins=$api; governing_evidence=$evidence
  import_resolution='Intended ImbalancedChen module paths; source-only Q/P/O/M dependencies not installed or elaborated by this task.'
  validation_flag_scope='compiled=false/kernel_verified=false on source declarations means no current-task execution or credit; it does not revoke earlier independent production acceptance.'
  eliminated_source_premises=@(
    'Native-x Buchstab image/equality/integrability are derived; no native integral equality or integrability premise is assumed.'
    'Full canonical upperAmplitude is proved bounded/measurable and convergent at actual root queries; no target approximation estimate is assumed.'
    'Full (upperAmplitude-H430)*physical root weight absolute error tends to zero, including the positive-measure clamp.'
    'One common finite mesh/positive tau is constructed for both complete roots before N.'
  )
  remaining_local_premises=@(
    'Native Buchstab identities require positive physical residual, positive inherited ceiling and directionGuard; lower s=2 is allowed.'
    'Native upper descendant integral convergence requires ideal Member and rootBand, but no frozen Member.'
    'Fine-mesh full frozen root integrability requires 0<=tau<=1/12 and meshError<=11/384, all derived eventually in the convergence conclusion.'
  )
  remaining_obligations=@(
    'Full Member filters, joint measurability, same-native-x L1 symmetric differences and full parent-variable integration.'
    'W1/W2 singleton/pair native measure transformations and original label multiplicities.'
    'Moving lower s=2 admission and equality/inherit treatment beyond the one-parent exact identity.'
    'Actual arithmetic C(BN)/(phi(B)*log(Q/B)) Theta law and zero-Theta absolute handling.'
    'Normalized all-action norm12, immutable seed-only430 predecessor history and common 441-generation realization.'
    'Arithmetic root/descendant count licences, source-only import installation, Lean elaboration and kernel verification.'
  )
  not_claimed=@('same-native-x global L1','arithmetic Theta equality','normalized norm12','full Member domain','whole D13 closure','manuscript counterexample','formal verification credit')
  classification=[ordered]@{supplied='II: actual local omitted analysis in source';expression='I: uncompiled API/elaboration risk';remaining_full_family='III: potentially substantive construction gap, not a counterexample'}
  deduplication=[ordered]@{
    local_scope=@('ImbalancedChen','all docs/source-only','ignored .lake/proof-continuation/source-reviews/drafts')
    hidden_hits=@('20261024z-P5/same-strategy-dictionary/Part5OriginalU34H430Integrable.lean','20261024zz-GitSourceCheckpoint/batch2-4/snapshot/ImbalancedChen/Part5OriginalU34H430Integrable.lean')
    remote_revision='09b97db5764ade1246bfb77206baa1b124760958'; remote_repository='subfish-zhou/goldbach-lean'
    remote_raw_probe='https://raw.githubusercontent.com/subfish-zhou/goldbach-lean/09b97db5764ade1246bfb77206baa1b124760958/ImbalancedChen/Part5OriginalU34H430Integrable.lean'
    remote_raw_result='HTTP404; path unverified, no absence inference'; remote_tree_result='GitHub unauthenticated API rate limit'; remote_scan_complete=$false
    remote_bytes_used=$false; actual_evidence='Exact readable local production/source-only files and actual UNC Mathlib bytes.'
  }
  independent_review=[ordered]@{agent='/root/r28_review_h430';status='local mathematical/API source review reported; final reviewer metadata pending';kernel_credit=$false}
  static_checks=[ordered]@{compiler_invocations=0;guard_evaluations=0;numerical_replays=0;ci_dispatches=0;git_mutations=0;child_agents_spawned=0;production_or_old_files_modified=$false;forbidden_source_tokens=@();metadata_only_script='BuildRegistry.ps1'}
}
$target = Join-Path $r15Root "$r15Scope/REGISTRY.json"
[IO.File]::WriteAllText($target, ($registry | ConvertTo-Json -Depth 30)+[Environment]::NewLine, [Text.UTF8Encoding]::new($false))
[pscustomobject]@{new_files=$new.Count;new_declarations=@($new | ForEach-Object {$_.declarations}).Count;reused_files=$reuse.Count;mathlib_files=$api.Count;registry_sha256=(Get-FileHash -LiteralPath $target -Algorithm SHA256).Hash.ToLowerInvariant()} | ConvertTo-Json
