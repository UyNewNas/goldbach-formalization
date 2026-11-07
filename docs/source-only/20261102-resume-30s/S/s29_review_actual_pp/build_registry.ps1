$ErrorActionPreference = 'Stop'
$repoRoot = 'E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation'
$reviewRoot = Join-Path $repoRoot 'docs/source-only/20261102-resume-30s/S/s29_review_actual_pp'
$records = @(
  @('docs/source-only/20261102-resume-30s/BRIEF.md','assignment'),
  @('../1_+_1.748_lean_proofs/main.md','initial_tracker'),
  @('../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex','original_manuscript'),
  @('../chen-imbalanced-semiprimes/paper/source/modules/distribution-prime-product-completion-20261010.txt','original_PP_applicability'),
  @('../chen-imbalanced-semiprimes/paper/source/modules/distribution-coefficient-completion-20261010.txt','original_coefficient_applicability'),
  @('../chen-imbalanced-semiprimes/paper/source/modules/final-classical-input-correspondence-20261010.txt','original_primary_correspondence'),
  @('../goldbach-research/external-source-audit-20261009/pascadi-2404.04239v3-classical-spectral-inputs-20261009.txt','primary_A_and_J_read_512_556_2886_2943'),
  @('../goldbach-research/external-source-audit-20261009/assing-blomer-li-2005.13915v1-large-a-20261009.txt','primary_ABL_read_575_1010'),
  @('ImbalancedChen/Part3DistributionTargets.lean','actual_target_definitions'),
  @('ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean','actual_upper_consumer_full_read'),
  @('ImbalancedChen/P5OriginalFixedDensitySupplierAssembly.lean','actual_lower_consumer_full_read'),
  @('ImbalancedChen/P5U7OriginalSourceSuppliedRoute.lean','actual_U7_consumer_full_read'),
  @('ImbalancedChen/P5U7OriginalPhysicalPP.lean','actual_U7_source'),
  @('ImbalancedChen/P5zUpsilon8OriginalSlot.lean','actual_U8_consumer'),
  @('ImbalancedChen/CurrentChenUpsilon8SharpKPhysicalPP.lean','actual_U8_source'),
  @('ImbalancedChen/CurrentChenP5U9OrderedPhysicalPP.lean','actual_U9_source'),
  @('ImbalancedChen/P5ZU1011SameRhoSmoothMainApproximation.lean','existing_U1011_main_approximation'),
  @('docs/source-only/20261102-resume-30r/reviews/r29_review_gamma_pp.md','inherited_independent_full_R17_R19_review'),
  @('docs/source-only/20261102-resume-30r/gamma_outer_theta/REPORT.md','R17_report_full_read'),
  @('docs/source-only/20261102-resume-30r/gamma_outer_theta/REGISTRY.json','R17_registry_metadata'),
  @('docs/source-only/20261102-resume-30r/gamma_outer_theta/P2GammaPairThetaZero.lean','R17_zeroTheta_full_read'),
  @('docs/source-only/20261102-resume-30r/gamma_grid_level/REPORT.md','R18_report_full_read'),
  @('docs/source-only/20261102-resume-30r/gamma_grid_level/REGISTRY.json','R18_registry_metadata'),
  @('docs/source-only/20261102-resume-30r/actual_same_rho_pp/REPORT.md','R19_report_full_read'),
  @('docs/source-only/20261102-resume-30r/actual_same_rho_pp/REGISTRY.json','R19_registry_metadata'),
  @('docs/source-only/20261102-resume-30r/actual_same_rho_pp/P4BActualUpperRoughPrimeReserveZero.lean','R19_source_full_read'),
  @('docs/source-only/20261102-resume-30r/actual_same_rho_pp/P4BActualUpperModesRoughPrimePaid.lean','R19_source_full_read'),
  @('docs/source-only/20261102-resume-30h/certificate_triple/P2OriginalU5SmallPartnerRootPayment.lean','actual_rootQ_and_residual_read'),
  @('docs/source-only/20261028-adopted-query/P2OriginalPairRootActualQuery.lean','actual_per_root_Q_dictionary_read'),
  @('docs/source-only/20261102-resume-30k/upper_fourier_tail/P4BOriginalUpperFourierTailPaid.lean','K_full_tail_223_326_direct_read'),
  @('docs/source-only/20261028-resume-30c/transfer_power/P5ProperPowerPhysicalPolynomialPayment.lean','exact_signedRow_dependency_read'),
  @('docs/source-only/20261028-resume-30f/transfer_lambda/P5OriginalSingletonLowerTrimPaid.lean','exact_originalLowerCut_dependency_read'),
  @('docs/source-only/20261028-resume-30e/transfer_power/P5ActualCommonRefinedRange.lean','exact_policy8_range_full_read'),
  @('docs/source-only/20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedConstructor.lean','exact_OriginalData_constructor_full_read'),
  @('docs/source-only/20261102-resume-30r/uniform_seven32/REPORT.md','R24_report_full_read'),
  @('docs/source-only/20261102-resume-30s/S/s19_actual_upper_pp/P4BActualUpperTrimPayment.lean','S19_independent_source_review'),
  @('docs/source-only/20261102-resume-30s/S/s19_actual_upper_pp/P4BCommonRefinedUpperTailAndTrim.lean','S19_independent_source_review'),
  @('docs/source-only/20261102-resume-30s/S/s19_actual_upper_pp/REPORT.md','S19_frozen_report_independently_read'),
  @('docs/source-only/20261102-resume-30s/S/s19_actual_upper_pp/REGISTRY.json','S19_frozen_registry_38_new_reuse_hashes_matched'),
  @('docs/source-only/20261102-resume-30s/S/s24_actual_lower_pp/P5OriginalU789SmoothLogSources.lean','S24_independent_source_review'),
  @('docs/source-only/20261102-resume-30s/S/s24_actual_lower_pp/P5OriginalU789SmoothChartRoughOne.lean','S24_independent_source_review'),
  @('docs/source-only/20261102-resume-30s/S/s24_actual_lower_pp/REPORT.md','S24_frozen_report_independently_read'),
  @('docs/source-only/20261102-resume-30s/S/s24_actual_lower_pp/REGISTRY.json','S24_frozen_registry_metadata'),
  @('docs/source-only/20261102-resume-30s/S/s22_actual_spectral_energy/Part3OriginalUniformTestCutoffBudget.lean','S22_cross_review_actual_export_type'),
  @('docs/source-only/20261102-resume-30s/S/s22_actual_spectral_energy/REPORT.md','S22_frozen_report_independently_read'),
  @('docs/source-only/20261102-resume-30s/S/s22_actual_spectral_energy/REGISTRY.json','S22_frozen_registry_metadata')
)
$evidence = foreach ($record in $records) {
  $absolute = [IO.Path]::GetFullPath((Join-Path $repoRoot $record[0])).Replace('\','/')
  $item = Get-Item -LiteralPath $absolute
  $lines = [IO.File]::ReadAllLines($absolute)
  $entry = [ordered]@{
    path = $record[0]
    absolute_path = $absolute
    role = $record[1]
    bytes = $item.Length
    lines = $lines.Count
    raw_sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $absolute).Hash.ToLowerInvariant()
  }
  if ($item.Extension -eq '.lean') {
    $entry.intended_module = 'ImbalancedChen.' + $item.BaseName
    $imports = @()
    $decls = @()
    for ($idx = 0; $idx -lt $lines.Count; $idx++) {
      if ($lines[$idx] -match '^import\s+(\S+)') {
        $imports += [ordered]@{module=$Matches[1];line=$idx+1}
      }
      if ($lines[$idx] -match '^(?:(?:private|protected|noncomputable)\s+)?(theorem|lemma|def|abbrev|structure)\s+([^\s:{(]+)') {
        $decls += [ordered]@{kind=$Matches[1];name=$Matches[2];line=$idx+1;header=$lines[$idx]}
      }
    }
    $entry.direct_imports = $imports
    $entry.declarations = $decls
  }
  $entry
}
$reportPath = Join-Path $reviewRoot 'REPORT.md'
$registry = [ordered]@{
  task = 'S29 independent actual upper/lower same-rho PP review'
  status = 'FROZEN_INDEPENDENT_PUBLICATION_CHECKPOINT_FULL_SCOPE_HOLD'
  whole_assigned_yellow_scope_source_complete = $false
  green_recommendation = $false
  compiled = $false
  kernel_verified = $false
  formal_credit = 0
  finite_proof_bodies = 'UNEVALUATED'
  pins = [ordered]@{
    lean = 'leanprover/lean4:v4.33.0-rc1'
    mathlib = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
    native = 'subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958'
    public_parent = 'e2a05f73d5f169fff847d72dcfcc66ec54ad4f87'
    public_tree = '43e3384e7178e05b66ac347c7f6321d89679dc45'
  }
  exact_upper_terminal = 'ImbalancedChen.P4BCurrentSmoothBadUpperSuppliers.current_realBad_upper_of_actual_density_and_uniform_smooth_PP / hUniformPP'
  upper_quantifier_order = 'delta>0; fixed legal width; A>0; exists C>0,N0; all N>=N0 even; all family members (Unit)'
  exact_lower_terminal = 'ImbalancedChen.P5OriginalCoefficientArithmetic.eventual_D12_of_fixed_original_grouped_suppliers / h7,h8,h9,h1011'
  final_premises_removed = [ordered]@{hUniformPP=0;hdensity=0;h7=0;h8=0;h9=0;h1011=0;actual_7_32_energy=0}
  remaining = @(
    'selected causal rootLabels/rootQ to genuine common-Q positive family binding',
    'positive-Theta relative error and full joint lower/order payment',
    'actual final full87 buffered coefficient identity with supplied support policy',
    'same integer enhanced whole-atom factorization with all full/selected squares and restoring scalars',
    'all physical low-rank classes and extra coupled Fourier/Mellin costs',
    'actual proper powers and full retained medium/low-rank/one-long/two-long modes',
    'actual normalized trace/A/J/regular/gap/full-class energy and zero budgets',
    'lower U7/U8/U9 quantitative physical Euler/Fourier, positive-main approximation or hard-source centre and boundary payment',
    'original U1011 joint raw source distribution supplier',
    'actual density and remaining original four lower groups (other reviewers)',
    'remote same-source elaboration, kernel and expanded-type/axiom evidence'
  )
  report = [ordered]@{
    path = 'docs/source-only/20261102-resume-30s/S/s29_review_actual_pp/REPORT.md'
    raw_sha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $reportPath).Hash.ToLowerInvariant()
    bytes = (Get-Item -LiteralPath $reportPath).Length
  }
  evidence = @($evidence)
  validation = [ordered]@{
    source_text_reads = $true
    metadata_only_registry_generation = $true
    compiler_invoked = $false
    proof_guard_invoked = $false
    numerical_replay = $false
    ci_dispatched = $false
    git_or_remote_mutation = $false
    author_edits = $false
    children_spawned = $false
    quota_usage_credit_tools = $false
  }
}
$utf8NoBom = [Text.UTF8Encoding]::new($false)
[IO.File]::WriteAllText((Join-Path $reviewRoot 'REGISTRY.json'), ($registry | ConvertTo-Json -Depth 15), $utf8NoBom)
Get-FileHash -Algorithm SHA256 -LiteralPath $reportPath,(Join-Path $reviewRoot 'REGISTRY.json') | Select-Object Path,Hash | ConvertTo-Json
