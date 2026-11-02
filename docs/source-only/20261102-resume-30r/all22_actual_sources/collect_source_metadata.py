"""Record source bytes/declarations only; never run a proof or numeric producer."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BODY = ROOT.parent / 'chen-imbalanced-semiprimes/paper/source/manuscript-body.tex'
UPPER = ROOT.parent / 'chen-imbalanced-semiprimes/paper/source/modules/global-positive-upper-completion-20261010.txt'
CATALOG = ROOT.parent / 'chen-imbalanced-semiprimes/verification/data/global-selected-numeric-completion-20261010.json'

def record(path, role):
    path = Path(path)
    if not path.is_absolute():
        path = ROOT / path
    raw = path.read_bytes()
    try:
        rel = path.relative_to(ROOT).as_posix()
    except ValueError:
        rel = path.as_posix()
    out = {'path': rel, 'absolute_path': path.as_posix(), 'role': role,
           'bytes': len(raw), 'raw_sha256': hashlib.sha256(raw).hexdigest()}
    if path.suffix == '.lean':
        lines = raw.decode('utf-8-sig').splitlines()
        out['intended_module'] = 'ImbalancedChen.' + path.stem
        out['intended_install_path'] = 'ImbalancedChen/' + path.name
        out['direct_imports'] = [s[7:].strip() for s in lines if s.startswith('import ')]
        out['declarations'] = [
            {'kind': m.group(1), 'name': m.group(2), 'line': n}
            for n, line in enumerate(lines, 1)
            if (m := re.match(r'(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)?(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s(:]+)', line))
        ]
        out['line_count'] = len(lines)
    return out

P = 'docs/source-only/'
NEW = [
 (HERE/'P4AOriginalArchiveFourteenPositivePresieve.lean', 'concrete original bank, actual current-parent full-q source, local positive-w fourteen envelope'),
 (HERE/'P4AOriginalFourteenThirteenCurrentSource.lean', 'original13 source preserves the actual sixth continuation after14; distinct reciprocal and physical unit-weight occurrence Lists'),
]
REUSED = [
 (P+'20261102-resume-30o/adopted87_policy/P5OriginalFourthFifthSourceInputs.lean', 'direct import: actual original fourth/fifth inputs'),
 (P+'20261102-resume-30q/saving16_scope/P2OriginalFourteenCommonScheduleEndpoint.lean', 'direct import: existing ordinary14 Q96 same-schedule endpoint'),
 (P+'20261102-resume-30h/coefficient_physical/P5OriginalCommonPositivePresieve.lean', 'direct import: existing normalization and same-tree presieve API'),
 (P+'20261102-resume-30o/adopted87_policy/provenance/original-fourth/FourthRows17LE.bin', 'actual fourth wire payload; raw bytes only; not decoded or checked here'),
 ('ImbalancedChen/P1OriginalFourthPackedParserCompleteness.lean', 'original full payload parsing semantics'),
 ('ImbalancedChen/P1OriginalFourthIntegerGeometryAdmission.lean', 'actual integer admission implies original Geometry'),
 (P+'20261102-resume-30o/all22_common_history/P4AOriginalCommonArchiveSchedule.lean', 'existing common archive/history schedule'),
 (P+'20261102-resume-30o/all22_common_history/P4AOriginalCausalHistory.lean', 'actual fourth/fifth signed preservation and archive data'),
 (P+'20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedConstructor.lean', 'actual policy5/policy6 and held policy8'),
 (P+'20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedSource.lean', 'independently defined full-q sourceChange'),
 (P+'20261102-resume-30j/saving16_compiler/P2OriginalFourteenSignedParentLedger.lean', 'literal14 policy and independent ordinary/positive-w charge'),
 (P+'20261028-resume-30/coefficient_rosser/P1Pair12RetainedSignedSource.lean', 'full-q signed attachment and stopped-frontier identity'),
 (P+'20261102-resume-30j/density_source/P5OriginalCommonFourthFallbackExcision.lean', 'actual fourth geometry and signed gain separation'),
 (P+'20261102-resume-30i/common4_source/P5OriginalCommonFourthSourceLedger.lean', 'existing original4/5 positive-w integral supplier; not reproved'),
 (P+'20261102-resume-30h/coefficient_physical/P5OriginalArchivePositivePresieveGain.lean', 'existing archive fifth positive-w supplier; not reproved'),
 ('.lake/proof-continuation/source-reviews/drafts/20261025a-P4A/fourth_fifth_ledger/P4AOriginalVariableFifthPhysicalLedger.lean', 'exact hidden source of raw/physical/even definitions; source materialization still needed'),
 ('ImbalancedChen/ActualFirstExitDensityProjection.lean', 'complete actual-tree projection and arbitrary-policy beta reserve'),
 ('ImbalancedChen/ActualNormalizedRhoError.lean', 'actual beta attachment error supplier consumed transitively'),
 ('ImbalancedChen/P2OriginalAscendingEighthCapDictionary.lean', 'original14 literal policy/cap/guard semantics'),
 ('ImbalancedChen/OriginalAscendingThirteenCellOwnership.lean', 'original13 StrictRows, ascendingThird halfspace and original cell semantics; no endpoint reproved'),
 ('ImbalancedChen/FrozenRosserPolicy.lean', 'literal ancestor preservation along every continuation'),
 ('ImbalancedChen/FirstExitHistoricalLevels.lean', 'exact List frontier preservation for later-depth splice'),
 ('ImbalancedChen/FinitePrimeGeometryCore.lean', 'frozenParityRosserPolicy actual test semantics'),
 ('ImbalancedChen/PrimeHistoryLogCoordinates.lean', 'genuine unit-weight frontier supplies actual rough-prime tuple'),
 ('ImbalancedChen/P4AOriginalEighthParentPhysicalLedger.lean', 'actual sixth parent, positive-w slot17/19 source; not full selected13 policy'),
 (P+'20261102-resume-30k/saving19_preservation/P4AOriginalSaving19BankFrontier.lean', 'direct import for second module: actual13 reciprocal-weight selected-list correspondence'),
 (P+'20261102-resume-30k/saving19_preservation/P4AOriginalSaving19BankExhaustion.lean', 'actual original13 bankRegion implies original StrictRows'),
 (P+'20261028-resume-30g/upper_chronology/P4AOriginalLive171819PrimeBank.lean', 'actual original13 bank and reciprocal-prime selected List'),
 (P+'20261028-resume-30g/upper_chronology/P4AOriginalLive171819CommonParent.lean', 'actual point8 logarithmic ancestor coordinates'),
 (P+'20261028-resume-30b/upper_chronology/P4AOriginalCell0HalfOpenPrimeCarrier.lean', 'original half-open actual prime-box definition'),
 (P+'20261102-resume-30m/saving19_owned_integral/P2OriginalSaving19OwnedIntegral.lean', 'existing unconditional original13/28918 analytic endpoint; no new theorem'),
 (P+'20261102-resume-30p/saving16_pulling_ownership/P2Winner9ActualEightSimplexMoment.lean', 'required inherited same-module canonical moment replacement'),
 ('ImbalancedChen/P4AAll22OriginalKLedger.lean', 'existing scalar replacement budget; not actual All22 source'),
 ('ImbalancedChen/P4AAll22ActualCompactPositiveBinding.lean', 'existing four-positive binding; not actual All22 source'),
 (P+'20261102-resume-30p/all22_common_history/P4AOriginalFiniteSignedHistoryRefinement.lean', 'existing same-rho finite signed telescope; not buffered policy'),
 (P+'20261102-resume-30q/reviews/q24_review_saving_geometry.md', 'required independent source boundary'),
 (P+'20261102-resume-30q/reviews/q30_review_history_final.md', 'required independent final boundary'),
 (P+'20261102-resume-30q/saving16_scope/REPORT.md', 'Q08 read before new work'),
 (P+'20261102-resume-30q/saving16_scope/REGISTRY.json', 'Q08 source pins and primitive inputs'),
 (P+'20261102-resume-30q/saving19_instance/REPORT.md', 'Q09 exact reuse conclusion'),
 (P+'20261102-resume-30q/saving19_instance/REGISTRY.json', 'Q09 effective inherited source mapping'),
 (P+'20261102-resume-30r/BRIEF.md', 'batch constraints'),
 (P+'20261102-resume-30r/DISPATCH.json', 'D04 scope and task allocation'),
 (BODY, 'original manuscript lines 371-509 and 1327-1369'),
 (UPPER, 'original source explanation lines 55-127 and 185-281'),
 (CATALOG, 'original22 source directory; endpoint strings copied, not recomputed'),
]

# This is a provenance inventory, not a validation of the quoted values.
catalog = json.loads(CATALOG.read_text(encoding='utf-8-sig'))
roles = {
  1: 'original fourth source; stronger enclosure replaces the prior fourth estimate',
  2: 'old fifth parents: complete parent subdivision replacement',
  3: 'new fifth cover disjoint from old fifth parents',
  4: 'expanded old sixth source replacement',
  5: 'above-mu second fallback; actual pair discrepancies retained in Q',
  6: 'above-mu third fallback on its actual current frontier',
  7: 'same eleven sixth cells: final log bound replaces earlier bound',
  8: 'descending33 sixth source',
  9: 'ascending34 sixth source with actual current parent',
 10: 'descending34 sixth source with actual current parent',
 11: 'lower complement clipping; missing intermediate difference only',
 12: 'lower descending34 complement source',
 13: 'selected local sixth corrections',
 14: 'four nonsingleton sixth cells counted at eighth-family stage once',
 15: 'original eighth radial same-domain maximum replaces old estimate',
 16: 'fourteen new ascending eighth cells; actual local positive-w envelope in R06',
 17: 'fifteen descending eighth cells',
 18: 'fifteen unequal eighth cells: final log bound replaces previous one',
 19: 'original thirteen third-minorant cells: existing M selectedSaving endpoint',
 20: 'twentynine first-failure cells: final log bound replaces previous one',
 21: 'same 11026 winner9 seed: curvature increment over adopted log only',
 22: 'same 11026 winner9 seed: mixed increment over adopted curvature only',
}
entries = []
for slot, entry in enumerate(catalog['selected_upper_direct_savings'], 1):
    entries.append({
        'slot_one_based': slot, **entry,
        'accounting_role': roles[slot],
        'source_artifact': record(CATALOG.parent / entry['source'], 'quoted original source; no numeric replay'),
        'all22_same_policy_correspondence_supplied': False,
        'r06_progress': {
          1: 'concrete original bank and attached signed fourth increment; full original numerical/analytic licence remains open',
          2: 'concrete original fifth archive and attached signed increment, counted once; actual fifth debts remain open',
          3: 'same actual fifth archive; no new whole-domain debt supplier',
          16: 'actual local original-bank common schedule, current-parent full-q source, and positive-w envelope',
          19: 'original13 strict bank separates from14; same current6 full signed continuation, reciprocal List and distinct physical unit-weight full-q List; arithmetic endpoint conversion remains open',
        }.get(slot, 'reuse/source audit only'),
    })

source_map = {
 'scope': 'Original22 provenance and accounting roles only; not an All22 instance or endpoint validation',
 'catalog': record(CATALOG, 'read-only original catalog'),
 'numerical_evaluation': False, 'finite_guards_status': 'UNEVALUATED',
 'entries': entries,
}
(HERE/'ALL22_SOURCE_MAP.json').write_text(json.dumps(source_map, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')

registry = {
 'schema_version': 1, 'batch': '20261102-resume-30r', 'task': 'R06', 'proof_plan_item': 'D04',
 'owner': '/root/r06_all22_actual_sources', 'write_scope': HERE.relative_to(ROOT).as_posix(),
 'status': 'SOURCE_ONLY_CONCRETE_BANK_POSITIVE14_AND_ORIGINAL13_CURRENT_SOURCE_SUPPLIED',
 'full_target_status': 'OPEN', 'compiled': False, 'kernel_verified': False, 'formal_credit': 0,
 'finite_guards_status': 'UNEVALUATED_INHERITED_NO_NEW_FINITE_GUARDS',
 'new_lean_sources': [record(path, role) for path, role in NEW],
 'new_assumptions': [], 'assumed_endpoint_estimates': [], 'new_axioms': [],
 'actually_eliminated_premises': [
   'Primitive rows4 argument: replaced by O originalRows4 from unchanged FourthRows17LE.bin.',
   'Primitive licensed4 argument: replaced by O originalAdmission4 integer geometry admission.',
   'Caller FourthGeometry: derived by originalAdmission4_geometry.',
   'Caller local positive-w density or beta estimate: whole-tree projection and actual beta supplier used directly.',
   'Caller current-parent/source identity: independently defined attached occurrence-list source identified with actual physical difference.',
   'Assumed original13/fourteen source separation: opposite strict halfspaces prove literal fourteen inheritance on actual original13 bank.',
   'Assumed unchanged original13 continuation: actual rank-eight ancestor and every later signed decision preserve current policy6 after14.',
   'Assumed primality/target exclusion of physical source: derived from actual unit-weight frontier, preserving original prime-bank selection.',
 ],
 'remaining_dependencies': [
   'All22 endpoint sources on one actual full87 policy, including complete sixth stages and exact chronological stage binding.',
   'Positive-w selected13 arithmetic/current-parent endpoint conversion; M analytic selectedSaving endpoint already exists.',
   'Original fourth filter does not prove all stored rows pass or every original analytic licence.',
   'Full buffered policy and mixed-cell compiler, complete support/PP and all reserve totals.',
   'Original fifth old-branch defect and actual64 reserve; catalog5 full-domain errors remain peer duties.',
   'Inherited exact-source materialization, finite guards and complete import-chain kernel acceptance.',
 ],
 'budget_accounting': {'ordinary_local_error': 'eta/2', 'beta_local_error': 'eta/2',
   'total_local_error': 'eta', 'compiler_payment': 'none', 'global_density_payment': 'none',
   'warning': 'Beta is one local envelope expenditure, not another independent debit to add to R09/R10.'},
 'quantifier_order': 'nu,eta,betaMax -> beta,n,e0 -> e,omega -> q,N0 -> N,cap',
 'physical_cutoffs': {'z': 'N^(19/96)', 'w': 'N^(nu*beta^2)', 'L': 'N^(nu*beta)',
                      'q96': '1222997719565324892497827/2^96', 'parent': 'policy6(data e q omega)',
                      'normalization': 'log(N)/singularSeries(N)'},
 'original13_source': {
   'strict_separation': 'original13 t1+t2<mu excludes original14 mu<t1+t2',
   'old_current': 'policy6(data e q omega)',
   'later_policy': 'fourteenPolicy e q omega',
   'reciprocal_carrier': 'existing selected (.ascending19 i); h(p)=1/(p-1)',
   'physical_carrier': 'originalThirteenPhysicalList; h(p)=1; same bankRegion/primeBox and List multiplicity',
   'full_modulus_test': 'attachedLeafTest N cap 1 w L G; arbitrary G and w,z,L',
   'new_thirteen_policy_defined': False,
   'arithmetic_endpoint_supplied': False,
 },
 'peer_results_consumed': [],
 'reused_sources': [record(path, role) for path, role in REUSED],
 'source_map': record(HERE/'ALL22_SOURCE_MAP.json', '22 original source records; no mathematical validation'),
 'metadata_script': record(Path(__file__).resolve(), 'hashes and textual declaration inventory only'),
 'transitive_import_closure_verified': False,
 'validation': ['source/API inspection', 'raw SHA256', 'JSON serialization and declaration/import line extraction'],
 'prohibited_operations_performed': [],
}
if (HERE/'REPORT.md').exists():
    registry['report'] = record(HERE/'REPORT.md', 'final scope/remaining obligation report')
(HERE/'REGISTRY.json').write_text(json.dumps(registry, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
print(json.dumps({'new_sources': {r['path']:r['raw_sha256'] for r in registry['new_lean_sources']},
                  'reused_files': len(REUSED), 'catalog_entries': len(entries),
                  'compiled': False, 'finite_guards': 'UNEVALUATED'}))
