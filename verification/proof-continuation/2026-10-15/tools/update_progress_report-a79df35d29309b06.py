from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / 'verification/proof-continuation/2026-10-15'
manifest = json.loads((DEST / 'manifest.json').read_text(encoding='utf-8'))
candidates = json.loads((DEST / 'unaccepted-candidates.json').read_text(encoding='utf-8'))
path = ROOT / 'docs/PROOF_CONTINUATION_2026-10-15.md'
text = path.read_text(encoding='utf-8')
descriptions = {
    'Part3CommonPoisson': 'Actual common smooth progression to integer lattice, Schwartz Poisson and the full nonzero-frequency remainder, retaining the true complex labels and V/U',
    'ActualExtendedThirdDyadicCoverage': 'Actual dyadic ownership, unique retained coverage away from the displayed stopping strip and uniform fine-grid bounds',
    'CurrentChenRosserEndpointDictionary': 'Exact actual initial-sieve product, nu=1/phi, Euler product and ceil-level dictionary; uniform genuine Mertens local bound',
    'CurrentChenRosserLowerRectangle': 'Uniform canonical AllDepth lower estimate on the actual initial sieve; rounding, sourceSigma and adaptive-depth error paid',
    'CurrentChenFixedEulerNormalization': 'Actual target-prime-deleted Euler product at fixed positive power cutoff has the genuine 2 exp(-gamma)/a normalized limit',
    'CurrentChenPairDensity': 'Uniform one-sided normalized density bound for every genuine rounded fifth-row level',
    'CurrentChenUpsilon5OrdinaryMean': 'Actual fifth-row ordinary count mean with the genuine moving harmonic integral and complete BV/centre payment',
    'Part3ComplexCRTConsumer': 'Actual complex W becomes a constructed lcm CRT progression, with incompatible/inactive labels and the primitive-centre V/U retained',
    'Part3ComplexCRTFiniteFourier': 'Same common finite source split into the actual mass/lcm zero mode and complete nonzero Fourier term, retaining V/U',
    'Part3CommonSmoothCutoff': 'One genuine smooth bump, Schwartz Fourier decay and its actual medium-atom common smooth Cauchy consumer',
    'ActualExtendedThirdIdealCap': 'Literal eight-branch/pair-gated ideal cap: measurability and finite vanishing noncompact canonical tail',
    'ActualExtendedThirdOrderedIntegral': 'Actual clamped correction kernel: measurability, Fin-3 Tonelli to nested integration, integrability and real integral identification',
    'ActualExtendedThirdClosedIntegral': 'Actual affine diagonal null wall pays the closed ordered domain; old-cube equality is paid by the clamped lower factor',
    'ActualExtendedThirdPhysicalCell': 'Literal closed ordered robust Gamma cells: retention/transition walls, two whole-cell pair gates, ideal domination and uniform small-z margin',
    'CurrentChenInitialRosserRemainder': 'Actual initial count above the same Rosser density with complete ordinary BV and centre errors paid',
    'CurrentChenOrdinaryInitialMean': 'Actual initial ordinary mean at full Q+1 level for every fixed 0<a<1/4, using canonical f at the genuine ratio 1/(2a)',
    'CurrentChenOrdinaryInitialLedger': 'The first two actual current Upsilon rows receive their full ordinary means at the original current cutoffs',
    'CurrentChenUpsilon6OrdinarySource': 'Literal corrected inner sixth selector and actual quotient counts, with only nonnegative counts dropped and E=False scope retained',
    'CurrentChenUpsilon6FiniteMean': 'One BV exponent pays all errors for every actual sixth-row subselector chosen after N, retaining the full physical moduli and row coefficients',
    'CurrentChenUpsilon6OrdinaryMean': 'Actual unmasked sixth-row ordinary mean: fixed-buffer arithmetic limit followed by the proved buffer-removal integral limit',
}
marker = 'These thirteen modules contain **266 complete owned declarations**, including\nprivate and generated declarations. The count is an inventory size, not\n266 independent major mathematical theorems.'
assert marker in text, 'This updater applies once to the original checkpoint report'
rows = []
for name, description in descriptions.items():
    module = 'ImbalancedChen.' + name
    if module not in manifest['modules']:
        continue
    count = manifest['modules'][module]['declarations']
    rows.append(f'| `{name}` | {description} | Strict compilation; original-object stock kernel replay; complete {count}-declaration types, inventory and transitive axiom audit |')
text = text.replace('\n\n' + marker, '\n' + '\n'.join(rows) + '\n\n' + marker)
n, d = len(manifest['modules']), manifest['declaration_count']
text = text.replace(marker, f'These {n} modules contain **{d} complete owned declarations**, including\nprivate and generated declarations. The count is an inventory size, not\n{d} independent major mathematical theorems.')
begin = text.index('## Candidates that must not be counted as completed proofs')
end = text.index('## External work reused', begin)
section = f'''## Candidates that must not be counted as completed proofs

The {len(candidates['candidates'])} unaccepted source candidates are listed with exact source
hashes in `verification/proof-continuation/2026-10-15/unaccepted-candidates.json`.
They are excluded from the accepted module/declaration inventory above.
Original failed attempts remain failures; replacement sources need their own checks.

'''
for module, entry in candidates['candidates'].items():
    section += f"* `{module.removeprefix('ImbalancedChen.')}`: {entry['note']}\n"
section += '''
The ordinary lower means above are baseline means. They do not prove the
manuscript's stronger causal h248 contribution, complete eleven-term lower
ledger, or adopted numerical constant. The sixth-row finite payment permits
every actual subselector but does not identify a deletion mask or justify
replacing the arithmetic N limit by a buffer limit.

The actual ideal cap, ordered integral and robust cell inequalities are
separate steps. Physical ownership, the actual branch/action licenses,
fine-grid coverage, robust Gamma convergence to A, and the same-policy
arithmetic count mean are still required for hUpper.

The complex CRT and finite Fourier identities do not prove the common
Poisson completion, reciprocal-phase dictionary, zero-mode cancellation,
aggregate gcd estimates or strong physical distribution bound. The fixed
smooth cutoff, when accepted, only pays its displayed smoothing and rapid
decay statements. The pointwise Buchstab comparison does not pay actual
arithmetic parent licensing or the full mean-value passage.

'''
text = text[:begin] + section + text[end:]
text = text.replace('All approved compiler/checker processes had terminated at this checkpoint.', 'The compiler/checker owner serializes all heavy work through slot zero;\nsource and proof work continue independently between those jobs.')
text = text.replace('1. Compile and replay the actual U5 mean chain, resolving its old import\n   resource obstruction without changing the required analytic statement.', '1. Complete the remaining actual ordinary/causal lower means with their\n   genuine row coefficients and physical remainder budgets.')
text = text.replace('No dependency pin, proof checker, analytic axiom or theorem premise was\nweakened to obtain a pass.', '''No dependency pin, proof checker, analytic axiom or theorem premise was
weakened to obtain a pass.

The new initial-sieve density route removes the unrelated B8/aggregate
Mathlib path while retaining the same actual product, nu=1/phi and ceil L.
Its full advisory source-DAG comparison removes 4851 foreign modules.
The initial remainder route similarly removes 4841 foreign modules and
pays its AP budget directly with singularNormalization_lower. These are
source-import analyses, not independent external-object replay claims.''')
path.write_text(text, encoding='utf-8', newline='\n')
print(json.dumps({'modules': n, 'declarations': d, 'candidates': len(candidates['candidates'])}))
