python3 -B - <<'PY'
from pathlib import Path
import hashlib
import json
import re
import subprocess

# Root must replace these five placeholders only after the new ChildGap stage
# has its original accepted RESULT and independent acceptance evidence.
source = '9aa63b9a82b25f03ea12f622a718aafb65d551cb'
child_spec = {
    'path': '/workspace/p1-complete-proof/20261125-p14-continuation/child-gap-continuity-moment-retry/9aa63b9a82b25f03ea12f622a718aafb65d551cb/runs/attempt-00000/RESULT.json',
    'sha256': 'a1b842177051bb3b7888a63ef9e0d4d2b9e8a9ba22fe1c9bb0145ac8f182d974',
    'stage': 'child-gap-continuity-moment-retry',
    'source_sha256': 'db8f9720be3396e1f01df1a27d20ac754193f2106d5a686b6c0f37e6c898818a',
}
assert re.fullmatch(r'[0-9a-f]{40}', source), 'fill the published accepted ChildGap source commit'
assert re.fullmatch(r'[0-9a-f]{64}', child_spec['sha256']), 'fill the raw original ChildGap RESULT hash'
assert re.fullmatch(r'[0-9a-f]{64}', child_spec['source_sha256']), 'fill the accepted ChildGap source hash'
assert re.fullmatch(r'[a-z0-9-]+', child_spec['stage']), 'fill the exact accepted ChildGap stage'
child_path = Path(child_spec['path'])
assert str(child_path.parent.parent.parent) == str(
    Path('/workspace/p1-complete-proof/20261125-p14-continuation') / child_spec['stage'] / source)
assert child_path.name == 'RESULT.json' and child_path.parent.parent.name == 'runs'
assert re.fullmatch(r'attempt-[0-9]{5}', child_path.parent.name)

config = {'stage_specs': [{'stage': 'pointwise-q-namespace-retry',
                  'requirements': ['ImbalancedChen.P5OldFifthChildGapIntegral'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/pointwise-q-namespace-retry.json',
                  'manifest_sha256': '719955a7ec430fddb79c3aa22371d3fa4df92884a75181a350f3b6b77ad8bbdd',
                  'module': 'ImbalancedChen.P5OldFifthPointwiseQ',
                  'path': 'ImbalancedChen/P5OldFifthPointwiseQ.lean',
                  'preimage_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                  'before_sha256': 'b2b1e89fee01dca52b6136250f4c20238cb564ea8f6691924a7fe3480b72e7d3',
                  'after_sha256': '990c9e369323a762eb11b9f2f27cd422d3b3f96ed02b81db1febc54f7132e682',
                  'project_imports': ['ImbalancedChen.P5OldFifthChildGapIntegral',
                                      'ImbalancedChen.ActualRosserLowerLimit']},
                 {'stage': 'named-payload-semantics',
                  'requirements': ['ImbalancedChen.P1FifthNamedParentActualIntegral',
                                   'ImbalancedChen.P5OldFifthChildGapIntegral',
                                   'ImbalancedChen.P5OldFifthPointwiseQ'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/named-payload-semantics.json',
                  'manifest_sha256': '861e78f8151a011a27bd0d2854b39406e0f7173ac4252daf3ad3fa1af8faca21',
                  'module': 'ImbalancedChen.P5NamedFifthPayloadSemantics',
                  'path': 'ImbalancedChen/P5NamedFifthPayloadSemantics.lean',
                  'preimage_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'before_sha256': '1dacad69cfc323d83ded2908acfb90a57b981010244ddf04a9801c009143244c',
                  'after_sha256': '1dacad69cfc323d83ded2908acfb90a57b981010244ddf04a9801c009143244c',
                  'project_imports': ['ImbalancedChen.P1FifthNamedParentActualIntegral',
                                      'ImbalancedChen.P5OldFifthChildGapIntegral',
                                      'ImbalancedChen.P5OldFifthPointwiseQ']},
                 {'stage': 'named-all-children',
                  'requirements': ['ImbalancedChen.P5NamedFifthPayloadSemantics'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/named-all-children.json',
                  'manifest_sha256': '5dd0e904c6b693dfc22c9ba3c8cf82b2c07c51db022016a534bc7256fe5cca97',
                  'module': 'ImbalancedChen.P5NamedFifthAllChildren',
                  'path': 'ImbalancedChen/P5NamedFifthAllChildren.lean',
                  'preimage_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'before_sha256': '357a26fd1b6e24d0f6aa5a651384012ec800711778bb251885c2d2c4f29f8bfe',
                  'after_sha256': '357a26fd1b6e24d0f6aa5a651384012ec800711778bb251885c2d2c4f29f8bfe',
                  'project_imports': ['ImbalancedChen.P5NamedFifthPayloadSemantics']},
                 {'stage': 'named-child-specific-ratio',
                  'requirements': ['ImbalancedChen.P5NamedFifthAllChildren'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/named-child-specific-ratio.json',
                  'manifest_sha256': 'fffcb1196c6603bdddf4867948576dc6355c4b12ccae009f718dc3a36383b215',
                  'module': 'ImbalancedChen.P5NamedFifthChildSpecificRatio',
                  'path': 'ImbalancedChen/P5NamedFifthChildSpecificRatio.lean',
                  'preimage_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'before_sha256': '5377f9724f6051056eddae1faf8059fe3cb8a3bbb6b65ff2afa7bec08187a29f',
                  'after_sha256': '5377f9724f6051056eddae1faf8059fe3cb8a3bbb6b65ff2afa7bec08187a29f',
                  'project_imports': ['ImbalancedChen.P5NamedFifthAllChildren']},
                 {'stage': 'sharp-directed-log',
                  'requirements': ['ImbalancedChen.P5OldFifthPointwiseQ'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/sharp-directed-log.json',
                  'manifest_sha256': 'a302e633bf1e25cf8fc92bd20a0f59cbe57ce4b60da329446d65df531bc77417',
                  'module': 'ImbalancedChen.P5OriginalSharpDirectedLog',
                  'path': 'ImbalancedChen/P5OriginalSharpDirectedLog.lean',
                  'preimage_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'before_sha256': '8d50207ff413c917a6842a48b3fc5d3783d3674a1f0ee7ea50fbab484e466801',
                  'after_sha256': '8d50207ff413c917a6842a48b3fc5d3783d3674a1f0ee7ea50fbab484e466801',
                  'project_imports': ['ImbalancedChen.P5OldFifthPointwiseQ']},
                 {'stage': 'first-f-concavity-namespace-retry',
                  'requirements': ['ImbalancedChen.P5OldFifthPointwiseQ'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/first-f-concavity-namespace-retry.json',
                  'manifest_sha256': '72965d879b539fab7c9e7536fa515b20702b3ad74d69a554e24c73b15e23e16b',
                  'module': 'ImbalancedChen.P5OldFifthFirstFConcavity',
                  'path': 'ImbalancedChen/P5OldFifthFirstFConcavity.lean',
                  'preimage_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                  'before_sha256': '5d232b9f9261286fbd270f0c49df61547f82a751864d291f2c3b3c4404cac8d1',
                  'after_sha256': '1d8455de700e64d4efe52caefa594dd56a9de09abbe8389272de0ff91a5cfcd3',
                  'project_imports': ['ImbalancedChen.P5OldFifthPointwiseQ']},
                 {'stage': 'child-q-jensen-namespace-retry',
                  'requirements': ['ImbalancedChen.P5OldFifthPointwiseQ',
                                   'ImbalancedChen.P5OldFifthFirstFConcavity'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/child-q-jensen-namespace-retry.json',
                  'manifest_sha256': '22c611107369e90adec71cc0158bff131397443e103444643aac20855d529eb3',
                  'module': 'ImbalancedChen.P5OldFifthChildQJensen',
                  'path': 'ImbalancedChen/P5OldFifthChildQJensen.lean',
                  'preimage_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                  'before_sha256': '93033fd02602c14f1f25934b922f425edeefbc754863785b3856fa33ac2090ba',
                  'after_sha256': '86f76d4b4a645bc02a5cce13a21c37a1f23b284a86255482237b5919d723fed8',
                  'project_imports': ['ImbalancedChen.P5OldFifthPointwiseQ',
                                      'ImbalancedChen.P5OldFifthFirstFConcavity']},
                 {'stage': 'actual-child-jensen-integral',
                  'requirements': ['ImbalancedChen.P5OldFifthFirstFConcavity',
                                   'ImbalancedChen.P5OldFifthChildQJensen',
                                   'ImbalancedChen.P1FifthUnitBoxLiteralGainLower'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/actual-child-jensen-integral.json',
                  'manifest_sha256': '71db90fa71a65ef6310b084afe0a20a867f14bf872ce1bac1f8541770b4fc78f',
                  'module': 'ImbalancedChen.P5OldFifthActualChildJensenIntegral',
                  'path': 'ImbalancedChen/P5OldFifthActualChildJensenIntegral.lean',
                  'preimage_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'before_sha256': '20d47753e58ccfbb4a0d3f7e07232591d1bf08437de44e96ca3b7d47cb0e60eb',
                  'after_sha256': '20d47753e58ccfbb4a0d3f7e07232591d1bf08437de44e96ca3b7d47cb0e60eb',
                  'project_imports': ['ImbalancedChen.P5OldFifthFirstFConcavity',
                                      'ImbalancedChen.P5OldFifthChildQJensen',
                                      'ImbalancedChen.P1FifthUnitBoxLiteralGainLower']},
                 {'stage': 'selected-owner-jensen-reserve',
                  'requirements': ['ImbalancedChen.P5OldFifthActualChildJensenIntegral',
                                   'ImbalancedChen.P1OriginalFifthLiteralKernelModulus',
                                   'ImbalancedChen.P1FifthPositivePartActualOwner'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/selected-owner-jensen-reserve.json',
                  'manifest_sha256': '0fc397ab9cb0f5c6672501c6f573fd86d071634856a8fb92799abc08530bbaa1',
                  'module': 'ImbalancedChen.P5ChildSelectedOwnerJensenReserve',
                  'path': 'ImbalancedChen/P5ChildSelectedOwnerJensenReserve.lean',
                  'preimage_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'before_sha256': 'ce0ceef3202b2186e3b7dfca1c634ea1f966c29970d2d9eee8d1b7f62ae8b5d2',
                  'after_sha256': 'ce0ceef3202b2186e3b7dfca1c634ea1f966c29970d2d9eee8d1b7f62ae8b5d2',
                  'project_imports': ['ImbalancedChen.P5OldFifthActualChildJensenIntegral',
                                      'ImbalancedChen.P1OriginalFifthLiteralKernelModulus',
                                      'ImbalancedChen.P1FifthPositivePartActualOwner']},
                 {'stage': 'named-all-children-selected-jensen',
                  'requirements': ['ImbalancedChen.P5ChildSelectedOwnerJensenReserve',
                                   'ImbalancedChen.P5NamedFifthAllChildren'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/named-all-children-selected-jensen.json',
                  'manifest_sha256': 'f8b5a0c7193eb9829bf16f08fc8b2e938b5df906a76b8f5d48bf9c69e1ed61ef',
                  'module': 'ImbalancedChen.P5NamedAllChildrenSelectedJensen',
                  'path': 'ImbalancedChen/P5NamedAllChildrenSelectedJensen.lean',
                  'preimage_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'before_sha256': '5b886d4be9651e26b794e3c0cad75bb6a0daeca8a68b5588fca6be6adf65cf98',
                  'after_sha256': '5b886d4be9651e26b794e3c0cad75bb6a0daeca8a68b5588fca6be6adf65cf98',
                  'project_imports': ['ImbalancedChen.P5ChildSelectedOwnerJensenReserve',
                                      'ImbalancedChen.P5NamedFifthAllChildren']},
                 {'stage': 'named-q80-floor-soundness',
                  'requirements': ['ImbalancedChen.P5NamedFifthChildSpecificRatio',
                                   'ImbalancedChen.P5OriginalSharpDirectedLog',
                                   'ImbalancedChen.P5NamedAllChildrenSelectedJensen'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/named-q80-floor-soundness.json',
                  'manifest_sha256': 'f8dc444827fcd9aa5935f05cd26cd669be9a6c88be8cd1d762dc1667cc469b50',
                  'module': 'ImbalancedChen.P5NamedFifthQ80FloorSoundness',
                  'path': 'ImbalancedChen/P5NamedFifthQ80FloorSoundness.lean',
                  'preimage_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'before_sha256': '326346be7336aee65f58ff8ee8680e50a48e1ed16704844f5f3eba63def00c58',
                  'after_sha256': '326346be7336aee65f58ff8ee8680e50a48e1ed16704844f5f3eba63def00c58',
                  'project_imports': ['ImbalancedChen.P5NamedFifthChildSpecificRatio',
                                      'ImbalancedChen.P5OriginalSharpDirectedLog',
                                      'ImbalancedChen.P5NamedAllChildrenSelectedJensen',
                                      'ImbalancedChen.P2DirectedLogRounding']},
                 {'stage': 'original-child-integer-wire',
                  'requirements': ['ImbalancedChen.P5NamedFifthQ80FloorSoundness'],
                  'manifest_path': 'docs/p1/20261125/p14-continuation/stages/original-child-integer-wire.json',
                  'manifest_sha256': '2b849b110221f66ae4551073ea31da558e4a8800fdf76de1c73c53f1efe8fbaa',
                  'module': 'ImbalancedChen.P5OriginalChildIntegerWireBinding',
                  'path': 'ImbalancedChen/P5OriginalChildIntegerWireBinding.lean',
                  'preimage_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'before_sha256': 'd57e06adf945a50ad2318667d9816c3b63c74c25e29f1b12e768b90032cdd6bc',
                  'after_sha256': 'd57e06adf945a50ad2318667d9816c3b63c74c25e29f1b12e768b90032cdd6bc',
                  'project_imports': ['ImbalancedChen.P5NamedFifthQ80FloorSoundness']}],
 'prior_specs': [{'path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8237d0b698ca01153a7e2823510cf67148083c0a/PIPELINE_RESULT.json',
                  'sha256': '6629d933bdd7f5baa5d94bab5ba0a46f76c30fb316215be01b149669a957b264',
                  'source_commit': '8237d0b698ca01153a7e2823510cf67148083c0a',
                  'accepted_owners': ['ImbalancedChen.P1FifthUnitBoxLiteralGainLower',
                                      'ImbalancedChen.P1OriginalFifthLiteralKernelModulus',
                                      'ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge']},
                 {'path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json',
                  'sha256': '60173a21ce20a88e58efe21b25ef127df230dfffab014f08cf60aaad38908a01',
                  'source_commit': 'c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b',
                  'accepted_owners': ['ImbalancedChen.P1FifthCheckedUnitBoxWholeGain',
                                      'ImbalancedChen.P1FifthMask5RawOwnerLicence',
                                      'ImbalancedChen.P1FifthMask6RawOwnerLicence',
                                      'ImbalancedChen.P1FifthPositivePartActualOwner',
                                      'ImbalancedChen.P1HistoricalFifthNpyPositionalSemantics']},
                 {'path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/93501ca11da26d233922739b6aece9987a877d93/PIPELINE_RESULT.json',
                  'sha256': '3fa68feb2f6070286165883499f7ac9150f150f08b01644712c3f3694df2ee2c',
                  'source_commit': '93501ca11da26d233922739b6aece9987a877d93',
                  'accepted_owners': ['ImbalancedChen.P1OriginalFifthMovingMeshFiberBands',
                                      'ImbalancedChen.P5OldFifthExact64ChildTiling']},
                 {'path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/c247cbcf8bfcf307a4898e3520e900da41148662/PIPELINE_RESULT.json',
                  'sha256': '4f38ec268ec5c0baff349e612e4a4c93ca0ee024a8699222622ef2ee2db60c38',
                  'source_commit': 'c247cbcf8bfcf307a4898e3520e900da41148662',
                  'accepted_owners': ['ImbalancedChen.P5OldFifthFrozenGapConcavity']},
                 {'path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json',
                  'sha256': '0ea4e2ae9dcbd2aad8468846b5c65aa3a0439ac784397b239b9b0339a47d1895',
                  'source_commit': '8eabdf5c9563ae73eb091242f376a5b28456f97f',
                  'accepted_owners': ['ImbalancedChen.P1FifthMask5NamedParent1Owner',
                                      'ImbalancedChen.P1FifthMask6NamedParent0Owner',
                                      'ImbalancedChen.P5OldFifthFiveCoordinateTree',
                                      'ImbalancedChen.P5OldFifthOneCoordinateVertexChord']},
                 {'path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69/named-j5-retry/PIPELINE_RESULT.json',
                  'sha256': '9445e6f4d9ad887cff065c3e501d7e60ec1984261b001029353619e252d9dc3e',
                  'source_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                  'accepted_owners': ['ImbalancedChen.P1FifthNamedParentsConcreteJ5']},
                 {'path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/numeric-second-repairs/PIPELINE_RESULT.json',
                  'sha256': '751a4fef4a9774c45dad46e5d10afc81a135571262d83d9c50ac5bf76ce4bda8',
                  'source_commit': 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a',
                  'accepted_owners': ['ImbalancedChen.P1FifthNamedParentActualIntegral']},
                 {'path': '/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json',
                  'sha256': 'a9e670f74bee98fd8a65ba3ea6de824a804fbcb1b5cffe8782a88463b755be61',
                  'source_commit': '28faf9d2b028997dfe7669b6750c0be5649c9ee4',
                  'accepted_owners': ['ImbalancedChen.P5OldFifthFiveCoordinateBarycentric']}],
 'repair_preimages': {'pointwise-q-namespace-retry': {'module': 'ImbalancedChen.P5OldFifthPointwiseQ',
                                                      'source_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                                                      'manifest_path': 'docs/p1/20261125/p14-continuation/stages/pointwise-q.json',
                                                      'manifest_sha256': 'e6ba7c59143aa3207085e9aee59a93d5034fda02021ef7da928680a3f436d5cc',
                                                      'source_sha256': 'b2b1e89fee01dca52b6136250f4c20238cb564ea8f6691924a7fe3480b72e7d3'},
                      'first-f-concavity-namespace-retry': {'module': 'ImbalancedChen.P5OldFifthFirstFConcavity',
                                                            'source_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                                                            'manifest_path': 'docs/p1/20261125/p14-continuation/stages/first-f-concavity.json',
                                                            'manifest_sha256': '8ad725da66341b9f8c27a31572d4567d540aa6287b6cc87edf4a6993c8041dbc',
                                                            'source_sha256': '5d232b9f9261286fbd270f0c49df61547f82a751864d291f2c3b3c4404cac8d1'},
                      'child-q-jensen-namespace-retry': {'module': 'ImbalancedChen.P5OldFifthChildQJensen',
                                                         'source_commit': 'ea78d79a4d73c2862722bf92b6bd60f6b4d6ec69',
                                                         'manifest_path': 'docs/p1/20261125/p14-continuation/stages/child-q-jensen.json',
                                                         'manifest_sha256': '32c43d714178f944f40e7bab929d5ed6bb4cd55e25fc7c86f0d553a34e1a7d5d',
                                                         'source_sha256': '93033fd02602c14f1f25934b922f425edeefbc754863785b3856fa33ac2090ba'}}}
repo = Path('/workspace/goldbach-formalization')
project = Path('/workspace/blue-member-build')
evidence_root = Path('/workspace/p1-complete-proof/20261125-p14-continuation')
sha = lambda data: hashlib.sha256(data).hexdigest()
driver_pins = {
    'run_stage.py': 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1',
    'materialize_sources.py': 'a074fc285a156eaf886e5a149e9e6f9f01a87f36500379f6c233a52f17dc0659',
}
child_module = 'ImbalancedChen.P5OldFifthChildGapIntegral'
bary_module = 'ImbalancedChen.P5OldFifthFiveCoordinateBarycentric'
assert len(config['stage_specs']) == 12 and len(config['prior_specs']) == 8
assert {s['module'] for s in config['stage_specs']}.isdisjoint({child_module, bary_module})
subprocess.run(['git', 'fetch', 'origin', 'refs/heads/codex/p1-4-continuation-20261125'], cwd=repo, check=True)
def git(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)

# Pin all twelve existing manifests and target sources before deployment.
for spec in config['stage_specs']:
    manifest_bytes = git(source, spec['manifest_path'])
    assert sha(manifest_bytes) == spec['manifest_sha256'], spec['stage']
    manifest = json.loads(manifest_bytes)
    assert manifest['stage'] == spec['stage'] and len(manifest['modules']) == 1
    row = manifest['modules'][0]
    assert row['module'] == spec['module'] and row['path'] == spec['path']
    assert row['before_sha256'] == spec['before_sha256'] and row['after_sha256'] == spec['after_sha256']
    assert sha(git(source, spec['path'])) == spec['after_sha256']
    assert sha(git(spec['preimage_commit'], spec['path'])) == spec['before_sha256']
for stage, spec in config['repair_preimages'].items():
    original_bytes = git(spec['source_commit'], spec['manifest_path'])
    assert sha(original_bytes) == spec['manifest_sha256']
    original = json.loads(original_bytes)
    assert len(original['modules']) == 1
    row = original['modules'][0]
    assert row['module'] == spec['module']
    assert row['before_sha256'] == row['after_sha256'] == spec['source_sha256']
    assert sha(git(spec['source_commit'], row['path'])) == spec['source_sha256']
assert sha(git(source, child_module.replace('.', '/') + '.lean')) == child_spec['source_sha256']

prior_accepted, reused_pipelines = set(), []
for spec in config['prior_specs']:
    raw = Path(spec['path']).read_bytes()
    prior = json.loads(raw)
    assert sha(raw) == spec['sha256'], spec['path']
    assert prior['source_commit'] == spec['source_commit']
    assert prior['driver_sha256'] == driver_pins['run_stage.py']
    assert prior['accepted_owners'] == spec['accepted_owners']
    assert prior['whole_P1_4_complete'] is False
    assert prior_accepted.isdisjoint(prior['accepted_owners'])
    prior_accepted.update(prior['accepted_owners'])
    reused_pipelines.append(dict(spec))
child_raw = child_path.read_bytes()
child = json.loads(child_raw)
assert sha(child_raw) == child_spec['sha256']
assert child['source_commit'] == source and child['stage'] == child_spec['stage']
assert child['targets'] == {child_module: child_spec['source_sha256']}
assert child['accepted_owners'] == child['normal_passed'] == [child_module]
assert not child['normal_failed_or_held'] and child['audit_error'] is None
assert child['whole_P1_4_complete'] is False
assert child_module not in prior_accepted
prior_accepted.add(child_module)
child_reuse = {'path': str(child_path), 'sha256': sha(child_raw), 'source_commit': source,
    'stage': child_spec['stage'], 'accepted_owners': [child_module]}
assert {s['module'] for s in config['stage_specs']}.isdisjoint(prior_accepted)

bootstrap = Path('/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap') / source / 'childgap-accepted-successors'
out = bootstrap / 'PIPELINE_RESULT.json'
assert not out.exists(), 'existing pipeline result requires inspection, not repetition'
bootstrap.mkdir(parents=True, exist_ok=True)
scripts = {}
for name, expected in driver_pins.items():
    raw = git(source, 'docs/p1/20261125/p14-continuation/' + name)
    assert sha(raw) == expected, name
    for spec in config['repair_preimages'].values():
        assert git(spec['source_commit'], 'docs/p1/20261125/p14-continuation/' + name) == raw
    path = bootstrap / name
    if path.exists():
        assert path.read_bytes() == raw
    else:
        with path.open('xb') as stream:
            stream.write(raw)
    scripts[name] = path

accepted, results, source_preimage_installations = set(), [], []
def held(spec, status, **details):
    row = {'stage': spec['stage'], 'status': status, 'accepted_owners': [], **details}
    results.append(row)
    print(json.dumps(row), flush=True)

for spec in config['stage_specs']:
    stage, requirements = spec['stage'], spec['requirements']
    if not set(requirements) <= accepted | prior_accepted:
        held(spec, 'HELD_UPSTREAM_NOT_ACCEPTED', requires=requirements)
        continue
    target = project / spec['path']
    if target.is_symlink() or (target.exists() and not target.is_file()):
        held(spec, 'HELD_SOURCE_PATH_NOT_REGULAR', path=str(target))
        continue
    observed_sha = sha(target.read_bytes()) if target.is_file() else None
    if observed_sha is not None and observed_sha not in {spec['before_sha256'], spec['after_sha256']}:
        held(spec, 'HELD_UNKNOWN_SOURCE_PREIMAGE', path=str(target), source_sha256=observed_sha)
        continue
    if observed_sha is None and stage in config['repair_preimages']:
        original_spec = config['repair_preimages'][stage]
        original = subprocess.run(['python3', '-B', str(scripts['materialize_sources.py']),
            '--source-commit', original_spec['source_commit'], '--manifest', original_spec['manifest_path'], '--run'], cwd=repo)
        source_preimage_installations.append({'module': spec['module'],
            'source_commit': original_spec['source_commit'], 'manifest': original_spec['manifest_path'],
            'exit_code': original.returncode,
            'reason': 'Install only the original published unchanged preimage when this repair target is absent; no compiler invoked.'})
        if original.returncode:
            held(spec, 'HELD_SOURCE_PREIMAGE_INSTALLATION_FAILED', exit_code=original.returncode)
            continue
    install = subprocess.run(['python3', '-B', str(scripts['materialize_sources.py']),
        '--source-commit', source, '--manifest', spec['manifest_path'], '--run'], cwd=repo)
    if install.returncode:
        held(spec, 'HELD_SOURCE_DEPLOYMENT_FAILED', exit_code=install.returncode)
        continue
    run_root = evidence_root / stage / source / 'runs'
    prior_result_paths = set(run_root.glob('attempt-*/RESULT.json'))
    proc = subprocess.run(['python3', '-B', str(scripts['run_stage.py']),
        '--source-commit', source, '--manifest', spec['manifest_path'], '--run'], cwd=repo)
    new_result_paths = set(run_root.glob('attempt-*/RESULT.json')) - prior_result_paths
    assert len(new_result_paths) <= 1, 'multiple new original stage results require inspection'
    row = {'stage': stage, 'exit_code': proc.returncode, 'accepted_owners': []}
    if not new_result_paths:
        row['status'] = 'HELD_MISSING_ORIGINAL_STAGE_RESULT'
    else:
        result_path = next(iter(new_result_paths))
        result = json.loads(result_path.read_bytes())
        assert result['source_commit'] == source and result['stage'] == stage
        assert result['targets'] == {spec['module']: spec['after_sha256']}
        assert result['whole_P1_4_complete'] is False
        assert set(result['accepted_owners']) <= set(result['normal_passed']) <= {spec['module']}
        complete = (result['accepted_owners'] == [spec['module']] and
            not result['normal_failed_or_held'] and result['audit_error'] is None)
        assert proc.returncode == (0 if complete else 1), 'outer exit/result mismatch requires inspection'
        row['result_path'] = str(result_path)
        row['accepted_owners'] = result['accepted_owners']
        accepted.update(result['accepted_owners'])
    results.append(row)
    print(json.dumps({'pipeline_stage_result': row}), flush=True)

report = {'source_commit': source, 'driver_sha256': driver_pins['run_stage.py'],
    'reused_pipelines': reused_pipelines, 'reused_stage_results': [child_reuse],
    'source_preimage_installations': source_preimage_installations, 'stages': results,
    'accepted_owners': sorted(accepted), 'planned_stages': [s['stage'] for s in config['stage_specs']],
    'barycentric_and_childgap_not_recompiled': True,
    'reused_owners_and_declarations_add_no_new_acceptance': True,
    'original_held_history_not_modified': True,
    'unknown_source_preimages_held_without_overwrite': True,
    'additional_imports_rely_on_existing_no_build_gate': [
        'ImbalancedChen.ActualRosserLowerLimit', 'ImbalancedChen.P2DirectedLogRounding'],
    'whole_P1_4_complete': False}
with out.open('x') as stream:
    json.dump(report, stream, indent=2)
print(json.dumps(report), flush=True)
raise SystemExit(0 if all(r.get('exit_code') == 0 and 'status' not in r for r in results) else 1)
PY
