# Task 2 implementation and local kernel evidence

Clean source **a2332ed58aea9ed41363c4366a96c301ef5d7989**, parent and review base **09e3cad2c06f204817ebb64989da16bc50ff7d04**, frozen donor and verifier ancestry baseline **145be87ff0a88914b607baa2a330bc88105a08d6**. Twelve tracked paths changed. The clean pinned local verifier passed **43/43** stages, re-elaborated **4/4** new modules with warnings as errors, replayed **4/4** with the bundled leanchecker, and audited **63** serialized and defining-module declarations. Counts by dependency order are **11, 24, 22, 6**. Transitive axiom union is precisely propext, Classical.choice, Quot.sound. The shared verifier, audit logic, and previous evidence are unchanged. Root controls independent cloud acceptance and publication.

## Mathematical result

The membership terminal derives signed exact division and reconstruction for the original integer output, positivity of the computed primary multiplier and absolute quotient, both required ABL coprimalities, and supported cofactor one for all natural labels. It opens the original primary and nonzero filters, uses the computed-key equality, original fixed-unit witnesses and old prime-support lemmas. Its only proof premise is membership. The beta terminal obtains a genuine weighted-output source witness via beta_ne_zero_mem_image. Its only proof premise is nonzero grouped beta. Its one-line transfer uses that same witness's output equality. We retained the two frequency signs, the starred second atom, the complex fibre sums, and both original physical-modulus kernel calls.

The manuscript at analytic-appendix-1106.tex lines 588ff gives the finite reciprocal source; 676ff gives signed input, residue coprimality and physical c; 964–982 uses primary arithmetic before the normalized oldform coefficient identity. The finite arithmetic used here has no open mathematical step. The spectral coefficient identity, four archived OriginalData terminals/FixedBlock assembly, physical spectral normalization, and the remaining P3.4 estimates are separate. The five retained analytic donor modules did not run as part of this four-module acceptance. A zero grouped coefficient need not have a witness; an occupied original row at zero beta may use the membership terminal directly. Relating a later dyadic blockBeta to this fibre requires the later source witness and key membership.

## Migration and observed repairs

The ledger freezes 57 donor declaration blocks and exact source signatures before editing. Its 53 active public declarations retain their names. It identifies one deliberate private-to-public promotion, the archived public scalar oldformCofactor, and two archived private helpers. All 57 target bodies match their original bytes, except the explicitly removed private modifier on carrier_data. Target names and type digests in the ledger were checked against the full clean inventory for all 57. New declarations are the two literal endpoints. Retained donor remainders differ solely by the requested removal of extracted declarations and associated documentation plus the new import. All six original source blobs were obtained from the fixed git revision, and the lone archive remains unchanged.

The initial endpoint lookup before extraction returned a missing module as expected. Focused A/B/C compilations passed on the first attempt with all donor proof bodies exactly unchanged. The first D proof attempt failed at the local support-function binder (line 55, unknown type for p.Prime). Giving p the explicit natural-number type fixed elaboration. No donor proof or theorem type changed. The pooled lean auditor passed without an inventory workaround. No additional Mathlib tactic import was required; the literal module explicitly imports the finite-ring sum distributivity API used by weighted_pushforward.

## Local commands

Working directory `/workspace/library-files/p34-proof-work`. Focused strict calls used the flags shown in the final strict commands. The full gate was run as follows, with pipefail active.

```bash
source /workspace/library-files/p34-runtime/env.sh
python verification/verify_p34_primary_arithmetic.py --expected-head a2332ed58aea9ed41363c4366a96c301ef5d7989 --output-dir .lake/p34-primary-arithmetic-acceptance | tee .lake/p34-primary-arithmetic-local.log
```

The CLI exited 0. The complete local receipt, compiler-emitted types, source and object SHA-256, resolved import paths, tool binaries, and every exact command/output appear below. The receipt and its machine-readable sibling files also remain in the output directory. All frozen external dependencies were checked against their pins. They are outside the four-module fresh kernel-replay scope.

## Complete CLI output

```text
START head
PASS head
START baseline-ancestor
PASS baseline-ancestor
START working-tree
PASS working-tree
START lean-version
PASS lean-version
START bundled-tools
PASS bundled-tools
START pin-goldbach
PASS pin-goldbach
START clean-goldbach
PASS clean-goldbach
START pin-mathlib
PASS pin-mathlib
START clean-mathlib
PASS clean-mathlib
START pin-LeanArchitect
PASS pin-LeanArchitect
START clean-LeanArchitect
PASS clean-LeanArchitect
START pin-plausible
PASS pin-plausible
START clean-plausible
PASS clean-plausible
START pin-LeanSearchClient
PASS pin-LeanSearchClient
START clean-LeanSearchClient
PASS clean-LeanSearchClient
START pin-importGraph
PASS pin-importGraph
START clean-importGraph
PASS clean-importGraph
START pin-proofwidgets
PASS pin-proofwidgets
START clean-proofwidgets
PASS clean-proofwidgets
START pin-aesop
PASS pin-aesop
START clean-aesop
PASS clean-aesop
START pin-Qq
PASS pin-Qq
START clean-Qq
PASS clean-Qq
START pin-batteries
PASS pin-batteries
START clean-batteries
PASS clean-batteries
START pin-Cli
PASS pin-Cli
START clean-Cli
PASS clean-Cli
START Part3PrimaryPrimeSupport-imports
PASS Part3PrimaryPrimeSupport-imports
START Part3PrimaryPrimeSupport-strict
PASS Part3PrimaryPrimeSupport-strict
START Part3LiteralReciprocalSource-imports
PASS Part3LiteralReciprocalSource-imports
START Part3LiteralReciprocalSource-strict
PASS Part3LiteralReciprocalSource-strict
START Part3FixedRhoPrimaryFiniteCore-imports
PASS Part3FixedRhoPrimaryFiniteCore-imports
START Part3FixedRhoPrimaryFiniteCore-strict
PASS Part3FixedRhoPrimaryFiniteCore-strict
START Part3LiteralPrimaryOldformArithmetic-imports
PASS Part3LiteralPrimaryOldformArithmetic-imports
START Part3LiteralPrimaryOldformArithmetic-strict
PASS Part3LiteralPrimaryOldformArithmetic-strict
START import-scope-regressions
PASS import-scope-regressions
START Part3PrimaryPrimeSupport-replay
PASS Part3PrimaryPrimeSupport-replay
START Part3LiteralReciprocalSource-replay
PASS Part3LiteralReciprocalSource-replay
START Part3FixedRhoPrimaryFiniteCore-replay
PASS Part3FixedRhoPrimaryFiniteCore-replay
START Part3LiteralPrimaryOldformArithmetic-replay
PASS Part3LiteralPrimaryOldformArithmetic-replay
START audit-imports
PASS audit-imports
START axioms
PASS axioms
START final-working-tree
PASS final-working-tree
PASS: 63 declarations across 4 modules, with strict compilation, kernel replay and complete transitive audits.
```

## Exact receipt

```json
{
  "status": "PASSED",
  "baseline": "145be87ff0a88914b607baa2a330bc88105a08d6",
  "modules": [
    "ImbalancedChen.Part3PrimaryPrimeSupport",
    "ImbalancedChen.Part3LiteralReciprocalSource",
    "ImbalancedChen.Part3FixedRhoPrimaryFiniteCore",
    "ImbalancedChen.Part3LiteralPrimaryOldformArithmetic"
  ],
  "scope": "Literal signed primary fibres and nonzero grouped beta, with ABL coprimality and integer K=1.",
  "fresh_external_kernel_closure_claimed": false,
  "started_utc": "2026-11-25T16:45:07.392214+00:00",
  "expected_head": "a2332ed58aea9ed41363c4366a96c301ef5d7989",
  "allowed_transitive_axioms": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "stages": [
    {
      "name": "head",
      "command": [
        "git",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:07.398826+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "baseline-ancestor",
      "command": [
        "git",
        "merge-base",
        "--is-ancestor",
        "145be87ff0a88914b607baa2a330bc88105a08d6",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:07.401420+00:00",
      "elapsed_seconds": 0.003,
      "exit_code": 0
    },
    {
      "name": "working-tree",
      "command": [
        "git",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:07.404810+00:00",
      "elapsed_seconds": 0.063,
      "exit_code": 0
    },
    {
      "name": "lean-version",
      "command": [
        "lake",
        "env",
        "lean",
        "--version"
      ],
      "started_utc": "2026-11-25T16:45:07.468592+00:00",
      "elapsed_seconds": 0.975,
      "exit_code": 0
    },
    {
      "name": "bundled-tools",
      "command": [
        "lake",
        "env",
        "/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python",
        "-c",
        "import json,os,shutil; print(json.dumps({'sysroot':os.environ.get('LEAN_SYSROOT'),'lean_path':os.environ.get('LEAN_PATH'),'lean':shutil.which('lean'),'leanchecker':shutil.which('leanchecker')}))"
      ],
      "started_utc": "2026-11-25T16:45:08.443799+00:00",
      "elapsed_seconds": 0.613,
      "exit_code": 0
    },
    {
      "name": "pin-goldbach",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/goldbach",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.058608+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-goldbach",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/goldbach",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.061317+00:00",
      "elapsed_seconds": 0.022,
      "exit_code": 0
    },
    {
      "name": "pin-mathlib",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/mathlib",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.084015+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-mathlib",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/mathlib",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.086732+00:00",
      "elapsed_seconds": 0.024,
      "exit_code": 0
    },
    {
      "name": "pin-LeanArchitect",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/LeanArchitect",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.111527+00:00",
      "elapsed_seconds": 0.004,
      "exit_code": 0
    },
    {
      "name": "clean-LeanArchitect",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/LeanArchitect",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.115865+00:00",
      "elapsed_seconds": 0.003,
      "exit_code": 0
    },
    {
      "name": "pin-plausible",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/plausible",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.119185+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-plausible",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/plausible",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.121409+00:00",
      "elapsed_seconds": 0.003,
      "exit_code": 0
    },
    {
      "name": "pin-LeanSearchClient",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/LeanSearchClient",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.124592+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-LeanSearchClient",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/LeanSearchClient",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.126353+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "pin-importGraph",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/importGraph",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.130238+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-importGraph",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/importGraph",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.132794+00:00",
      "elapsed_seconds": 0.003,
      "exit_code": 0
    },
    {
      "name": "pin-proofwidgets",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/proofwidgets",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.136157+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-proofwidgets",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/proofwidgets",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.138247+00:00",
      "elapsed_seconds": 0.003,
      "exit_code": 0
    },
    {
      "name": "pin-aesop",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/aesop",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.141239+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-aesop",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/aesop",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.143293+00:00",
      "elapsed_seconds": 0.004,
      "exit_code": 0
    },
    {
      "name": "pin-Qq",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/Qq",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.147684+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-Qq",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/Qq",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.149492+00:00",
      "elapsed_seconds": 0.003,
      "exit_code": 0
    },
    {
      "name": "pin-batteries",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/batteries",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.152795+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-batteries",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/batteries",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.154893+00:00",
      "elapsed_seconds": 0.004,
      "exit_code": 0
    },
    {
      "name": "pin-Cli",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/Cli",
        "rev-parse",
        "HEAD"
      ],
      "started_utc": "2026-11-25T16:45:09.159100+00:00",
      "elapsed_seconds": 0.002,
      "exit_code": 0
    },
    {
      "name": "clean-Cli",
      "command": [
        "git",
        "-C",
        "/workspace/library-files/p34-proof-work/.lake/packages/Cli",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:09.161240+00:00",
      "elapsed_seconds": 0.003,
      "exit_code": 0
    },
    {
      "name": "Part3PrimaryPrimeSupport-imports",
      "command": [
        "lake",
        "env",
        "lean",
        "--deps",
        "ImbalancedChen/Part3PrimaryPrimeSupport.lean"
      ],
      "started_utc": "2026-11-25T16:45:09.165765+00:00",
      "elapsed_seconds": 0.632,
      "exit_code": 0
    },
    {
      "name": "Part3PrimaryPrimeSupport-strict",
      "command": [
        "lake",
        "env",
        "lean",
        "-t0",
        "-j1",
        "-M6000",
        "-DwarningAsError=true",
        "-o",
        "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3PrimaryPrimeSupport.olean",
        "ImbalancedChen/Part3PrimaryPrimeSupport.lean"
      ],
      "started_utc": "2026-11-25T16:45:09.800118+00:00",
      "elapsed_seconds": 2.109,
      "exit_code": 0
    },
    {
      "name": "Part3LiteralReciprocalSource-imports",
      "command": [
        "lake",
        "env",
        "lean",
        "--deps",
        "ImbalancedChen/Part3LiteralReciprocalSource.lean"
      ],
      "started_utc": "2026-11-25T16:45:11.910296+00:00",
      "elapsed_seconds": 0.773,
      "exit_code": 0
    },
    {
      "name": "Part3LiteralReciprocalSource-strict",
      "command": [
        "lake",
        "env",
        "lean",
        "-t0",
        "-j1",
        "-M6000",
        "-DwarningAsError=true",
        "-o",
        "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralReciprocalSource.olean",
        "ImbalancedChen/Part3LiteralReciprocalSource.lean"
      ],
      "started_utc": "2026-11-25T16:45:12.685344+00:00",
      "elapsed_seconds": 2.579,
      "exit_code": 0
    },
    {
      "name": "Part3FixedRhoPrimaryFiniteCore-imports",
      "command": [
        "lake",
        "env",
        "lean",
        "--deps",
        "ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.lean"
      ],
      "started_utc": "2026-11-25T16:45:15.265941+00:00",
      "elapsed_seconds": 1.036,
      "exit_code": 0
    },
    {
      "name": "Part3FixedRhoPrimaryFiniteCore-strict",
      "command": [
        "lake",
        "env",
        "lean",
        "-t0",
        "-j1",
        "-M6000",
        "-DwarningAsError=true",
        "-o",
        "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.olean",
        "ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.lean"
      ],
      "started_utc": "2026-11-25T16:45:16.303482+00:00",
      "elapsed_seconds": 2.116,
      "exit_code": 0
    },
    {
      "name": "Part3LiteralPrimaryOldformArithmetic-imports",
      "command": [
        "lake",
        "env",
        "lean",
        "--deps",
        "ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.lean"
      ],
      "started_utc": "2026-11-25T16:45:18.420282+00:00",
      "elapsed_seconds": 0.575,
      "exit_code": 0
    },
    {
      "name": "Part3LiteralPrimaryOldformArithmetic-strict",
      "command": [
        "lake",
        "env",
        "lean",
        "-t0",
        "-j1",
        "-M6000",
        "-DwarningAsError=true",
        "-o",
        "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.olean",
        "ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.lean"
      ],
      "started_utc": "2026-11-25T16:45:18.996933+00:00",
      "elapsed_seconds": 2.127,
      "exit_code": 0
    },
    {
      "name": "import-scope-regressions",
      "command": [
        "lake",
        "env",
        "/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python",
        "verification/test_p34_import_scope.py"
      ],
      "started_utc": "2026-11-25T16:45:21.125096+00:00",
      "elapsed_seconds": 0.692,
      "exit_code": 0
    },
    {
      "name": "Part3PrimaryPrimeSupport-replay",
      "command": [
        "lake",
        "env",
        "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker",
        "--verbose",
        "ImbalancedChen.Part3PrimaryPrimeSupport"
      ],
      "started_utc": "2026-11-25T16:45:21.817517+00:00",
      "elapsed_seconds": 2.826,
      "exit_code": 0
    },
    {
      "name": "Part3LiteralReciprocalSource-replay",
      "command": [
        "lake",
        "env",
        "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker",
        "--verbose",
        "ImbalancedChen.Part3LiteralReciprocalSource"
      ],
      "started_utc": "2026-11-25T16:45:24.644468+00:00",
      "elapsed_seconds": 3.025,
      "exit_code": 0
    },
    {
      "name": "Part3FixedRhoPrimaryFiniteCore-replay",
      "command": [
        "lake",
        "env",
        "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker",
        "--verbose",
        "ImbalancedChen.Part3FixedRhoPrimaryFiniteCore"
      ],
      "started_utc": "2026-11-25T16:45:27.669773+00:00",
      "elapsed_seconds": 2.697,
      "exit_code": 0
    },
    {
      "name": "Part3LiteralPrimaryOldformArithmetic-replay",
      "command": [
        "lake",
        "env",
        "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker",
        "--verbose",
        "ImbalancedChen.Part3LiteralPrimaryOldformArithmetic"
      ],
      "started_utc": "2026-11-25T16:45:30.367604+00:00",
      "elapsed_seconds": 3.474,
      "exit_code": 0
    },
    {
      "name": "audit-imports",
      "command": [
        "lake",
        "env",
        "lean",
        "--deps",
        "verification/P34PrimaryArithmeticAudit.lean"
      ],
      "started_utc": "2026-11-25T16:45:33.842583+00:00",
      "elapsed_seconds": 0.65,
      "exit_code": 0
    },
    {
      "name": "axioms",
      "command": [
        "lake",
        "env",
        "lean",
        "-t0",
        "-j1",
        "-M6000",
        "-DwarningAsError=true",
        "verification/P34PrimaryArithmeticAudit.lean"
      ],
      "started_utc": "2026-11-25T16:45:34.493453+00:00",
      "elapsed_seconds": 14.568,
      "exit_code": 0
    },
    {
      "name": "final-working-tree",
      "command": [
        "git",
        "status",
        "--porcelain",
        "--untracked-files=all"
      ],
      "started_utc": "2026-11-25T16:45:49.064468+00:00",
      "elapsed_seconds": 0.042,
      "exit_code": 0
    }
  ],
  "source_sha256": {
    "ImbalancedChen/Part3PrimaryPrimeSupport.lean": "e3df644ca8fbbea64e547cc664408ca8b0859f0d44f7a216d7a99577f1f39117",
    "ImbalancedChen/Part3LiteralReciprocalSource.lean": "af03ad72797ed4761c50261a6e532f135bd95779f90ae9c89dde9ccf743a7e31",
    "ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.lean": "54c19ddcf0e6317ef1a6f1c20cc95f243744b01b6c443e993f3be1273bdaec68",
    "ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.lean": "0eb92330fd3ab4df1860ca2098525fc9828bbef9731aaba694bcb1abfde16b3b",
    "verification/P34PrimaryArithmeticAudit.lean": "1a821b39c246f115af8a6955f06d1a642c69754c29517550c98993cf2de0bb4e",
    "verification/verify_p34_cusp_normalization.py": "57415c3617e2e4ee7aab8aad34b606dbb767bf577c45a2ae8980f079edd2c68e",
    "verification/verify_variable_envelope_boxes.py": "8979f29bda930f19f06b29d840ea1f997d1de631b45a6eeb35d8a801149bc916",
    "verification/test_p34_import_scope.py": "3ec6990afbc9055b1b59850a868528e8ada573357153a530350959ffc710385a",
    "verification/verify_p34_primary_arithmetic.py": "af4b5aae5d342daf9083549de227d9a696fe200f886da09fbae972b66a341792",
    "docs/part3-distribution/p34-20261126/PRIMARY_DECLARATION_MOVES.json": "6dbd34a4842483d2fe7059667695f65249779a967fea6afc7056fc6ed1887ffa",
    "lean-toolchain": "62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef",
    "lake-manifest.json": "35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849",
    "lakefile.toml": "b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254"
  },
  "head_commit": "a2332ed58aea9ed41363c4366a96c301ef5d7989",
  "working_tree": "",
  "lean_version": "Lean (version 4.33.0-rc1, x86_64-unknown-linux-gnu, commit 62eed1db4d67327ec8120be05f1a1b0847d74561, Release)",
  "tool_paths": {
    "sysroot": "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux",
    "lean_path": "/workspace/library-files/p34-runtime/project/.lake/packages/Cli/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/batteries/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/Qq/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/aesop/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/proofwidgets/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/importGraph/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/plausible/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/LeanArchitect/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/goldbach/.lake/build/lib/lean:/workspace/library-files/p34-proof-work/.lake/build/lib/lean:/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean",
    "lean": "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/lean",
    "leanchecker": "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker"
  },
  "tool_sha256": {
    "lean": "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
    "leanchecker": "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"
  },
  "parsed_dependencies": {
    "ImbalancedChen.Part3PrimaryPrimeSupport": [
      "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean",
      "/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/BigOperators/Associated.olean",
      "/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Factorization/Basic.olean"
    ],
    "ImbalancedChen.Part3LiteralReciprocalSource": [
      "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean",
      "/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/BigOperators/Group/Finset/Basic.olean",
      "/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/BigOperators/Ring/Finset.olean",
      "/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Complex/Basic.olean",
      "/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Finset/Prod.olean",
      "/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/GCD/Basic.olean",
      "/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Order/Interval/Finset/Nat.olean"
    ],
    "ImbalancedChen.Part3FixedRhoPrimaryFiniteCore": [
      "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralReciprocalSource.olean",
      "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3PrimaryPrimeSupport.olean",
      "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean"
    ],
    "ImbalancedChen.Part3LiteralPrimaryOldformArithmetic": [
      "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.olean",
      "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean"
    ],
    "verification/P34PrimaryArithmeticAudit.lean": [
      "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.olean",
      "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.olean",
      "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralReciprocalSource.olean",
      "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3PrimaryPrimeSupport.olean",
      "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean",
      "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Lean/Util/CollectAxioms.olean"
    ]
  },
  "olean_sha256": {
    ".lake/build/lib/lean/ImbalancedChen/Part3PrimaryPrimeSupport.olean": "560f16851f18cdb30779b344fcba974346fdeb384e95364fbcfab30bee72d81a",
    ".lake/build/lib/lean/ImbalancedChen/Part3LiteralReciprocalSource.olean": "c775cff34573fab58672c2b09f06e27fab5506cf3ab95d6e0bd5e2ef279299c2",
    ".lake/build/lib/lean/ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.olean": "aa377051e3a5d79d7fbf521d73dc163cd7995a6db5c5833d3576f5eafbee2643",
    ".lake/build/lib/lean/ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.olean": "3ec4059522d2880439cede9586ad0df646e9da6c6d615b4da5775109b7940b75"
  },
  "declaration_count": 63,
  "module_counts": [
    {
      "count": 11,
      "module": "ImbalancedChen.Part3PrimaryPrimeSupport"
    },
    {
      "count": 24,
      "module": "ImbalancedChen.Part3LiteralReciprocalSource"
    },
    {
      "count": 22,
      "module": "ImbalancedChen.Part3FixedRhoPrimaryFiniteCore"
    },
    {
      "count": 6,
      "module": "ImbalancedChen.Part3LiteralPrimaryOldformArithmetic"
    }
  ]
}
```

## Per-stage commands and complete outputs

### head

```text
command=["git", "rev-parse", "HEAD"]
a2332ed58aea9ed41363c4366a96c301ef5d7989
```

### baseline-ancestor

```text
command=["git", "merge-base", "--is-ancestor", "145be87ff0a88914b607baa2a330bc88105a08d6", "HEAD"]
```

### working-tree

```text
command=["git", "status", "--porcelain", "--untracked-files=all"]
```

### lean-version

```text
command=["lake", "env", "lean", "--version"]
Lean (version 4.33.0-rc1, x86_64-unknown-linux-gnu, commit 62eed1db4d67327ec8120be05f1a1b0847d74561, Release)
```

### bundled-tools

```text
command=["lake", "env", "/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python", "-c", "import json,os,shutil; print(json.dumps({'sysroot':os.environ.get('LEAN_SYSROOT'),'lean_path':os.environ.get('LEAN_PATH'),'lean':shutil.which('lean'),'leanchecker':shutil.which('leanchecker')}))"]
{"sysroot": "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux", "lean_path": "/workspace/library-files/p34-runtime/project/.lake/packages/Cli/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/batteries/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/Qq/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/aesop/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/proofwidgets/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/importGraph/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/plausible/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/LeanArchitect/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean:/workspace/library-files/p34-runtime/project/.lake/packages/goldbach/.lake/build/lib/lean:/workspace/library-files/p34-proof-work/.lake/build/lib/lean:/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean", "lean": "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/lean", "leanchecker": "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker"}
```

### pin-goldbach

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/goldbach", "rev-parse", "HEAD"]
09b97db5764ade1246bfb77206baa1b124760958
```

### clean-goldbach

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/goldbach", "status", "--porcelain", "--untracked-files=all"]
```

### pin-mathlib

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/mathlib", "rev-parse", "HEAD"]
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1
```

### clean-mathlib

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/mathlib", "status", "--porcelain", "--untracked-files=all"]
```

### pin-LeanArchitect

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/LeanArchitect", "rev-parse", "HEAD"]
78dd66840d3efe8c824c699fc03381cec817c271
```

### clean-LeanArchitect

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/LeanArchitect", "status", "--porcelain", "--untracked-files=all"]
```

### pin-plausible

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/plausible", "rev-parse", "HEAD"]
b1c4a69a7e247ab7df20460212001673d74f08c0
```

### clean-plausible

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/plausible", "status", "--porcelain", "--untracked-files=all"]
```

### pin-LeanSearchClient

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/LeanSearchClient", "rev-parse", "HEAD"]
0498c7c070c143a3bf7379f4d99a2c63bb9d9715
```

### clean-LeanSearchClient

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/LeanSearchClient", "status", "--porcelain", "--untracked-files=all"]
```

### pin-importGraph

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/importGraph", "rev-parse", "HEAD"]
18a90119a5d316358fde6c86e0ca24e59212e32c
```

### clean-importGraph

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/importGraph", "status", "--porcelain", "--untracked-files=all"]
```

### pin-proofwidgets

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/proofwidgets", "rev-parse", "HEAD"]
b1436dc749e722c9920036b52cdc43b3451d0b69
```

### clean-proofwidgets

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/proofwidgets", "status", "--porcelain", "--untracked-files=all"]
```

### pin-aesop

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/aesop", "rev-parse", "HEAD"]
57d3325be72a842920813bcb40f96a6f7393c185
```

### clean-aesop

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/aesop", "status", "--porcelain", "--untracked-files=all"]
```

### pin-Qq

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/Qq", "rev-parse", "HEAD"]
ee41917ae11d38479fb8fb24745f7ca4bf0a784d
```

### clean-Qq

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/Qq", "status", "--porcelain", "--untracked-files=all"]
```

### pin-batteries

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/batteries", "rev-parse", "HEAD"]
41bd267b3f6b7252f6676af46d4ffc6783b64de9
```

### clean-batteries

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/batteries", "status", "--porcelain", "--untracked-files=all"]
```

### pin-Cli

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/Cli", "rev-parse", "HEAD"]
da07ca808b6718cb2aed14dba154e5a08b8f8ecf
```

### clean-Cli

```text
command=["git", "-C", "/workspace/library-files/p34-proof-work/.lake/packages/Cli", "status", "--porcelain", "--untracked-files=all"]
```

### Part3PrimaryPrimeSupport-imports

```text
command=["lake", "env", "lean", "--deps", "ImbalancedChen/Part3PrimaryPrimeSupport.lean"]
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Factorization/Basic.olean
/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/BigOperators/Associated.olean
```

### Part3PrimaryPrimeSupport-strict

```text
command=["lake", "env", "lean", "-t0", "-j1", "-M6000", "-DwarningAsError=true", "-o", "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3PrimaryPrimeSupport.olean", "ImbalancedChen/Part3PrimaryPrimeSupport.lean"]
```

### Part3LiteralReciprocalSource-imports

```text
command=["lake", "env", "lean", "--deps", "ImbalancedChen/Part3LiteralReciprocalSource.lean"]
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Finset/Prod.olean
/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Order/Interval/Finset/Nat.olean
/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/GCD/Basic.olean
/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Complex/Basic.olean
/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/BigOperators/Group/Finset/Basic.olean
/workspace/library-files/p34-runtime/project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/BigOperators/Ring/Finset.olean
```

### Part3LiteralReciprocalSource-strict

```text
command=["lake", "env", "lean", "-t0", "-j1", "-M6000", "-DwarningAsError=true", "-o", "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralReciprocalSource.olean", "ImbalancedChen/Part3LiteralReciprocalSource.lean"]
```

### Part3FixedRhoPrimaryFiniteCore-imports

```text
command=["lake", "env", "lean", "--deps", "ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.lean"]
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3PrimaryPrimeSupport.olean
/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralReciprocalSource.olean
```

### Part3FixedRhoPrimaryFiniteCore-strict

```text
command=["lake", "env", "lean", "-t0", "-j1", "-M6000", "-DwarningAsError=true", "-o", "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.olean", "ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.lean"]
```

### Part3LiteralPrimaryOldformArithmetic-imports

```text
command=["lake", "env", "lean", "--deps", "ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.lean"]
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.olean
```

### Part3LiteralPrimaryOldformArithmetic-strict

```text
command=["lake", "env", "lean", "-t0", "-j1", "-M6000", "-DwarningAsError=true", "-o", "/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.olean", "ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.lean"]
```

### import-scope-regressions

```text
command=["lake", "env", "/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python", "verification/test_p34_import_scope.py"]
...
----------------------------------------------------------------------
Ran 3 tests in 0.117s

OK
```

### Part3PrimaryPrimeSupport-replay

```text
command=["lake", "env", "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker", "--verbose", "ImbalancedChen.Part3PrimaryPrimeSupport"]
replaying ImbalancedChen.Part3PrimaryPrimeSupport
```

### Part3LiteralReciprocalSource-replay

```text
command=["lake", "env", "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker", "--verbose", "ImbalancedChen.Part3LiteralReciprocalSource"]
replaying ImbalancedChen.Part3LiteralReciprocalSource
```

### Part3FixedRhoPrimaryFiniteCore-replay

```text
command=["lake", "env", "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker", "--verbose", "ImbalancedChen.Part3FixedRhoPrimaryFiniteCore"]
replaying ImbalancedChen.Part3FixedRhoPrimaryFiniteCore
```

### Part3LiteralPrimaryOldformArithmetic-replay

```text
command=["lake", "env", "/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/leanchecker", "--verbose", "ImbalancedChen.Part3LiteralPrimaryOldformArithmetic"]
replaying ImbalancedChen.Part3LiteralPrimaryOldformArithmetic
```

### audit-imports

```text
command=["lake", "env", "lean", "--deps", "verification/P34PrimaryArithmeticAudit.lean"]
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Init.olean
/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3PrimaryPrimeSupport.olean
/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralReciprocalSource.olean
/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.olean
/workspace/library-files/p34-proof-work/.lake/build/lib/lean/ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.olean
/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/lib/lean/Lean/Util/CollectAxioms.olean
```

### axioms

```text
command=["lake", "env", "lean", "-t0", "-j1", "-M6000", "-DwarningAsError=true", "verification/P34PrimaryArithmeticAudit.lean"]
PART3_AUDIT_DECL {"axioms":[],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output","type":"Type"}
PART3_AUDIT_DECL {"axioms":[],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source","type":"Type"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.beta","type":"Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source →\n  (Nat → Complex) → (Int → Complex) → ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output → Complex"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.beta_ne_zero_mem_image","type":"∀ {U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source} {lambda : Nat → Complex}\n  {omega : Int → Complex} {zy : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output},\n  @Ne.{1} Complex (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.beta U lambda omega zy)\n      (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) →\n    @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output\n      (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output)\n      (@SetLike.instMembership.{0, 0}\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output)\n        ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output\n        (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output))\n      (@Finset.image.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output\n        (fun a b => @instDecidableEqProd.{0, 0} Nat Int instDecidableEqNat Int.instDecidableEq a b)\n        ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output U)\n      zy"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.carrier","type":"Nat →\n  Int →\n    Finset.{0} Nat →\n      Nat → Finset.{0} Int → Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.carrier_data","type":"∀ {A : Nat} {a : Int} {T : Finset.{0} Nat} {H : Nat} {F : Finset.{0} Int}\n  {s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source},\n  @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n      (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n      (@SetLike.instMembership.{0, 0}\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n        ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n      (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.carrier A a T H F) s →\n    And\n      (@Membership.mem.{0, 0} Int (Finset.{0} Int)\n        (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int)) F\n        (@Prod.fst.{0, 0} Int\n          (Prod.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n            ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n          s))\n      (And\n        (@Membership.mem.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n          (Finset.{0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n          (@SetLike.instMembership.{0, 0}\n            (Finset.{0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n            ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n            (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner))\n          (ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.finiteInnerCarrier T H)\n          (@Prod.fst.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n            ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n            (@Prod.snd.{0, 0} Int\n              (Prod.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n                ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n              s)))\n        (And\n          (@Membership.mem.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n            (Finset.{0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n            (@SetLike.instMembership.{0, 0}\n              (Finset.{0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n              ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n              (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner))\n            (ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.finiteInnerCarrier T H)\n            (@Prod.snd.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n              ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n              (@Prod.snd.{0, 0} Int\n                (Prod.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n                  ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n                s)))\n          (And\n            (@Ne.{1} Int\n              (@Prod.fst.{0, 0} Int\n                (Prod.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n                  ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n                s)\n              (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))\n            (And\n              (ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.fixedUnit A a\n                (@Prod.fst.{0, 0} Nat Int\n                  (@Prod.fst.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n                    ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n                    (@Prod.snd.{0, 0} Int\n                      (Prod.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n                        ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n                      s))))\n              (ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.fixedUnit A a\n                (@Prod.fst.{0, 0} Nat Int\n                  (@Prod.snd.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n                    ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n                    (@Prod.snd.{0, 0} Int\n                      (Prod.{0, 0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner\n                        ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner)\n                      s))))))))"}
PART3_AUDIT_DECL {"axioms":["propext","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.fiber","type":"Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source →\n  ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output →\n    Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source"}
PART3_AUDIT_DECL {"axioms":["propext","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.nonzeroSource","type":"Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source →\n  Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source"}
PART3_AUDIT_DECL {"axioms":[],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output","type":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source →\n  ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output_positive_level","type":"∀ {A : Nat} {a : Int} {T : Finset.{0} Nat} {H : Nat} {F : Finset.{0} Int},\n  (∀ (t : Nat),\n      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)\n          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) T t →\n        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t) →\n    ∀ {s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source},\n      @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n          (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n          (@SetLike.instMembership.{0, 0}\n            (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n            ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n            (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n          (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.carrier A a T H F) s →\n        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))\n          (@Prod.fst.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output_residue_coprime","type":"∀ {A : Nat} {a : Int} {T : Finset.{0} Nat} {H : Nat} {F : Finset.{0} Int}\n  {s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source},\n  @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n      (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n      (@SetLike.instMembership.{0, 0}\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n        ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n      (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.carrier A a T H F) s →\n    a.natAbs.Coprime\n      (@Prod.fst.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.rawCarrier","type":"Finset.{0} Nat →\n  Nat → Finset.{0} Int → Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.weight","type":"(Nat → Complex) → (Int → Complex) → ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source → Complex"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.weighted_pushforward","type":"∀ (U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source) (lambda : Nat → Complex)\n  (omega : Int → Complex) (K : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output → Complex),\n  @Eq.{1} Complex\n    (∑ s ∈ U,\n      @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)\n        (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.weight lambda omega s)\n        (K (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s)))\n    (∑\n      zy ∈\n        @Finset.image.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n          ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output\n          (fun a b => @instDecidableEqProd.{0, 0} Nat Int instDecidableEqNat Int.instDecidableEq a b)\n          ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output U,\n      @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)\n        (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.beta U lambda omega zy) (K zy))"}
PART3_AUDIT_DECL {"axioms":[],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner","type":"Type"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.atomCoeff","type":"(Nat → Complex) → (Int → Complex) → ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner → Complex"}
PART3_AUDIT_DECL {"axioms":[],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.difference","type":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner →\n  ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner → Int"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.finiteInnerCarrier","type":"Finset.{0} Nat → Nat → Finset.{0} ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner"}
PART3_AUDIT_DECL {"axioms":[],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.fixedUnit","type":"Nat → Int → Nat → Prop"}
PART3_AUDIT_DECL {"axioms":[],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.level","type":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner →\n  ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner → Nat"}
PART3_AUDIT_DECL {"axioms":[],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.outputY","type":"Int →\n  ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner →\n    ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner → Int"}
PART3_AUDIT_DECL {"axioms":[],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.output_level_pos","type":"∀ {u v : ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner},\n  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Prod.fst.{0, 0} Nat Int u) →\n    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))\n        (@Prod.fst.{0, 0} Nat Int v) →\n      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))\n        (ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.level u v)"}
PART3_AUDIT_DECL {"axioms":["propext","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.output_level_residue_coprime","type":"∀ (A : Nat) (a : Int) {u v : ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.Inner},\n  ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.fixedUnit A a (@Prod.fst.{0, 0} Nat Int u) →\n    ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.fixedUnit A a (@Prod.fst.{0, 0} Nat Int v) →\n      a.natAbs.Coprime (ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly.level u v)"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.coprimePart","type":"Nat → Nat → Nat"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.coprimePart_coprime","type":"∀ (n d : Nat), (ImbalancedChen.Part3.CanonicalReciprocalData.coprimePart n d).Coprime d"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.coprime_of_prime_support","type":"∀ {u d s : Nat},\n  u.Coprime d →\n    (∀ (p : Nat), Nat.Prime p → @Dvd.dvd.{0} Nat Nat.instDvd p s → @Dvd.dvd.{0} Nat Nat.instDvd p d) → u.Coprime s"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.prime_dvd_coprimePart_not_dvd","type":"∀ {n d p : Nat},\n  Nat.Prime p →\n    @Dvd.dvd.{0} Nat Nat.instDvd p (ImbalancedChen.Part3.CanonicalReciprocalData.coprimePart n d) →\n      Not (@Dvd.dvd.{0} Nat Nat.instDvd p d)"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.prime_dvd_supportedPart","type":"∀ {n d p : Nat},\n  Nat.Prime p →\n    @Dvd.dvd.{0} Nat Nat.instDvd p (ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart n d) →\n      @Dvd.dvd.{0} Nat Nat.instDvd p d"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart","type":"Nat → Nat → Nat"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart_dvd","type":"∀ {n : Nat},\n  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →\n    ∀ (d : Nat), @Dvd.dvd.{0} Nat Nat.instDvd (ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart n d) n"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart_mul_coprimePart","type":"∀ {n : Nat},\n  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →\n    ∀ (d : Nat),\n      @Eq.{1} Nat\n        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)\n          (ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart n d)\n          (ImbalancedChen.Part3.CanonicalReciprocalData.coprimePart n d))\n        n"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart_pos","type":"∀ (n d : Nat),\n  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))\n    (ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart n d)"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralReciprocalSource","name":"ImbalancedChen.Part3.CommonSmoothCutoff.poissonNonzeroFrequencyWindow","type":"Nat → Finset.{0} Int"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.finite_primary_decomposition","type":"∀ (rho : Int) (U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n  (F : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source → Complex),\n  @Eq.{1} Complex (∑ s ∈ U, F s)\n    (∑ nu ∈ ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryKeys rho U,\n      ∑ s ∈ ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre rho U nu, F s)"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.finite_primary_original_modulus","type":"∀ (rho : Int) (U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source),\n  (∀ (s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source),\n      @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n          (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n          (@SetLike.instMembership.{0, 0}\n            (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n            ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n            (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n          U s →\n        @Ne.{1} Int\n          (@Prod.snd.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))\n          (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →\n    ∀ (lambda : Nat → Complex) (omega : Int → Complex) (c : Nat) (K : Nat → Int → Nat → Int → Complex),\n      @Eq.{1} Complex\n        (∑ s ∈ U,\n          @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)\n            (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.weight lambda omega s)\n            (K c rho\n              (@Prod.fst.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))\n              (@Prod.snd.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))))\n        (∑ nu ∈ ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryKeys rho U,\n          ∑ s ∈ ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre rho U nu,\n            @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)\n              (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.weight lambda omega s)\n              (K c rho\n                (@Prod.fst.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))\n                (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) (@Nat.cast.{0} Int instNatCastInt nu)\n                  (@HDiv.hDiv.{0, 0, 0} Int Int Int (@instHDiv.{0} Int Int.instDiv)\n                    (@Prod.snd.{0, 0} Nat Int\n                      (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))\n                    (@Nat.cast.{0} Int instNatCastInt nu)))))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.mem_primaryFibre_iff","type":"∀ {rho : Int} {U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source} {nu : Nat}\n  {s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source},\n  Iff\n    (@Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n      (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n      (@SetLike.instMembership.{0, 0}\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n        ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n      (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre rho U nu) s)\n    (And\n      (@Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n        (@SetLike.instMembership.{0, 0}\n          (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n          ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n          (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n        U s)\n      (@Eq.{1} Nat\n        (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho\n          (@Prod.snd.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s)))\n        nu))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre","type":"Int →\n  Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source →\n    Nat → Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre_gate","type":"∀ {rho : Int} {U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source},\n  (∀ (s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source),\n      @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n          (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n          (@SetLike.instMembership.{0, 0}\n            (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n            ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n            (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n          U s →\n        @Ne.{1} Int\n          (@Prod.snd.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))\n          (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →\n    ∀ {nu : Nat} {s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source},\n      @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n          (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n          (@SetLike.instMembership.{0, 0}\n            (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n            ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n            (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n          (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre rho U nu) s →\n        And\n          (@Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt nu)\n            (@Prod.snd.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s)))\n          ((@HDiv.hDiv.{0, 0, 0} Int Int Int (@instHDiv.{0} Int Int.instDiv)\n                  (@Prod.snd.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))\n                  (@Nat.cast.{0} Int instNatCastInt nu)).natAbs.Coprime\n            rho.natAbs)"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre_key_unique","type":"∀ {rho : Int} {U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source} {nu eta : Nat}\n  {s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source},\n  @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n      (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n      (@SetLike.instMembership.{0, 0}\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n        ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n      (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre rho U nu) s →\n    @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n        (@SetLike.instMembership.{0, 0}\n          (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n          ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n          (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n        (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre rho U eta) s →\n      @Eq.{1} Nat nu eta"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryKeys","type":"Int → Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source → Finset.{0} Nat"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryKeys_pos","type":"∀ {rho : Int} {U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source} {nu : Nat},\n  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)\n      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))\n      (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryKeys rho U) nu →\n    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) nu"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryKeys_prime_support","type":"∀ {rho : Int} {U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source} {nu p : Nat},\n  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)\n      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))\n      (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryKeys rho U) nu →\n    Nat.Prime p → @Dvd.dvd.{0} Nat Nat.instDvd p nu → @Dvd.dvd.{0} Nat Nat.instDvd p rho.natAbs"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu","type":"Int → Int → Nat"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu_dvd","type":"∀ (rho : Int) {y : Int},\n  @Ne.{1} Int y (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →\n    @Dvd.dvd.{0} Int Int.instDvd\n      (@Nat.cast.{0} Int instNatCastInt (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y))\n      y"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu_dvd_natAbs","type":"∀ (rho : Int) {y : Int},\n  @Ne.{1} Int y (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →\n    @Dvd.dvd.{0} Nat Nat.instDvd (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y)\n      y.natAbs"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu_pos","type":"∀ (rho y : Int),\n  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))\n    (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y)"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu_prime_support","type":"∀ (rho y : Int) {p : Nat},\n  Nat.Prime p →\n    @Dvd.dvd.{0} Nat Nat.instDvd p (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y) →\n      @Dvd.dvd.{0} Nat Nat.instDvd p rho.natAbs"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient","type":"Int → Int → Int"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient_coprime","type":"∀ (rho : Int) {y : Int},\n  @Ne.{1} Int y (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →\n    (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient rho y).natAbs.Coprime rho.natAbs"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient_natAbs","type":"∀ (rho : Int) {y : Int},\n  @Ne.{1} Int y (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →\n    @Eq.{1} Nat (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient rho y).natAbs\n      (ImbalancedChen.Part3.CanonicalReciprocalData.coprimePart y.natAbs rho.natAbs)"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient_ne_zero","type":"∀ (rho : Int) {y : Int},\n  @Ne.{1} Int y (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →\n    @Ne.{1} Int (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient rho y)\n      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimary_reconstruct","type":"∀ (rho : Int) {y : Int},\n  @Ne.{1} Int y (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →\n    @Eq.{1} Int\n      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)\n        (@Nat.cast.{0} Int instNatCastInt\n          (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y))\n        (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient rho y))\n      y"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimary_spec","type":"∀ {rho y : Int},\n  @Ne.{1} Int rho (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →\n    @Ne.{1} Int y (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →\n      And\n        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))\n          (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y))\n        (And\n          (@Dvd.dvd.{0} Int Int.instDvd\n            (@Nat.cast.{0} Int instNatCastInt\n              (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y))\n            y)\n          (And\n            (@Eq.{1} Int\n              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)\n                (@Nat.cast.{0} Int instNatCastInt\n                  (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y))\n                (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient rho y))\n              y)\n            (And\n              (@Ne.{1} Int (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient rho y)\n                (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))\n              (And\n                ((ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient rho y).natAbs.Coprime\n                  rho.natAbs)\n                (∀ (p : Nat),\n                  Nat.Prime p →\n                    @Dvd.dvd.{0} Nat Nat.instDvd p\n                        (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y) →\n                      @Dvd.dvd.{0} Nat Nat.instDvd p rho.natAbs)))))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.source_mem_own_primaryFibre","type":"∀ {rho : Int} {U : Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source}\n  {s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source},\n  @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n      (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n      (@SetLike.instMembership.{0, 0}\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n        ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n      U s →\n    And\n      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)\n        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))\n        (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryKeys rho U)\n        (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho\n          (@Prod.snd.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))))\n      (@Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n        (@SetLike.instMembership.{0, 0}\n          (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n          ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n          (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n        (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre rho U\n          (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho\n            (@Prod.snd.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s))))\n        s)"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralPrimaryOldformArithmetic","name":"ImbalancedChen.Part3.LiteralPrimaryOldformArithmetic.literal_primaryBeta_abl_licenses","type":"∀ {A : Nat} {a : Int} {T : Finset.{0} Nat} {H : Nat} {F : Finset.{0} Int} {nu : Nat} {lambda : Nat → Complex}\n  {omega : Int → Complex} {zy : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Output},\n  @Ne.{1} Complex\n      (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.beta\n        (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre a\n          (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.nonzeroSource\n            (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.carrier A a T H F))\n          nu)\n        lambda omega zy)\n      (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) →\n    have n :=\n      (@HDiv.hDiv.{0, 0, 0} Int Int Int (@instHDiv.{0} Int Int.instDiv) (@Prod.snd.{0, 0} Nat Int zy)\n          (@Nat.cast.{0} Int instNatCastInt nu)).natAbs;\n    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) nu)\n      (And (@Ne.{1} Int (@Prod.snd.{0, 0} Nat Int zy) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))\n        (And (@Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt nu) (@Prod.snd.{0, 0} Nat Int zy))\n          (And\n            (@Eq.{1} Int\n              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) (@Nat.cast.{0} Int instNatCastInt nu)\n                (@HDiv.hDiv.{0, 0, 0} Int Int Int (@instHDiv.{0} Int Int.instDiv) (@Prod.snd.{0, 0} Nat Int zy)\n                  (@Nat.cast.{0} Int instNatCastInt nu)))\n              (@Prod.snd.{0, 0} Nat Int zy))\n            (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)\n              (And (n.Coprime (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a.natAbs nu))\n                (And\n                  ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a.natAbs nu).Coprime\n                    (@Prod.fst.{0, 0} Nat Int zy))\n                  (∀ (qf v : Nat),\n                    @Eq.{1} Nat\n                      (ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart\n                        (ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102.oldformCofactor\n                          (@Prod.fst.{0, 0} Nat Int zy) qf v)\n                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a.natAbs nu))\n                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralPrimaryOldformArithmetic","name":"ImbalancedChen.Part3.LiteralPrimaryOldformArithmetic.literal_primaryFibre_abl_licenses","type":"∀ {A : Nat} {a : Int} {T : Finset.{0} Nat} {H : Nat} {F : Finset.{0} Int} {nu : Nat}\n  {s : ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source},\n  @Membership.mem.{0, 0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n      (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n      (@SetLike.instMembership.{0, 0}\n        (Finset.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source)\n        ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source\n        (@Finset.instSetLike.{0} ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.Source))\n      (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.primaryFibre a\n        (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.nonzeroSource\n          (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.carrier A a T H F))\n        nu)\n      s →\n    have z := @Prod.fst.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s);\n    have y := @Prod.snd.{0, 0} Nat Int (ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly.output s);\n    have n :=\n      (@HDiv.hDiv.{0, 0, 0} Int Int Int (@instHDiv.{0} Int Int.instDiv) y (@Nat.cast.{0} Int instNatCastInt nu)).natAbs;\n    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) nu)\n      (And (@Ne.{1} Int y (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))\n        (And (@Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt nu) y)\n          (And\n            (@Eq.{1} Int\n              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) (@Nat.cast.{0} Int instNatCastInt nu)\n                (@HDiv.hDiv.{0, 0, 0} Int Int Int (@instHDiv.{0} Int Int.instDiv) y\n                  (@Nat.cast.{0} Int instNatCastInt nu)))\n              y)\n            (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)\n              (And (n.Coprime (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a.natAbs nu))\n                (And ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a.natAbs nu).Coprime z)\n                  (∀ (qf v : Nat),\n                    @Eq.{1} Nat\n                      (ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart\n                        (ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102.oldformCofactor z qf v)\n                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a.natAbs nu))\n                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))"}
PART3_AUDIT_DECL {"axioms":[],"kind":"definition","level_parameters":[],"module":"ImbalancedChen.Part3LiteralPrimaryOldformArithmetic","name":"ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102.oldformCofactor","type":"Nat → Nat → Nat → Nat"}
PART3_AUDIT_DECL {"axioms":["propext","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralPrimaryOldformArithmetic","name":"_private.ImbalancedChen.Part3LiteralPrimaryOldformArithmetic.0.ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102.oldformCofactor_dvd","type":"∀ (z qf v : Nat),\n  @Dvd.dvd.{0} Nat Nat.instDvd (ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102.oldformCofactor z qf v) z"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralPrimaryOldformArithmetic","name":"_private.ImbalancedChen.Part3LiteralPrimaryOldformArithmetic.0.ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102.supportedPart_eq_one_of_coprime","type":"∀ {b a : Nat},\n  b.Coprime a →\n    @Eq.{1} Nat (ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart b a)\n      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.coprimePart.eq_1","type":"∀ (n d : Nat),\n  @Eq.{1} Nat (ImbalancedChen.Part3.CanonicalReciprocalData.coprimePart n d)\n    (∏ p ∈ n.primeFactors with Not (@Dvd.dvd.{0} Nat Nat.instDvd p d),\n      @HPow.hPow.{0, 0, 0} Nat Nat Nat\n        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p\n        (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat\n          (fun x => Nat) (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))\n          n.factorization p))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3PrimaryPrimeSupport","name":"ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart.eq_1","type":"∀ (n d : Nat),\n  @Eq.{1} Nat (ImbalancedChen.Part3.CanonicalReciprocalData.supportedPart n d)\n    (∏ p ∈ n.primeFactors with @Dvd.dvd.{0} Nat Nat.instDvd p d,\n      @HPow.hPow.{0, 0, 0} Nat Nat Nat\n        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p\n        (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat\n          (fun x => Nat) (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))\n          n.factorization p))"}
PART3_AUDIT_DECL {"axioms":["propext","Classical.choice","Quot.sound"],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore","name":"ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient.eq_1","type":"∀ (rho y : Int),\n  @Eq.{1} Int (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryQuotient rho y)\n    (@HDiv.hDiv.{0, 0, 0} Int Int Int (@instHDiv.{0} Int Int.instDiv) y\n      (@Nat.cast.{0} Int instNatCastInt\n        (ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly.rhoPrimaryNu rho y)))"}
PART3_AUDIT_DECL {"axioms":[],"kind":"theorem","level_parameters":[],"module":"ImbalancedChen.Part3LiteralPrimaryOldformArithmetic","name":"ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102.oldformCofactor.eq_1","type":"∀ (z qf v : Nat),\n  @Eq.{1} Nat (ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102.oldformCofactor z qf v)\n    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) z\n      ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) v qf).gcd z))"}
PART3_AUDIT_MODULE {"count":11,"module":"ImbalancedChen.Part3PrimaryPrimeSupport"}
PART3_AUDIT_MODULE {"count":24,"module":"ImbalancedChen.Part3LiteralReciprocalSource"}
PART3_AUDIT_MODULE {"count":22,"module":"ImbalancedChen.Part3FixedRhoPrimaryFiniteCore"}
PART3_AUDIT_MODULE {"count":6,"module":"ImbalancedChen.Part3LiteralPrimaryOldformArithmetic"}
PART3_AUDIT_COUNT 63
```

### final-working-tree

```text
command=["git", "status", "--porcelain", "--untracked-files=all"]
```
