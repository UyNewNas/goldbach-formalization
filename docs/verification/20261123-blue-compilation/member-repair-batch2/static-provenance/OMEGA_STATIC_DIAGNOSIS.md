# Three Member failures: static diagnosis and existing-source reuse

Status: **UNCOMPILED static candidates**. No Lean, Lake, compiler, kernel replay,
type probe, or axiom probe was run for this task. No Member/main/P6/frozen source
was edited. The original failure log is retained at
`/workspace/blue-member-aggregate-evidence/attempt-1-build.log`; focused excerpts
are in `FAILURE_EXCERPTS.txt`.

## Project candidates

`project-proof-bodies.patch` and `candidate/ImbalancedChen/` contain two minimal
proof repairs. `STATIC_CANDIDATES.json` binds exact baseline/candidate SHA256s.

* `P2EnhancedActualBuchstabTransfer`: baseline `d0d669359d3e38743ae32ea5af5266b2c7d90f13f689618a500a8c213fd69913`,
  candidate `66365f77892e8c887f53050e6a4af628518e43fc65157017dc1a31994a8f45be`.
  Explicitly unfold `childWindow` in the finite Buchstab identity, and specify
  `(s := s) (t := t)` in the three sandwich applications. The failing implicit
  endpoint has no occurrence in those calls' hypotheses, so Lean cannot infer it
  from an untyped `have`. All 10 theorem headers and all six definitions are
  unchanged, as are imports and numeric tokens. The marked weights, original
  total `Q`, child floor level, signed remainder, and same-Theta normalization
  remain literal. Main's canonical path is absent; its docs/source-only
  `20261028-resume-30e/certificate_enhanced/` source is the exact baseline, also
  present at published project commits `d35adaf9` and `b2c20e78`. P6 has no file.
* `P2EnhancedCollisionFloorBound`: baseline `5acf6a9a285c1e0553002e74518aba0a25f4a6ea9841dac50c27933340803862`,
  candidate `8800e2a635fa6e023b30dcf1730cc522d2e1c3fb158cfb873f28fb4707de63ed`.
  Add `change N - ell = N - ell' at heq` before the existing `omega`; the log
  treats the unapplied beta-redex as an unrelated atom. Complementation is
  injective for the existing `ell,ell' < N` hypotheses. All six theorem headers,
  numeric constants and assumptions remain unchanged. Main has the exact
  baseline; P6 has no file. The complete labelled divisor `d*l.prod`, factor
  `1/d`, tuple multiplicity, and per-tuple scope remain unchanged.

The reference main HEAD when read was
`f25503c0ebf598f9be9ed417899eda9798ac0a13`. No already-published project fix was
found in the exact canonical/docs paths inspected. The sole build owner must
adopt and validate the candidates; this report claims no compiler acceptance.

## Native Uniform: missing selected implementation, existing published supplier

The native consumer baseline SHA256 is
`29294b01f78b188a399877d30b1329a85c2f3fa3442efa5cb1111552258e97cf`.
Its source authority is native commit `09b97db5764ade1246bfb77206baa1b124760958`,
`research/wu2008/src/MathlibNt/Wu2008DoubleSieve/Omega3XBuchstabUniform.lean`.
Line 34 calls `roughCount_uniform_buchstab_fixed`, absent from its selected
old provider. The old theorem only covers `[u0,100]`.

This is **an implementation-selection omission**, not evidence of a manuscript
mathematical gap. Public upstream commit
[`9d4c3a4010d42aedd9e7231bf94386019cfffccc`](https://github.com/subfish-zhou/goldbach-lean/tree/9d4c3a4010d42aedd9e7231bf94386019cfffccc)
already contains the exact required interface in its research source, and the
consumer is byte-identical to the current failing consumer. Three small public
source/API reads identified the current upstream commit; subsequent source and
receipt reads used that exact commit's already-local Git objects. No large
archive or compiled object was downloaded.

The precise published interface is:

```lean
theorem roughCount_uniform_buchstab_fixed (M : ℕ) (hM : 2 ≤ M)
    {u₀ : ℝ} (hu₀ : 1 < u₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 1 < X ∧ ∀ x ≥ X, ∀ u ∈ Set.Icc u₀ (M : ℝ),
      0 < u * buchstab u * x / Real.log x ∧
      |(roughCount x (x ^ (1 / u)) : ℝ) /
        (u * buchstab u * x / Real.log x) - 1| < ε
```

`Omega3XGeometryCompact.lean:16` chooses `u0,M` after `k,δ` but before `N`,
all source boxes, labels, primes, and `s,t`. Here
`η = min (δ^(k+1)) (1/2-δ)/10`, `u0 = 1+2δ/(1/2-δ)`, and `1/η < M`.
The interval is not universally bounded by 100. For example `k=3,δ=1/4`
already makes this chosen cap greater than 2560. Thus a rename to the old
cap100 theorem, a new `M≤100` premise, or restriction on `k,δ` would be invalid.
The caller's fixed-domain-before-threshold order and qualitative relative
convergence remain literal; no logarithmic rate is inferred.

The three published research suppliers have SHA256s:

| Module suffix | Published research SHA256 |
| --- | --- |
| `LiLiuPrereqBuchstabUniformAbel` | `51a5ac728e115811f9abffb02e15df8db8fcf0fc0da1124fdf4d61f12c240563` |
| `LiLiuPrereqBuchstabBands` | `bfc465b9e55d597afeac1e2485dad992c591a30d2089ddc9ac7b738d63930350` |
| `LiLiuPrereqBuchstabUniform` | `9b8f109fc3f3ac21cb20db707f1e19e68ba86ad5568f547a72c3189ec18c242e` |

All original public declarations remain with identical types modulo six unused
hypothesis binder spellings (`hU`/`_hU`, `hk`/`_hk`); all original definition
bodies remain unchanged. The canonical compressed copies remove old APIs and
are unsuitable for wholesale overlay. The four external direct dependencies
`PrimeSums`, `Bounds`, `Integral`, and `BaseEstimate` were compared byte-for-byte
to current selected Member sources and are identical. Published and current
Lean are `v4.33.0-rc1`, mathlib revision
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## Preferred minimal integration proposal

Keep the old cap100 suppliers byte-exact. Add a separate compat/extension module
which imports the old `LiLiuPrereqBuchstabUniform`, and copy only the following
already-published proofs in namespace `LiLiuPrereqBuchstab`:

1. Abel additions: `abs_shift_mul_buchstabSlope_le_two`,
   `abs_buchstabPrimeKernelSlope_le_unrestricted`, private
   `abs_buchstabPrimeKernelSlope_le_coarse`,
   `integrableOn_buchstabPrimeKernelSlope_unrestricted`,
   `buchstabPrimeKernel_sum_Ioc_error_le_unrestricted`,
   `buchstabPrimeKernel_sum_Ico_error_le_unrestricted`.
2. Band addition: `roughCount_buchstab_band_error_unrestricted`.
3. Uniform additions: `rpow_cutoff_bounds_fixed`,
   `roughCount_relative_band_error_fixed`, `roughCount_uniform_error_bound_fixed`,
   `tendsto_uniform_buchstab_majorant_fixed`, `roughCount_uniform_buchstab_fixed`.

Copy the existing private helper proofs `kernel_range`,
`kernel_hasDerivAt_on_band`, `kernel_endpoint_le`, `bands_pos`,
`buchstab_main_decomposition`, and `roughCount_base_band_error` into the extension
as private declarations, before their users. Their old-module private aliases
cannot be referenced directly across module boundaries. The extension needs
the original `Set MeasureTheory Filter` opens and `BigOperators Topology`
scopes. The published `buchstabPrimeKernel_abel_unrestricted` is not required
by this dependency chain. No new analytic argument is necessary. This proposal
adds 11 public and seven private declarations, all copied from existing source.

Only native consumers of the generic interface need the extension import.
The immediate failing module's two direct consumers are
`Omega3XBuchstabSource` and `Gamma16MassGeometry`. The latter also calls the
same missing fixed-cap interface. `NonunitRoughUniform` calls it independently;
its downstream consumers are `SecondFunctionalHighNonunitRoughFamily` and
`InclusiveRoughUniform`. All these calls retain their existing statements.
No extension was created and no native source was edited by this task.

## Existing acceptance evidence and its limit

`NATIVE_SUPPLIER_PROVENANCE.json` binds public commit/blob/SHA, exact focused
source-manifest rows, current dependency comparisons, and historical receipts.
`remote-main-supplier/FOCUSED_PRODUCTION_BINDINGS.json` records the four exact
source, object, and individual receipt hashes from published production records.

The published source manifest SHA256 is
`2079027dc274619f04f255a0dcaecc0410ea914a2af56994d1a979f916892455`.
The published production verification SHA256 is
`d13f60c24222fb0882fadd6ca289ca45eff8e62b2635ff53bd259fd02125494a`.
The acceptance validation SHA256 is
`676e4d73645d6d0173027072a42e794ca0c516e4214584c456a475ce6551da14`.
All downloaded/extracted record hashes checked against that validation match.

Those records bind the three parameterized research sources and unchanged
consumer above. They report 4151 verified modules, 3500 promoted actual source
compilation receipts, 651 unchanged receipts, and exit 0 for cached receipt
verification, final literal/axiom acceptance, and final theorem kernel replay.
That final verification itself ran zero fresh source compilations. The final
theorem axiom reports use `propext`, `Classical.choice`, and `Quot.sound`.
The individual supplier receipts have published SHA bindings, but their payloads
are absent from this Git tree. This is prior acceptance evidence, not a local
compiler/kernel/axiom result or binary-artifact qualification for the proposed
extension. The Member owner must validate any adopted extension under the
existing guard and audit its public declarations.

## Manuscript scope

Nov6 `sieve-appendix.tex:497–535` retains the positive marked family, original
total level and physical child state. Lines 638–646 and 741–744 retain distinct
selected primes and the fixed positive-box collision error; the project
candidates keep the corresponding exact finite statements. Lines 550–561
identify the switched rough family and fixed positive exponents. Lines 775–792,
especially “Prime summation and the rough-number formula on fixed positive
boxes”, give the Buchstab switched mass while retaining the separate unit
surface. These require uniformity on each chosen fixed positive box, not a
universal depth-independent cap. The existing generic-M rough-count proof
supplies that scope; no Wu endpoint theorem or published numerical conclusion
is used as a shortcut in either the current consumer or this reuse proposal.
