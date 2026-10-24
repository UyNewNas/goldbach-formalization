import ImbalancedChen.Part3ActualNormalizedSmoothF
import ImbalancedChen.Part3NativePeriod64Sampling
import ImbalancedChen.Part3ActualSampledFourierLattice
import ImbalancedChen.Part3ActualWeightedSpectralBudget
import ImbalancedChen.Part3NativePeriod64Reconstruction
import ImbalancedChen.Part3DistributionTargets
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-
ACTUAL INTAKE -- 2026-10-23, prepared for ROOT's single compilation queue.
Frozen source: .lake/proof-continuation/drafts/20261023-P3-actual-literal-packet-finite-integral-adapter-SOURCEONLY.lean.txt
Source SHA256: 27ce336a869df1b2f460a10dcfc8d924a11f21eb69f39cb595467fcf3257badb
Only the import/provenance preamble and UTF-8 BOM handling change.
Mathematical bodies, namespaces, quantifiers and existing scope ends are retained.
Global noncomputable sections are valid Lean syntax and their matching ends are preserved.
Historical SOURCEONLY comments below describe provenance; this intake is UNCOMPILED / NOT OWNED.
-/

/-
SOURCEONLY -- 2026-10-23. No Lean/lake/compiler/typechecker/CI was run by this
worker. ROOT owns the single compilation queue. No actual .lean/cache/Git edit.

ACTUAL LITERAL INTERFACES USED:
 ImbalancedChen/Part3DistributionTargets.lean:
  CommonCompletedVariable.weight = 1_I(m)e(additivePhase*m);
  CoprimePacket.transformedCoefficient =
    1_(n,a)=1 beta(nu*n,z)e(-n/z).
The completed variable below has PHYSICAL phase k1/(64*V), not k1/64.
The signed negative cusp chart is defined with e(+n/z); only its norm,
not its complex value, is identified with the minus chart.

SOURCE DECLARATION ASSEMBLY (collect all imports at the beginning):
 1. actual-normalizedF-uniform-derivative-mass-astra f74bc534...,
    which contains smooth V2 fc9e3c72...; do not duplicate that parent.
 2. compact-coordinate-IBP-and-coefficient-continuity 933d9458...;
    native-torus-period64-actual-Fourier-sampling c346582f....
 3. actual-FT-sampled-weighted-lattice 778555ad....
    ROOT must use a new corrected copy supplying the explicit exponent to
    pow_le_pow_left₀ at old L129/144/185/429. Old hash stays unchanged.
 4. four-coordinate-period64-native-reconstruction 6e4a32cc...,
    independent peer34e067fd....
 5. actual-normalizedF-weighted-spectral-budget-astra-V2, SHA256
    f864ac9f87c17ffb5ea31f946269d8190c92f0b4a0cfe7792ca18a8dde676f89.
 6. This new file. All declarations below have complete by bodies.
Use one outer noncomputable section around extracted namespace bodies,
or close every parent's own section explicitly. Do not import fictitious
project modules named after source-only text files.

The main finite/integral HasSum theorem has NO Fourier separation, weighted
L1, derivative-mass or final spectral-estimate hypothesis. It consumes the
actual prior theorems. Its only packet-data conditions are literal finite
carriers, positive scales and normalized-coordinate geometry.

Actual q is the PHYSICAL spectral-test variable. The real support interval
is [Y0/16,16*Y0], and volume.real of that interval is (255/16)*Y0.
Every kernel bound below is the genuine sup norm of the given continuous
kernel restricted to that interval. Thus no measure/Jacobian/sup factor is
discarded in the exchange.

Fixed mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Additional source APIs actually read:
 MeasureTheory/Integral/DominatedConvergence.lean, blob
 e01402b504d1b8f96ed88bdd18266da7def493aa, L77--86:
   hasSum_integral_of_dominated_convergence, with summable integrable majorants.
 Integral/Bochner/Basic.lean, L288--290: integral_const_mul.
 Integral/Bochner/Set.lean, L489--491 and616--618:
   setIntegral_eq_integral_of_forall_compl_eq_zero;
   norm_setIntegral_le_of_norm_le_const.
 Measure/Lebesgue/Basic.lean, blobd6538e19f4368264267c876898b08d5453793ddb,
   L92--94: Real.volume_real_Icc_of_le.
 Topology/Order/Compact.lean, blob676c1bf5eb219ad6da734a31ac967130757e1421,
   L114--115: compactSpace_Icc.
 Topology/Algebra/InfiniteSum/Basic.lean, generated hasSum_sum L345--351.
 Measure/Restrict.lean, blob1c0d3412b2148bc91c4f4c0b2de56abcc502f975,
   L641--642: ae_restrict_mem.

This is a concrete actual packet adapter and convergence proof. The
classical 7/32 spectral inequality remains an INDEPENDENT OPEN input.
-/


/-
20261024q mechanical repair V2 candidate -- SOURCEONLY / UNCOMPILED / NOT OWNED.
Base: ImbalancedChen/Part3ActualLiteralPacketIntegral.lean
Base SHA256: 5ea9bc50456a7ad1c8b423cd5a4368ce6ccd86ca7e2d3bbf33c7da4faccf9554
V1 repaired phase-name qualification, structure syntax, coprime branch
simplification and ENNReal top notation. V2 repairs completed-weight
unfolding, explicitly supplies compactness of the same closed interval,
forces continuity-definition unfolding and resolves two style lint errors.
The original packet family, physical integrals, HasSum conclusions and
weighted absolute budgets are retained. This file claims no 7/32 estimate.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace P3ActualLiteralPacketIntegralSourceOnly

open ImbalancedChen.Part3 (CommonCompletedVariable CoprimePacket)
open P3NativePeriod64SamplingSourceOnly (D4 E4)
open P3Period64NativeReconstructionSourceOnly
  (norm_e point4 actualCoeff chi chiBump chi_tsupport_subset chi_mul_actual
   spectralMode spectralTest spectralTest_contDiff actual_global_separation_hasSum)
open ImbalancedChen.Part3.ActualNormalizedSmoothF (normalizedF normalizedF_contDiff)
open P3ActualSampledLatticeSourceOnly (testWeight)
open P3ActualWeightedSpectralBudgetSourceOnly (actualW actualW_nonneg)

def cuspPhase (negative : Bool) (z n : ℕ) : ℂ :=
  P3Period64NativeReconstructionSourceOnly.e ((if negative then (1 : ℝ) else -1)*(n : ℝ)/(z : ℝ))

def signedCoefficient (negative : Bool) (d : CoprimePacket) (n : ℕ) : ℂ :=
  if Nat.Coprime n d.residue then
    d.beta (d.multiplier*n) d.level * cuspPhase negative d.level n
  else 0

theorem signedCoefficient_false_eq_actual (d : CoprimePacket) (n : ℕ) :
    signedCoefficient false d n = d.transformedCoefficient n := by
  by_cases hc : Nat.Coprime n d.residue
  · rw [signedCoefficient, if_pos hc, CoprimePacket.transformedCoefficient, if_pos hc]
    apply congrArg (fun z : ℂ => d.beta (d.multiplier*n) d.level*z)
    dsimp [cuspPhase, P3Period64NativeReconstructionSourceOnly.e]
    push_cast
    congr 1
    ring
  · simp only [signedCoefficient, CoprimePacket.transformedCoefficient, if_neg hc]

theorem signedCoefficient_true_eq_plus (d : CoprimePacket) (n : ℕ) :
    signedCoefficient true d n =
      if Nat.Coprime n d.residue then
        d.beta (d.multiplier*n) d.level * P3Period64NativeReconstructionSourceOnly.e ((n : ℝ)/(d.level : ℝ))
      else 0 := by
  simp [signedCoefficient, cuspPhase]

theorem norm_signedCoefficient (negative : Bool) (d : CoprimePacket) (n : ℕ) :
    ‖signedCoefficient negative d n‖ = ‖d.transformedCoefficient n‖ := by
  rw [← signedCoefficient_false_eq_actual d n]
  by_cases hc : Nat.Coprime n d.residue
  · simp only [signedCoefficient, if_pos hc, norm_mul, cuspPhase, norm_e, mul_one]
  · simp only [signedCoefficient, if_neg hc]

def modePacket (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) : CoprimePacket :=
  { d with
    beta := fun y z =>
      d.beta y z *
        P3Period64NativeReconstructionSourceOnly.e
          ((k 2 : ℝ)/64*((y : ℝ)/U) + (k 3 : ℝ)/64*((z : ℝ)/Z)) }

theorem modePacket_beta_norm (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (y z : ℕ) :
    ‖(modePacket d k U Z).beta y z‖ = ‖d.beta y z‖ := by
  simp only [modePacket, norm_mul, norm_e, mul_one]

theorem modePacket_beta_finite_l2 (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ)
    (S : Finset (ℕ × ℕ)) :
    (∑ yz ∈ S, ‖(modePacket d k U Z).beta yz.1 yz.2‖^2) =
      ∑ yz ∈ S, ‖d.beta yz.1 yz.2‖^2 := by
  apply Finset.sum_congr rfl
  intro yz _hyz
  rw [modePacket_beta_norm]

theorem signedCoefficient_modePacket
    (negative : Bool) (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    signedCoefficient negative (modePacket d k U Z) n =
      signedCoefficient negative d n *
        P3Period64NativeReconstructionSourceOnly.e ((k 2 : ℝ)/64*(((d.multiplier*n : ℕ) : ℝ)/U) +
           (k 3 : ℝ)/64*((d.level : ℝ)/Z)) := by
  dsimp only [signedCoefficient, modePacket]
  by_cases hc : Nat.Coprime n d.residue
  · simp only [if_pos hc]
    ring
  · simp only [if_neg hc, zero_mul]

theorem norm_signedCoefficient_modePacket
    (negative : Bool) (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    ‖signedCoefficient negative (modePacket d k U Z) n‖ =
      ‖d.transformedCoefficient n‖ := by
  rw [signedCoefficient_modePacket, norm_mul, norm_e, mul_one, norm_signedCoefficient]

theorem modePacket_finite_fibre_l2
    (negative : Bool) (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (N : Finset ℕ) :
    (∑ n ∈ N, ‖signedCoefficient negative (modePacket d k U Z) n‖^2) =
      ∑ n ∈ N, ‖d.transformedCoefficient n‖^2 := by
  apply Finset.sum_congr rfl
  intro n _hn
  rw [norm_signedCoefficient_modePacket]

/- A concrete extension for kernels originally defined only away from0.
   Choosing a<=Y0/16 preserves the kernel on the entire physical region;
   this avoids pretending a singular positive-axis kernel is continuous
   at0 merely to fit the continuous-kernel parameter below. -/
def extendKernelFromHalfLine (a : ℝ) (K : C(Ici a, ℂ)) : C(ℝ, ℂ) where
  toFun q := K ⟨max q a,le_max_right q a⟩
  continuous_toFun := K.continuous.comp
    ((continuous_id.max continuous_const).subtype_mk (fun q => le_max_right q a))

theorem extendKernelFromHalfLine_eq (a : ℝ) (K : C(Ici a, ℂ))
    (q : ℝ) (hq : a ≤ q) : extendKernelFromHalfLine a K q = K ⟨q,hq⟩ := by
  apply congrArg K
  apply Subtype.ext
  exact max_eq_left hq

/- Ordinary frozen packet data. The finite row index can be a pair(nu,z),
   so no flattening or deletion of either nu or level is implicit.
   All coefficients/carriers/scales are selected before q and k. -/
structure PacketData (ι : Type*) where
  rows : Finset ι
  packet : ι → CoprimePacket
  nCarrier : ι → Finset ℕ
  lo : ℕ
  hi : ℕ
  V : ℝ
  U : ℝ
  Z : ℝ
  Y0 : ℝ
  rho : ℝ
  sigma : ℝ
  negativeCusp : Bool
  kernel : ι → ℕ → ℕ → C(ℝ, ℂ)
  V_pos : 0 < V
  U_pos : 0 < U
  Z_pos : 0 < Z
  Y0_pos : 0 < Y0
  m_normalized : ∀ m ∈ Finset.Ico lo hi, (m : ℝ)/V ∈ Ioo (-32 : ℝ) 32
  n_normalized : ∀ j ∈ rows, ∀ n ∈ nCarrier j,
    (((packet j).multiplier*n : ℕ) : ℝ)/U ∈ Ioo (-32 : ℝ) 32
  level_normalized : ∀ j ∈ rows, ((packet j).level : ℝ)/Z ∈ Ioo (-32 : ℝ) 32

namespace PacketData

variable {ι : Type*} (P : PacketData ι)

def mCarrier : Finset ℕ := Finset.Ico P.lo P.hi

def completed (k : D4 → ℤ) : CommonCompletedVariable :=
  { intervalLo := P.lo, intervalHi := P.hi,
    additivePhase := (k 1 : ℝ)/(64*P.V) }

theorem completed_weight_mem (k : D4 → ℤ) (m : ℕ) (hm : m ∈ P.mCarrier) :
    (P.completed k).weight m = P3Period64NativeReconstructionSourceOnly.e ((k 1 : ℝ)/64*((m : ℝ)/P.V)) := by
  dsimp only [mCarrier] at hm
  dsimp only [CommonCompletedVariable.weight, completed]
  rw [if_pos hm]
  dsimp only [P3Period64NativeReconstructionSourceOnly.e]
  push_cast
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem completed_weight_norm_mem (k : D4 → ℤ) (m : ℕ) (hm : m ∈ P.mCarrier) :
    ‖(P.completed k).weight m‖ = 1 := by
  rw [P.completed_weight_mem k m hm, norm_e]

/- The natural index is the positive p in a reflected negative-m block.
   In the ORIGINAL signed integer m=-p, its physical phase is -k1/(64V). -/
theorem reflected_original_m_phase (k : D4 → ℤ) (p : ℕ) :
    P3Period64NativeReconstructionSourceOnly.e ((k 1 : ℝ)/64*((p : ℝ)/P.V)) =
      P3Period64NativeReconstructionSourceOnly.e ((-(k 1 : ℝ)/(64*P.V))*((-(p : ℤ) : ℤ) : ℝ)) := by
  congr 1
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def physical (q : ℝ) : ℂ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    signedCoefficient P.negativeCusp (P.packet j) n * P.kernel j m n q *
      normalizedF P.rho P.sigma
        (point4 (q/P.Y0) ((m : ℝ)/P.V)
          ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
          (((P.packet j).level : ℝ)/P.Z))

def modeCore (k : D4 → ℤ) (q : ℝ) : ℂ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    (P.completed k).weight m *
      signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
        P.kernel j m n q

def modeFunction (k : D4 → ℤ) (q : ℝ) : ℂ :=
  spectralTest k P.Y0 q * P.modeCore k q

def modeTerm (k : D4 → ℤ) (q : ℝ) : ℂ :=
  actualCoeff P.rho P.sigma k * P.modeFunction k q

/- TRUE finite packet HasSum, derived from actual normalizedF reconstruction.
   No weighted-L1 or desired packet identity is a premise. -/
theorem pointwise_hasSum (J0 : ℕ) (q : ℝ) :
    HasSum (fun k : D4 → ℤ => P.modeTerm k q) (P.physical q) := by
  have hp (j : ι) (hj : j ∈ P.rows) (m : ℕ) (hm : m ∈ P.mCarrier)
      (n : ℕ) (hn : n ∈ P.nCarrier j) :
      HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
        spectralTest k P.Y0 q * (P.completed k).weight m *
          signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
            P.kernel j m n q)
        (signedCoefficient P.negativeCusp (P.packet j) n * P.kernel j m n q *
          normalizedF P.rho P.sigma
            (point4 (q/P.Y0) ((m : ℝ)/P.V)
              ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
              (((P.packet j).level : ℝ)/P.Z))) := by
    have h := actual_global_separation_hasSum P.rho P.sigma J0
      (q/P.Y0) ((m : ℝ)/P.V)
      ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
      (((P.packet j).level : ℝ)/P.Z)
      (P.m_normalized m hm) (P.n_normalized j hj n hn)
      (P.level_normalized j hj)
    apply (HasSum.mul_left
      (signedCoefficient P.negativeCusp (P.packet j) n * P.kernel j m n q) h).congr_fun
    intro k
    rw [P.completed_weight_mem k m hm, signedCoefficient_modePacket]
    dsimp [spectralTest]
    ring
  have hs := hasSum_sum (s := P.rows) (fun j hj =>
    hasSum_sum (s := P.mCarrier) (fun m hm =>
      hasSum_sum (s := P.nCarrier j) (fun n hn => hp j hj m hm n hn)))
  apply hs.congr_fun
  intro k
  dsimp [modeTerm, modeFunction, modeCore]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  ring

def region : Set ℝ := Icc (P.Y0/16) (16*P.Y0)

instance region_compactSpace : CompactSpace P.region :=
  isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact P.region)

theorem region_measure :
    (volume : Measure ℝ).real P.region = (255/16 : ℝ)*P.Y0 := by
  rw [region, Real.volume_real_Icc_of_le (by nlinarith [P.Y0_pos])]
  ring

def restrictedKernel (j : ι) (m n : ℕ) : C(P.region, ℂ) :=
  (P.kernel j m n).comp ⟨Subtype.val, continuous_subtype_val⟩

/- This is a REAL finite sum of REAL sup norms, not an unexplained hb. -/
def mass : ℝ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    ‖(P.packet j).transformedCoefficient n‖ * ‖P.restrictedKernel j m n‖

theorem mass_nonneg : 0 ≤ P.mass := by
  apply Finset.sum_nonneg
  intro j _hj
  apply Finset.sum_nonneg
  intro m _hm
  apply Finset.sum_nonneg
  intro n _hn
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem chi_scaled_zero_off (q : ℝ) (hq : q ∉ P.region) : chi (q/P.Y0) = 0 := by
  by_contra hn
  have hs := chi_tsupport_subset (subset_closure hn)
  have hl := (lt_div_iff₀ P.Y0_pos).1 hs.1
  have hu := (div_lt_iff₀ P.Y0_pos).1 hs.2
  apply hq
  constructor <;> nlinarith

theorem mode_zero_off (k : D4 → ℤ) (q : ℝ) (hq : q ∉ P.region) :
    P.modeTerm k q = 0 := by
  simp only [modeTerm, modeFunction, spectralTest, spectralMode,
    P.chi_scaled_zero_off q hq, Complex.ofReal_zero, zero_mul, mul_zero]

theorem physical_zero_off (q : ℝ) (hq : q ∉ P.region) : P.physical q = 0 := by
  have hF (v w z : ℝ) :
      normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) = 0 := by
    have hh := chi_mul_actual P.rho P.sigma (point4 (q/P.Y0) v w z)
    change (chi (q/P.Y0) : ℂ) *
      normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) =
        normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) at hh
    rw [P.chi_scaled_zero_off q hq] at hh
    simpa only [Complex.ofReal_zero, zero_mul] using hh.symm
  simp only [physical, hF, mul_zero, Finset.sum_const_zero]

theorem mode_continuous (k : D4 → ℤ) : Continuous (P.modeTerm k) := by
  have hs := (spectralTest_contDiff k P.Y0).continuous
  unfold modeTerm modeFunction modeCore
  fun_prop

theorem physical_continuous : Continuous P.physical := by
  have hf := (normalizedF_contDiff P.rho P.sigma).continuous
  have hp (v w z : ℝ) : Continuous (fun q : ℝ => point4 (q/P.Y0) v w z) := by
    apply (PiLp.continuous_toLp 2 (fun _ : D4 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hF (v w z : ℝ) :
      Continuous (fun q : ℝ => normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z)) :=
    hf.comp (hp v w z)
  unfold physical
  fun_prop

theorem mode_integrable (k : D4 → ℤ) : Integrable (P.modeTerm k) := by
  apply (P.mode_continuous k).integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  exact hq (P.mode_zero_off k q hn)

theorem physical_integrable : Integrable P.physical := by
  apply P.physical_continuous.integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  exact hq (P.physical_zero_off q hn)

theorem spectralMode_norm_le_one (k : D4 → ℤ) (t : ℝ) : ‖spectralMode k t‖ ≤ 1 := by
  have hc : 0 ≤ chi t := chiBump.nonneg
  have h1 : chi t ≤ 1 := chiBump.le_one
  simpa only [spectralMode, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_e, mul_one, abs_of_nonneg hc] using h1

theorem modeCore_norm_le (k : D4 → ℤ) (q : ℝ) (hq : q ∈ P.region) :
    ‖P.modeCore k q‖ ≤ P.mass := by
  have htri :
      ‖P.modeCore k q‖ ≤
        ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
          ‖(P.completed k).weight m *
            signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
              P.kernel j m n q‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _hj
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro m _hm
    exact norm_sum_le _ _
  apply htri.trans
  apply Finset.sum_le_sum
  intro j _hj
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro n _hn
  rw [norm_mul, norm_mul, P.completed_weight_norm_mem k m hm,
    norm_signedCoefficient_modePacket, one_mul]
  exact mul_le_mul_of_nonneg_left
    ((P.restrictedKernel j m n).norm_coe_le_norm ⟨q,hq⟩) (norm_nonneg _)

theorem modeTerm_norm_le (k : D4 → ℤ) (q : ℝ) (hq : q ∈ P.region) :
    ‖P.modeTerm k q‖ ≤ ‖actualCoeff P.rho P.sigma k‖ * P.mass := by
  calc
    ‖P.modeTerm k q‖ =
        ‖actualCoeff P.rho P.sigma k‖ *
          (‖spectralMode k (q/P.Y0)‖ * ‖P.modeCore k q‖) := by
      simp only [modeTerm, modeFunction, spectralTest, norm_mul]
    _ ≤ ‖actualCoeff P.rho P.sigma k‖ * (1 * P.mass) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (spectralMode_norm_le_one k (q/P.Y0))
          (P.modeCore_norm_le k q hq) (norm_nonneg _) (by norm_num)) (norm_nonneg _)
    _ = ‖actualCoeff P.rho P.sigma k‖ * P.mass := by rw [one_mul]

theorem weight_one_le (J0 : ℕ) (n : ℤ) : 1 ≤ testWeight J0 n := by
  unfold testWeight
  induction J0 with
  | zero => simp
  | succ j hj =>
      rw [pow_succ]
      calc
        (1 : ℝ) = 1*1 := by ring
        _ ≤ (1+|(n : ℝ)|)^j * (1+|(n : ℝ)|) :=
          mul_le_mul hj (by linarith [abs_nonneg (n : ℝ)])
            (by norm_num) (by positivity)

theorem actual_weighted_summable (J0 : ℕ) :
    Summable (fun k : D4 → ℤ =>
      ‖actualCoeff P.rho P.sigma k‖ * testWeight J0 (k 0)) := by
  exact (P3ActualSampledLatticeSourceOnly.actual_normalizedF_weighted_l1
    P.rho P.sigma J0).1

theorem actual_norm_summable (J0 : ℕ) :
    Summable (fun k : D4 → ℤ => ‖actualCoeff P.rho P.sigma k‖) := by
  apply (P.actual_weighted_summable J0).of_nonneg_of_le (fun _k => norm_nonneg _)
  intro k
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (weight_one_le J0 (k 0)) (norm_nonneg _)

/- REAL set-integral exchange. The dominated series is explicit:
      b_k(q)=norm(actualCoeff_k)*mass,
   and the restricted measure has finite total mass equal to
      volume.real [Y0/16,16Y0]=(255/16)*Y0. -/
theorem hasSum_setIntegral (J0 : ℕ) :
    HasSum (fun k : D4 → ℤ => ∫ q in P.region, P.modeTerm k q)
      (∫ q in P.region, P.physical q) := by
  let μ : Measure ℝ := volume.restrict P.region
  have hfin : (volume : Measure ℝ) P.region < ⊤ := isCompact_Icc.measure_lt_top
  let : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using hfin⟩
  have ha := P.actual_norm_summable J0
  apply MeasureTheory.hasSum_integral_of_dominated_convergence
    (fun k _q => ‖actualCoeff P.rho P.sigma k‖ * P.mass)
  · intro k
    exact (P.mode_continuous k).aestronglyMeasurable
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    exact P.modeTerm_norm_le k q hq
  · exact Filter.Eventually.of_forall (fun _q => ha.mul_right P.mass)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun q => P.pointwise_hasSum J0 q)

/- The global physical q integral equals the compact set integral because
   BOTH actual sides have already been proved zero outside that real region. -/
theorem hasSum_fullIntegral (J0 : ℕ) :
    HasSum (fun k : D4 → ℤ => ∫ q : ℝ, P.modeTerm k q)
      (∫ q : ℝ, P.physical q) := by
  have h := P.hasSum_setIntegral J0
  have hp : (∫ q in P.region, P.physical q) = ∫ q : ℝ, P.physical q :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun q hq => P.physical_zero_off q hq)
  rw [hp] at h
  apply h.congr_fun
  intro k
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun q hq => P.mode_zero_off k q hq)).symm

/- This is the exact per-mode integral consumer: the native coefficient
   multiplies the ACTUAL common completed-variable / modulated packet integral. -/
theorem hasSum_coefficient_times_modeIntegral (J0 : ℕ) :
    HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
      ∫ q : ℝ, P.modeFunction k q) (∫ q : ℝ, P.physical q) := by
  apply (P.hasSum_fullIntegral J0).congr_fun
  intro k
  symm
  exact integral_const_mul (actualCoeff P.rho P.sigma k) (P.modeFunction k)

/- An honest absolute convergence budget for the interchange, not the
   7/32 spectral saving. All continuous-kernel sup norms and physical
   measure are retained in mass*volume.real(region). -/
theorem norm_fullIntegral_le (J0 : ℕ) :
    ‖∫ q : ℝ, P.physical q‖ ≤
      actualW P.rho P.sigma J0 * P.mass * (volume : Measure ℝ).real P.region := by
  have hW := P.actual_weighted_summable J0
  have hvol : 0 ≤ (volume : Measure ℝ).real P.region := ENNReal.toReal_nonneg
  have hB (k : D4 → ℤ) :
      ‖∫ q in P.region, P.modeTerm k q‖ ≤
        (‖actualCoeff P.rho P.sigma k‖ * testWeight J0 (k 0)) *
          P.mass * (volume : Measure ℝ).real P.region := by
    calc
      ‖∫ q in P.region, P.modeTerm k q‖ ≤
          (‖actualCoeff P.rho P.sigma k‖ * P.mass) *
            (volume : Measure ℝ).real P.region :=
        norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
          (fun q hq => P.modeTerm_norm_le k q hq)
      _ ≤ ((‖actualCoeff P.rho P.sigma k‖ * testWeight J0 (k 0)) * P.mass) *
          (volume : Measure ℝ).real P.region := by
        apply mul_le_mul_of_nonneg_right _ hvol
        apply mul_le_mul_of_nonneg_right _ P.mass_nonneg
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (weight_one_le J0 (k 0)) (norm_nonneg _)
  have hmajor := (hW.mul_right P.mass).mul_right ((volume : Measure ℝ).real P.region)
  have hnorm := (P.hasSum_setIntegral J0).norm_le_of_bounded hmajor.hasSum hB
  have hp : (∫ q in P.region, P.physical q) = ∫ q : ℝ, P.physical q :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun q hq => P.physical_zero_off q hq)
  rw [hp] at hnorm
  calc
    ‖∫ q : ℝ, P.physical q‖ ≤
        ∑' k : D4 → ℤ,
          (‖actualCoeff P.rho P.sigma k‖ * testWeight J0 (k 0)) *
            P.mass * (volume : Measure ℝ).real P.region := hnorm
    _ = actualW P.rho P.sigma J0 * P.mass * (volume : Measure ℝ).real P.region := by
      rw [(hW.mul_right P.mass).tsum_mul_right ((volume : Measure ℝ).real P.region),
        hW.tsum_mul_right P.mass]; rfl

/- Genuine uniform rho/x budget is CONSUMED, not assumed. The finite family,
   every kernel and its physical sup/measure cost are allowed after C. -/
theorem uniform_xeta_integral_budget (J0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PacketData ι) (x : ℝ), 1 ≤ x →
      ∀ eta : ℝ, 0 ≤ eta → 0 ≤ P.rho → P.rho ≤ x^eta → |P.sigma| ≤ 1 →
      ‖∫ q : ℝ, P.physical q‖ ≤
        C * x^((4*(J0+3) : ℕ)*eta) * P.mass * (volume : Measure ℝ).real P.region ∧
      ‖∫ q : ℝ, P.physical q‖^2 ≤
        C^2 * x^((8*(J0+3) : ℕ)*eta) *
          (P.mass * (volume : Measure ℝ).real P.region)^2 := by
  obtain ⟨C,hC,hbudget⟩ :=
    P3ActualWeightedSpectralBudgetSourceOnly.actual_uniform_xeta_weighted_budget J0
  refine ⟨C,hC,?_⟩
  intro P x hx eta heta hrho hrX hsigma
  obtain ⟨_hs,hW,hWsq⟩ := hbudget x hx eta heta P.rho hrho hrX P.sigma hsigma
  let B : ℝ := P.mass * (volume : Measure ℝ).real P.region
  have hB : 0 ≤ B := mul_nonneg P.mass_nonneg ENNReal.toReal_nonneg
  have hN : ‖∫ q : ℝ, P.physical q‖ ≤ actualW P.rho P.sigma J0 * B := by
    simpa only [B, mul_assoc] using P.norm_fullIntegral_le J0
  refine ⟨?_,?_⟩
  · calc
      ‖∫ q : ℝ, P.physical q‖ ≤ actualW P.rho P.sigma J0 * B := hN
      _ ≤ (C * x^((4*(J0+3) : ℕ)*eta)) * B :=
        mul_le_mul_of_nonneg_right hW hB
      _ = C * x^((4*(J0+3) : ℕ)*eta) * P.mass *
          (volume : Measure ℝ).real P.region := by dsimp [B]; ring
  · calc
      ‖∫ q : ℝ, P.physical q‖^2 ≤ (actualW P.rho P.sigma J0 * B)^2 := by
        simpa only [pow_two] using mul_le_mul hN hN (norm_nonneg _)
          (mul_nonneg (actualW_nonneg _ _ _) hB)
      _ = (actualW P.rho P.sigma J0)^2 * B^2 := by rw [mul_pow]
      _ ≤ (C^2 * x^((8*(J0+3) : ℕ)*eta)) * B^2 :=
        mul_le_mul_of_nonneg_right hWsq (sq_nonneg B)
      _ = C^2 * x^((8*(J0+3) : ℕ)*eta) *
          (P.mass * (volume : Measure ℝ).real P.region)^2 := rfl

end PacketData
end P3ActualLiteralPacketIntegralSourceOnly
end

/-
EXACT REMAINING INTERFACES / NO FALSE CLOSURE

1. Instantiate PacketData.rows/nCarrier with the actual finite(nu,z) and n
   rectangles, packets with the original frozen beta, and kernel with the
   actual regular/exceptional/Plancherel kernel. All unit/coprime gates of
   CoprimePacket survive verbatim. There is no new beta norm hypothesis.
   The negative cusp branch is literally e(+n/z); positive and negative
   packets are NOT asserted equal as complex numbers.

2. The actual m carrier is ONE Finset.Ico(lo,hi) from the previously chosen
   global I_V, and the same completed variable is used for every row.
   A reflected negative original m=-p has physical phase -k1/(64V).
   The positive natural p adapter uses +k1/(64V). Every V,U,Z,Y0 denominator
   is explicit; the physical q support measure is (255/16)*Y0.

3. hasSum_coefficient_times_modeIntegral is the exact linear analytic
   consumer: native Fourier coefficient times an actual integral of the
   common completed-variable / genuinely modulated CoprimePacket family.
   The majorant is actual sup-kernel mass times the genuine coefficient
   norm series, derived from proved weighted summability. Global integrals
   are real Bochner integrals of continuous compactly supported functions.

4. The uniform_xeta bound is ONLY an interchange/absolute-family budget.
   Its mass factor contains all finite coefficient norms and continuous
   kernel sup norms. It is NOT the desired averaged spectral saving.
   The missing 7/32 spectral theorem remains OPEN; no final spectral target
   or uniform weighted-L1 conclusion was inserted as a hypothesis here.
   Actual regular/exceptional shell estimates, level Cauchy and formal
   continuous Plancherel remain obligations of that independent input.

5. r=4L, L=J0+3, costs4L*eta before squaring and8L*eta afterwards, from the
   real Astra supplier. The previous5*kappa slow-phase payment is not
   duplicated. Nothing here repairs or assumes the upstream supported
   RowSquareMass -> original smooth physical square comparison.

UNCOMPILED SOURCEONLY CANDIDATE. ROOT may compile only after source assembly
and the listed parent mechanical fixes, in its single authorized queue.
-/

