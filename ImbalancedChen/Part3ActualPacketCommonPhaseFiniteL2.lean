import ImbalancedChen.Part3ActualKPacketAdapter
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / NOT PASS -- 20261024u.
No compiler, helper, numerical experiment, Git operation or actual Lean edit.

Read actual anchors (SHA256):
 Part3ActualKPacketAdapter.lean
  12e330c48521506b320cfd4f39fa636486fad6124658b36a43190bdb958b43b4
 Part3ActualLiteralPacketIntegral.lean
  500b7c1476c8afb777551807f1f737b17d785aeafec401c7b691fd46b0b9aa55
 Part3NativePeriod64Reconstruction.lean
  724b2fd91c84aad404bad66a023d9c9151ffe21358c22a141e96bbf17b7c31bb

Manuscript read: chen-imbalanced-semiprimes/paper/source/manuscript-body.tex,
P3 lines 207--253: one common interval and one common additive phase across
levels, frozen coprime beta(nu*n,z)e(-n/z), normalized spectral inputs.

Pinned Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, read only:
 Analysis/Fourier/AddCircle.lean: orthonormal_fourier, fourier_eval_zero,
 fourier_coe_apply; InnerProductSpace/Orthonormal.lean: comp, inner_sum;
 MeasureTheory/Function/L2Space.lean: ContinuousMap.inner_toLp;
 Algebra/Order/BigOperators/Ring/Finset.lean: sum_mul_sq_le_sq_mul_sq.
The native hasSum_sq_fourierCoeff and multivariate Parseval were inspected.
For this FINITE packet the orthonormal finite-sum identity is the direct
specialization; no infinite truncation or spectral coefficient is needed.

This is an exact identity for the EXISTING modeCore under a single common
phase shift. Its value at zero is the actual modeCore. The full level and
n interference stays inside each m slice. It closes only finite common-
phase L2 bookkeeping and the evaluation operator cost card(mCarrier).
It does NOT turn an averaged phase estimate into a uniform spectral saving.
-/

namespace ImbalancedChen.Part3.ActualPacketCommonPhaseL2_20261024u
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3 (CommonCompletedVariable)
open ImbalancedChen.Part3.ActualKPacketAdapterSourceOnly
  (withKKernel kModeFunction withKKernel_modeFunction)

variable {ι : Type*}

/-- The original row and n sums, grouped at a fixed completed variable m. -/
def mSlice (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) (m : ℕ) : ℂ :=
  ∑ j ∈ P.rows, ∑ n ∈ P.nCarrier j,
    signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
      P.kernel j m n q

def phaseCoefficient (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) (m : ℕ) : ℂ :=
  (P.completed k).weight m * mSlice P k q m

/-- ONE phase shift shared by every row/level, on the original m carrier. -/
def phasePacket (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    C(UnitAddCircle, ℂ) :=
  ∑ m ∈ P.mCarrier, phaseCoefficient P k q m • fourier (m : ℤ)

theorem modeCore_eq_sum (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    P.modeCore k q = ∑ m ∈ P.mCarrier, phaseCoefficient P k q m := by
  unfold PacketData.modeCore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  simp only [phaseCoefficient, mSlice, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem phasePacket_zero (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    phasePacket P k q 0 = P.modeCore k q := by
  rw [modeCore_eq_sum]
  simp only [phasePacket, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, fourier_eval_zero, mul_one]

theorem common_shift_weight (P : PacketData ι) (k : D4 → ℤ) (s : ℝ)
    (m : ℕ) (hm : m ∈ P.mCarrier) :
    ({ P.completed k with additivePhase := (P.completed k).additivePhase + s } :
      CommonCompletedVariable).weight m =
        (P.completed k).weight m * fourier (m : ℤ) (s : UnitAddCircle) := by
  change m ∈ Finset.Ico P.lo P.hi at hm
  dsimp only [CommonCompletedVariable.weight, PacketData.completed]
  simp only [hm, ↓reduceIte, fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Identifies the auxiliary circle with a literal shared phase change. -/
theorem phasePacket_real (P : PacketData ι) (k : D4 → ℤ) (q s : ℝ) :
    phasePacket P k q (s : UnitAddCircle) =
      ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
        ({ P.completed k with additivePhase := (P.completed k).additivePhase + s } :
          CommonCompletedVariable).weight m *
            signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
              P.kernel j m n q := by
  rw [Finset.sum_comm]
  simp only [phasePacket, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [common_shift_weight P k s m hm]
  simp only [phaseCoefficient, mSlice, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Finite Parseval on the actual packet, with probability Haar measure. -/
theorem phasePacket_parseval (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    (∫ s : UnitAddCircle, ‖phasePacket P k q s‖^2 ∂AddCircle.haarAddCircle) =
      ∑ m ∈ P.mCarrier, ‖mSlice P k q m‖^2 := by
  have ho : Orthonormal ℂ (fun m : ℕ => fourierLp (T := (1 : ℝ)) 2 (m : ℤ)) :=
    (orthonormal_fourier (T := (1 : ℝ))).comp (fun m : ℕ => (m : ℤ))
      (by intro m n h; exact Int.ofNat_injective h)
  have hmap :
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (phasePacket P k q) =
        ∑ m ∈ P.mCarrier, phaseCoefficient P k q m •
          fourierLp (T := (1 : ℝ)) 2 (m : ℤ) := by
    simp only [phasePacket, map_sum, map_smul, fourierLp]
  have h := ho.inner_sum (phaseCoefficient P k q) (phaseCoefficient P k q)
    P.mCarrier
  simp only [← hmap, ContinuousMap.inner_toLp] at h
  simp only [Complex.mul_conj', Complex.conj_mul', ← Complex.ofReal_pow] at h
  have hcast := (integral_complex_ofReal
    (f := fun s : UnitAddCircle => ‖phasePacket P k q s‖^2)
    (μ := AddCircle.haarAddCircle)).symm.trans h
  have hr :
      (∫ s : UnitAddCircle, ‖phasePacket P k q s‖^2 ∂AddCircle.haarAddCircle) =
        ∑ m ∈ P.mCarrier, ‖phaseCoefficient P k q m‖^2 := by
    exact_mod_cast hcast
  rw [hr]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [phaseCoefficient, norm_mul, P.completed_weight_norm_mem k m hm, one_mul]

/-- The exact finite-band evaluation cost; no fixed-phase cancellation is assumed. -/
theorem modeCore_sq_le_phaseL2 (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    ‖P.modeCore k q‖^2 ≤ (P.mCarrier.card : ℝ) *
      (∫ s : UnitAddCircle, ‖phasePacket P k q s‖^2 ∂AddCircle.haarAddCircle) := by
  rw [phasePacket_parseval, modeCore_eq_sum]
  have ht := norm_sum_le P.mCarrier (phaseCoefficient P k q)
  have hs : ‖∑ m ∈ P.mCarrier, phaseCoefficient P k q m‖^2 ≤
      (∑ m ∈ P.mCarrier, ‖phaseCoefficient P k q m‖)^2 := by
    simpa only [pow_two] using mul_le_mul ht ht (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq P.mCarrier (fun _ : ℕ => (1 : ℝ))
    (fun m => ‖phaseCoefficient P k q m‖)
  have hnorm : (∑ m ∈ P.mCarrier, ‖phaseCoefficient P k q m‖^2) =
      ∑ m ∈ P.mCarrier, ‖mSlice P k q m‖^2 := by
    apply Finset.sum_congr rfl
    intro m hm
    simp only [phaseCoefficient, norm_mul, P.completed_weight_norm_mem k m hm, one_mul]
  have hc' : (∑ m ∈ P.mCarrier, ‖phaseCoefficient P k q m‖)^2 ≤
      (P.mCarrier.card : ℝ) * ∑ m ∈ P.mCarrier, ‖mSlice P k q m‖^2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hnorm] using hc
  exact hs.trans hc'

/-- The same identity with the actual K/q replacement, no kernel-bound premise. -/
theorem k_phasePacket_parseval (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (k : D4 → ℤ) (q : ℝ) :
    (∫ s : UnitAddCircle, ‖phasePacket (withKKernel P t) k q s‖^2
      ∂AddCircle.haarAddCircle) =
      ∑ m ∈ P.mCarrier, ‖mSlice (withKKernel P t) k q m‖^2 := by
  exact phasePacket_parseval (withKKernel P t) k q

/-- A consumer in the existing literal K-mode object, at every real q. -/
theorem kModeFunction_sq_le_phaseL2 (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) (q : ℝ) :
    ‖kModeFunction P t k q‖^2 ≤ (P.mCarrier.card : ℝ) *
      (∫ s : UnitAddCircle, ‖phasePacket (withKKernel P t) k q s‖^2
        ∂AddCircle.haarAddCircle) := by
  have htest := PacketData.spectralMode_norm_le_one k (q/P.Y0)
  have hn : ‖kModeFunction P t k q‖ ≤ ‖(withKKernel P t).modeCore k q‖ := by
    rw [← withKKernel_modeFunction]
    change ‖P3Period64NativeReconstructionSourceOnly.spectralMode k (q/P.Y0) *
      (withKKernel P t).modeCore k q‖ ≤ ‖(withKKernel P t).modeCore k q‖
    rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right htest (norm_nonneg ((withKKernel P t).modeCore k q))
  have hsq : ‖kModeFunction P t k q‖^2 ≤ ‖(withKKernel P t).modeCore k q‖^2 := by
    simpa only [pow_two] using mul_le_mul hn hn (norm_nonneg _) (norm_nonneg _)
  exact hsq.trans (modeCore_sq_le_phaseL2 (withKKernel P t) k q)

end
end ImbalancedChen.Part3.ActualPacketCommonPhaseL2_20261024u

/-
Remaining: ROOT compile and independent audit; exact same-mask smooth
physical-square comparison; normalized Kuznetsov regular/J/exceptional/
continuous branch identities; ABL coprime packet and continuous quadratic-
form inequalities; level average with one common interval/phase; 7/32
exceptional parameter and uniform saving. The average identity above
does not imply any one fixed phase is at most the average; the proved
evaluation inequality explicitly pays card(mCarrier). All levels and
all n cross terms remain in mSlice. No final target is closed.
-/

/-!
SOURCEONLY / UNCOMPILED / NOT PASS -- 20261024w.

ADDITIVE CONTINUATION: append these declarations AFTER the complete body of
20261024u-actual-packet-common-phase-finite-L2-SOURCEONLY.lean.txt
SHA256 c462be436de00d8145311435493e515049d50f890e30a741bd35b77f32cdac98.
Do not duplicate that body and do not import a fictional source-text module.
Its existing imports suffice; its actual K adapter imports Bochner.Set and
the continuity/integrability APIs used below. If ROOT puts the predecessor
in an actual admitted module, import that real module before this fragment.

Actual read-only anchors:
 Part3ActualKPacketAdapter.lean
  12e330c48521506b320cfd4f39fa636486fad6124658b36a43190bdb958b43b4
 Part3ActualLiteralPacketIntegral.lean
  500b7c1476c8afb777551807f1f737b17d785aeafec401c7b691fd46b0b9aa55
 P3 manuscript-body.tex L207--253, especially common interval/phase and
 the frozen signed coprime beta(nu*n,z)e(-n/z) coefficient.

Every physical integral below uses ORIGINAL q in [Y0/16,16*Y0].
The mSlice retains ALL row/level and n cross terms. The only removal of
the completed m-phase is finite common-phase Parseval in the predecessor.
Recovering the fixed phase pays card(mCarrier); integrating a complex
mode costs additionally the EXACT physical measure (255/16)*Y0.
No spectral-height independence beyond the existing t(j,m,n) data is
asserted, and no ABL, Kuznetsov, 7/32 or uniform saving is supplied.
-/

namespace ImbalancedChen.Part3.ActualPacketPhysicalRegionL2_20261024w
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ImbalancedChen.Part3.ActualKPacketAdapterSourceOnly
  (withKKernel kModeFunction withKKernel_modeFunction)
open ImbalancedChen.Part3.ActualPacketCommonPhaseL2_20261024u
  (mSlice phasePacket phasePacket_parseval k_phasePacket_parseval
   kModeFunction_sq_le_phaseL2)
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly

variable {ι : Type*}

theorem mSlice_continuous (P : PacketData ι) (k : D4 → ℤ) (m : ℕ) :
    Continuous (fun q : ℝ => mSlice P k q m) := by
  unfold mSlice
  fun_prop

theorem mSlice_sq_integrableOn_region (P : PacketData ι)
    (k : D4 → ℤ) (m : ℕ) :
    IntegrableOn (fun q : ℝ => ‖mSlice P k q m‖^2) P.region := by
  exact ((mSlice_continuous P k m).norm.pow 2).integrableOn_Icc

/-- Integrates finite Parseval in q without a Fubini or truncation premise. -/
theorem integrated_phasePacket_parseval (P : PacketData ι) (k : D4 → ℤ) :
    (∫ q in P.region, ∫ s : UnitAddCircle, ‖phasePacket P k q s‖^2
      ∂AddCircle.haarAddCircle) =
      ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖mSlice P k q m‖^2 := by
  simp_rw [phasePacket_parseval]
  exact integral_finsetSum P.mCarrier
    (fun m _hm => mSlice_sq_integrableOn_region P k m)

/-- The literal K/q slice, including the original signed frozen coefficient. -/
def kSlice (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (k : D4 → ℤ) (q : ℝ) (m : ℕ) : ℂ :=
  ∑ j ∈ P.rows, ∑ n ∈ P.nCarrier j,
    signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
      ((imaginaryOrderK (t j m n) q : ℂ)/(q : ℂ))

/-- The extension is eliminated only on the original physical region. -/
theorem k_mSlice_eq_literal_on_region (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) (q : ℝ) (hq : q ∈ P.region)
    (m : ℕ) : mSlice (withKKernel P t) k q m = kSlice P t k q m := by
  unfold mSlice kSlice
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro n _hn
  change
    signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
        extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) (t j m n) q =
      signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
        ((imaginaryOrderK (t j m n) q : ℂ)/(q : ℂ))
  rw [extendedKKernel_eq_on_physical_region P (t j m n) q hq]

theorem k_integrated_phasePacket_parseval (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) :
    (∫ q in P.region, ∫ s : UnitAddCircle,
      ‖phasePacket (withKKernel P t) k q s‖^2 ∂AddCircle.haarAddCircle) =
      ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2 := by
  change (∫ q in (withKKernel P t).region, ∫ s : UnitAddCircle,
    ‖phasePacket (withKKernel P t) k q s‖^2 ∂AddCircle.haarAddCircle) = _
  rw [integrated_phasePacket_parseval]
  apply Finset.sum_congr rfl
  intro m _hm
  apply setIntegral_congr_fun measurableSet_Icc
  intro q hq
  exact congrArg (fun z : ℂ => ‖z‖^2) (k_mSlice_eq_literal_on_region P t k q hq m)

theorem kModeFunction_continuous (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) :
    Continuous (kModeFunction P t k) := by
  rw [← withKKernel_modeFunction]
  have hs :=
    (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous
  unfold PacketData.modeFunction PacketData.modeCore
  fun_prop

theorem kModeFunction_sq_integrableOn_region (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) :
    IntegrableOn (fun q : ℝ => ‖kModeFunction P t k q‖^2) P.region := by
  exact ((kModeFunction_continuous P t k).norm.pow 2).integrableOn_Icc

theorem kModeFunction_zero_off_region (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) (q : ℝ) (hq : q ∉ P.region) :
    kModeFunction P t k q = 0 := by
  simp only [kModeFunction, spectralTest,
    P3Period64NativeReconstructionSourceOnly.spectralMode,
    P.chi_scaled_zero_off q hq, Complex.ofReal_zero, zero_mul]

/-- The original literal K mode consumes the integrated finite Parseval bound. -/
theorem kModeFunction_integrated_sq_le (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) :
    (∫ q in P.region, ‖kModeFunction P t k q‖^2) ≤
      (P.mCarrier.card : ℝ) *
        ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2 := by
  have hsum : IntegrableOn
      (fun q : ℝ => ∑ m ∈ P.mCarrier, ‖mSlice (withKKernel P t) k q m‖^2)
      P.region :=
    integrable_finsetSum P.mCarrier
      (fun m _hm => mSlice_sq_integrableOn_region (withKKernel P t) k m)
  have hpoint (q : ℝ) : ‖kModeFunction P t k q‖^2 ≤
      (P.mCarrier.card : ℝ) *
        ∑ m ∈ P.mCarrier, ‖mSlice (withKKernel P t) k q m‖^2 := by
    have h := kModeFunction_sq_le_phaseL2 P t k q
    rw [k_phasePacket_parseval] at h
    exact h
  have hle := integral_mono (kModeFunction_sq_integrableOn_region P t k)
    (hsum.const_mul (P.mCarrier.card : ℝ)) hpoint
  rw [integral_const_mul] at hle
  have hi (m : ℕ) : IntegrableOn
      (fun q : ℝ => ‖mSlice (withKKernel P t) k q m‖^2) P.region :=
    mSlice_sq_integrableOn_region (withKKernel P t) k m
  rw [integral_finsetSum P.mCarrier (fun m _hm => hi m)] at hle
  calc
    (∫ q in P.region, ‖kModeFunction P t k q‖^2) ≤
        (P.mCarrier.card : ℝ) *
          ∑ m ∈ P.mCarrier,
            ∫ q in P.region, ‖mSlice (withKKernel P t) k q m‖^2 := hle
    _ = (P.mCarrier.card : ℝ) *
        ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro m _hm
      apply setIntegral_congr_fun measurableSet_Icc
      intro q hq
      exact congrArg (fun z : ℂ => ‖z‖^2) (k_mSlice_eq_literal_on_region P t k q hq m)

/-- This also controls the full real-line L2 integral, by actual support. -/
theorem kModeFunction_full_sq_integral_le (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) :
    (∫ q : ℝ, ‖kModeFunction P t k q‖^2) ≤
      (P.mCarrier.card : ℝ) *
        ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2 := by
  have heq : (∫ q in P.region, ‖kModeFunction P t k q‖^2) =
      ∫ q : ℝ, ‖kModeFunction P t k q‖^2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun q hq => by
      rw [kModeFunction_zero_off_region P t k q hq]
      simp)
  rw [← heq]
  exact kModeFunction_integrated_sq_le P t k

/-- Elementary Cauchy--Schwarz on this exact physical interval.
Its continuity input is discharged for the actual mode in the consumer. -/
private theorem region_norm_integral_sq_le (P : PacketData ι)
    (f : ℝ → ℂ) (hf : Continuous f) :
    ‖∫ q in P.region, f q‖^2 ≤ (volume : Measure ℝ).real P.region *
      ∫ q in P.region, ‖f q‖^2 := by
  let M : ℝ := (volume : Measure ℝ).real P.region
  let A : ℝ := ∫ q in P.region, ‖f q‖
  let B : ℝ := ∫ q in P.region, ‖f q‖^2
  have hM : 0 < M := by
    dsimp [M]
    rw [P.region_measure]
    have hY := P.Y0_pos
    positivity
  have hAi : IntegrableOn (fun q : ℝ => ‖f q‖) P.region :=
    hf.norm.integrableOn_Icc
  have hBi : IntegrableOn (fun q : ℝ => ‖f q‖^2) P.region :=
    (hf.norm.pow 2).integrableOn_Icc
  have hCi : IntegrableOn (fun _q : ℝ => A^2) P.region :=
    continuous_const.integrableOn_Icc
  have hv : 0 ≤ ∫ q in P.region, (M*‖f q‖ - A)^2 :=
    integral_nonneg (fun q => sq_nonneg (M*‖f q‖ - A))
  have he : (∫ q in P.region, (M*‖f q‖ - A)^2) = M^2*B - M*A^2 := by
    calc
      (∫ q in P.region, (M*‖f q‖ - A)^2) =
          ∫ q in P.region, M^2*‖f q‖^2 - (2*M*A)*‖f q‖ + A^2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun q => by ring)
      _ = M^2*B - (2*M*A)*A + M*A^2 := by
        change (∫ q in P.region,
          ((fun x => M^2*‖f x‖^2) - (fun x => (2*M*A)*‖f x‖)) q +
            (fun _ : ℝ => A^2) q) = _
        rw [integral_add ((hBi.const_mul (M^2)).sub (hAi.const_mul (2*M*A))) hCi]
        simp only [Pi.sub_apply]
        rw [integral_sub (hBi.const_mul (M^2)) (hAi.const_mul (2*M*A)),
          integral_const_mul, integral_const_mul, setIntegral_const]
        rfl
      _ = M^2*B - M*A^2 := by ring
  rw [he] at hv
  have hAB : A^2 ≤ M*B := by
    by_contra hbad
    have hneg : M*B - A^2 < 0 := sub_neg.mpr (lt_of_not_ge hbad)
    have hprod := mul_neg_of_pos_of_neg hM hneg
    nlinarith
  have hn : ‖∫ q in P.region, f q‖ ≤ A := norm_integral_le_integral_norm f
  have hA : 0 ≤ A := integral_nonneg (fun q => norm_nonneg (f q))
  have hsq : ‖∫ q in P.region, f q‖^2 ≤ A^2 := by
    simpa only [pow_two] using mul_le_mul hn hn (norm_nonneg _) hA
  exact hsq.trans hAB

/-- Direct consumer for the ORIGINAL mode integral in literal reconstruction.
No phase average is promoted to a uniform saving, and no factor is dropped. -/
theorem kModeFunction_norm_fullIntegral_sq_le (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (k : D4 → ℤ) :
    ‖∫ q : ℝ, kModeFunction P t k q‖^2 ≤
      ((255/16 : ℝ)*P.Y0) * (P.mCarrier.card : ℝ) *
        ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2 := by
  have heq : (∫ q in P.region, kModeFunction P t k q) =
      ∫ q : ℝ, kModeFunction P t k q :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (kModeFunction_zero_off_region P t k)
  calc
    ‖∫ q : ℝ, kModeFunction P t k q‖^2 =
        ‖∫ q in P.region, kModeFunction P t k q‖^2 := by rw [heq]
    _ ≤ (volume : Measure ℝ).real P.region *
        ∫ q in P.region, ‖kModeFunction P t k q‖^2 :=
      region_norm_integral_sq_le P (kModeFunction P t k)
        (kModeFunction_continuous P t k)
    _ ≤ (volume : Measure ℝ).real P.region *
        ((P.mCarrier.card : ℝ) *
          ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2) :=
      mul_le_mul_of_nonneg_left (kModeFunction_integrated_sq_le P t k)
        ENNReal.toReal_nonneg
    _ = ((255/16 : ℝ)*P.Y0) * (P.mCarrier.card : ℝ) *
        ∑ m ∈ P.mCarrier, ∫ q in P.region, ‖kSlice P t k q m‖^2 := by
      rw [P.region_measure]
      ring

end
end ImbalancedChen.Part3.ActualPacketPhysicalRegionL2_20261024w

/-
EXACT REMAINING BOUNDARY:
* ROOT must elaborate/compile predecessor and this additive fragment.
* The RHS contains the complete signed row/n interference at each m.
  A nontrivial bound for that RHS is an independent spectral problem.
* This supplies neither same-mask smooth physical-square comparison nor
  normalized regular/J/exceptional/continuous branches, ABL level average,
  Kim--Sarnak 7/32 or the final manuscript D0,D1,D2 saving.
* The measure and carrier costs are explicit, including empty m carriers.
  No numerical constant, cutoff, exponent, phase or original source changes.
-/
