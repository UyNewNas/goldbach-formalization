import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import Mathlib.Tactic

/-!
SOURCEONLY 20261024s -- UNCOMPILED, NOT PASS, no acceptance credit.
No Lean/lake/helper/numerical/Git command was run by this worker.
ROOT owns compilation and acceptance.

Actual read-only source anchors, SHA256:
 Part3ActualLiteralPacketIntegral.lean
  500b7c1476c8afb777551807f1f737b17d785aeafec401c7b691fd46b0b9aa55
 Part3ImaginaryOrderKPositiveAxis.lean
  5b8926ef4c08172773d7f9e7736eb85e6692ea71e8654be1452c1245ad900658
 Part3ImaginaryOrderKExplicitMajorant.lean
  aa3f3c624d0541927b35971679730bc53ef0fccbdde39aab1aed5d4f5f9478ed
The first two are ROOT-reported strict compile PASS; this draft does not
independently certify them. The explicit-majorant import still awaits
ROOT compilation. This anchor includes ROOT's three lint-only repairs
after the original d51bfeb3337864e592092d12d501ee23cdc7936da74ae4180088b005977db854.
No equality of arbitrary kernels or spectral estimate
is an input below. A record update chooses the specific K kernel.

Each finite row, carrier, packet, coefficient, phase, scale and support
region is retained definitionally. The real order parameter may depend
on (j,m,n), but never on q or the Fourier mode. A common spectral height
is the specialization t := fun _ _ _ => T. No tail is truncated here.

Manuscript checked: chen-imbalanced-semiprimes/paper/source/manuscript-body.tex,
lines 207--253: common interval/phase, frozen coprime beta(nu*n,z)e(-n/z),
normalized Kuznetsov, ABL, Kim--Sarnak 7/32 and exceptional inputs.
This adapter proves only exact K/q packet reconstruction and an absolute
interchange budget. It does not construct the Kuznetsov normalization,
the remaining J/exceptional/Plancherel branches or any spectral saving;
it does not close hLower/hUpper or the smooth physical-square comparison.
-/

namespace ImbalancedChen.Part3.ActualKPacketAdapterSourceOnly
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
  (point4 actualCoeff spectralTest spectralMode chi chi_mul_actual)
open ImbalancedChen.Part3.ActualNormalizedSmoothF (normalizedF)
open P3ActualWeightedSpectralBudgetSourceOnly (actualW actualW_nonneg)
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly

variable {ι : Type*}

/-- Only the kernel field is replaced, using the original physical cutoff. -/
def withKKernel (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ) : PacketData ι :=
  { P with
    kernel := fun j m n =>
      extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) (t j m n) }

/-- All data used for the frozen coefficient and common interval survive. -/
theorem withKKernel_frozen (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ) :
    (withKKernel P t).rows = P.rows ∧
    (withKKernel P t).packet = P.packet ∧
    (withKKernel P t).nCarrier = P.nCarrier ∧
    (withKKernel P t).mCarrier = P.mCarrier ∧
    (withKKernel P t).completed = P.completed ∧
    (withKKernel P t).region = P.region ∧
    (withKKernel P t).Y0 = P.Y0 ∧
    (withKKernel P t).rho = P.rho ∧
    (withKKernel P t).sigma = P.sigma ∧
    (withKKernel P t).negativeCusp = P.negativeCusp ∧
    (withKKernel P t).V = P.V ∧
    (withKKernel P t).U = P.U ∧
    (withKKernel P t).Z = P.Z := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Equality of continuous maps, not a supplied kernel-identification hypothesis. -/
theorem withKKernel_restrictedKernel (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (j : ι) (m n : ℕ) :
    (withKKernel P t).restrictedKernel j m n = restrictedKKernel P (t j m n) := by
  rfl

theorem withKKernel_restrictedKernel_apply (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (j : ι) (m n : ℕ) (q : P.region) :
    (withKKernel P t).restrictedKernel j m n q =
      (imaginaryOrderK (t j m n) (q : ℝ) : ℂ)/((q : ℝ) : ℂ) := by
  rw [withKKernel_restrictedKernel]
  exact restrictedKKernel_eq P (t j m n) q

theorem withKKernel_restrictedKernel_norm_le (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (j : ι) (m n : ℕ) :
    ‖(withKKernel P t).restrictedKernel j m n‖ ≤ 512/P.Y0^2 := by
  rw [withKKernel_restrictedKernel]
  exact restrictedKKernel_norm_le P (t j m n)

/-- The original literal physical packet with the actual K/q in every summand. -/
def kPhysical (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ) (q : ℝ) : ℂ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    signedCoefficient P.negativeCusp (P.packet j) n *
      ((imaginaryOrderK (t j m n) q : ℂ)/(q : ℂ)) *
      normalizedF P.rho P.sigma
        (point4 (q/P.Y0) ((m : ℝ)/P.V)
          ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
          (((P.packet j).level : ℝ)/P.Z))

/-- Same common completed variable and genuinely modulated coprime packets. -/
def kModeFunction (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (k : D4 → ℤ) (q : ℝ) : ℂ :=
  spectralTest k P.Y0 q *
    (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
      (P.completed k).weight m *
        signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
          ((imaginaryOrderK (t j m n) q : ℂ)/(q : ℂ)))

lemma kPhysical_zero_off (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (q : ℝ) (hq : q ∉ P.region) : kPhysical P t q = 0 := by
  have hF (v w z : ℝ) :
      normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) = 0 := by
    have hh := chi_mul_actual P.rho P.sigma (point4 (q/P.Y0) v w z)
    change (chi (q/P.Y0) : ℂ) *
      normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) =
        normalizedF P.rho P.sigma (point4 (q/P.Y0) v w z) at hh
    rw [P.chi_scaled_zero_off q hq] at hh
    simpa only [Complex.ofReal_zero, zero_mul] using hh.symm
  simp only [kPhysical, hF, mul_zero, Finset.sum_const_zero]

/-- Support makes the literal singular quotient agree globally with the extension. -/
theorem withKKernel_physical (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ) :
    (withKKernel P t).physical = kPhysical P t := by
  funext q
  by_cases hq : q ∈ P.region
  · change
      (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
        signedCoefficient P.negativeCusp (P.packet j) n *
          extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) (t j m n) q *
          normalizedF P.rho P.sigma
            (point4 (q/P.Y0) ((m : ℝ)/P.V)
              ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
              (((P.packet j).level : ℝ)/P.Z))) = kPhysical P t q
    unfold kPhysical
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    rw [extendedKKernel_eq_on_physical_region P (t j m n) q hq]
  · rw [(withKKernel P t).physical_zero_off q hq, kPhysical_zero_off P t q hq]

theorem withKKernel_modeFunction (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (k : D4 → ℤ) : (withKKernel P t).modeFunction k = kModeFunction P t k := by
  funext q
  change spectralTest k P.Y0 q *
    (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
      (P.completed k).weight m *
        signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n *
          extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) (t j m n) q) =
      kModeFunction P t k q
  unfold kModeFunction
  by_cases hq : q ∈ P.region
  · apply congrArg (fun z : ℂ => spectralTest k P.Y0 q * z)
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    rw [extendedKKernel_eq_on_physical_region P (t j m n) q hq]
  · simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
      Complex.ofReal_zero, zero_mul]

theorem kPhysical_integrable (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ) :
    Integrable (kPhysical P t) := by
  rw [← withKKernel_physical P t]
  exact (withKKernel P t).physical_integrable

theorem kModeFunction_integrable (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
    (k : D4 → ℤ) : Integrable (kModeFunction P t k) := by
  rw [← withKKernel_modeFunction P t k]
  have hc : Continuous ((withKKernel P t).modeFunction k) := by
    have hs :=
      (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous
    unfold PacketData.modeFunction PacketData.modeCore
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  apply hq
  change spectralTest k P.Y0 q * _ = 0
  simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hn,
    Complex.ofReal_zero, zero_mul]

/-- Reuse the already proved literal-packet integral exchange, with actual K/q. -/
theorem k_hasSum_coefficient_times_modeIntegral (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (J0 : ℕ) :
    HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
      ∫ q : ℝ, kModeFunction P t k q) (∫ q : ℝ, kPhysical P t q) := by
  have h := (withKKernel P t).hasSum_coefficient_times_modeIntegral J0
  change HasSum (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
    ∫ q : ℝ, (withKKernel P t).modeFunction k q)
      (∫ q : ℝ, (withKKernel P t).physical q) at h
  simpa only [withKKernel_modeFunction, withKKernel_physical] using h

/-- Real coefficient mass, with the original finite rows and all m,n copies. -/
def coefficientMass (P : PacketData ι) : ℝ :=
  ∑ j ∈ P.rows, ∑ _m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    ‖(P.packet j).transformedCoefficient n‖

lemma coefficientMass_nonneg (P : PacketData ι) : 0 ≤ coefficientMass P := by
  apply Finset.sum_nonneg
  intro j _hj
  apply Finset.sum_nonneg
  intro m _hm
  apply Finset.sum_nonneg
  intro n _hn
  exact norm_nonneg _

/-- Derived sup budget for this actual record; no generic kernel bound is assumed. -/
theorem withKKernel_mass_le (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ) :
    (withKKernel P t).mass ≤ coefficientMass P * (512/P.Y0^2) := by
  calc
    (withKKernel P t).mass =
        ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
          ‖(P.packet j).transformedCoefficient n‖ *
            ‖(withKKernel P t).restrictedKernel j m n‖ := rfl
    _ ≤ ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
          ‖(P.packet j).transformedCoefficient n‖ * (512/P.Y0^2) := by
      apply Finset.sum_le_sum
      intro j _hj
      apply Finset.sum_le_sum
      intro m _hm
      apply Finset.sum_le_sum
      intro n _hn
      exact mul_le_mul_of_nonneg_left
        (withKKernel_restrictedKernel_norm_le P t j m n) (norm_nonneg _)
    _ = coefficientMass P * (512/P.Y0^2) := by
      simp only [coefficientMass, Finset.sum_mul]

/-- Both the actual sup bound 512/Y0^2 and physical measure (255/16)Y0 remain. -/
theorem k_norm_fullIntegral_le (P : PacketData ι)
    (t : ι → ℕ → ℕ → ℝ) (J0 : ℕ) :
    ‖∫ q : ℝ, kPhysical P t q‖ ≤
      actualW P.rho P.sigma J0 * coefficientMass P * (512/P.Y0^2) *
        ((255/16 : ℝ)*P.Y0) := by
  have h := (withKKernel P t).norm_fullIntegral_le J0
  change ‖∫ q : ℝ, (withKKernel P t).physical q‖ ≤
    actualW P.rho P.sigma J0 * (withKKernel P t).mass *
      (volume : Measure ℝ).real P.region at h
  rw [withKKernel_physical] at h
  calc
    ‖∫ q : ℝ, kPhysical P t q‖ ≤
        actualW P.rho P.sigma J0 * (withKKernel P t).mass *
          (volume : Measure ℝ).real P.region := h
    _ ≤ actualW P.rho P.sigma J0 *
        (coefficientMass P * (512/P.Y0^2)) * (volume : Measure ℝ).real P.region :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (withKKernel_mass_le P t)
          (actualW_nonneg _ _ _)) ENNReal.toReal_nonneg
    _ = actualW P.rho P.sigma J0 * coefficientMass P * (512/P.Y0^2) *
        ((255/16 : ℝ)*P.Y0) := by
      rw [P.region_measure]
      ring

/-- The original rho/x exponents are preserved, with a proved K-kernel budget. -/
theorem k_uniform_xeta_integral_budget (J0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PacketData ι) (t : ι → ℕ → ℕ → ℝ)
      (x : ℝ), 1 ≤ x → ∀ eta : ℝ, 0 ≤ eta →
      0 ≤ P.rho → P.rho ≤ x^eta → |P.sigma| ≤ 1 →
      ‖∫ q : ℝ, kPhysical P t q‖ ≤
        C * x^((4*(J0+3) : ℕ)*eta) *
          (coefficientMass P * (512/P.Y0^2)) * ((255/16 : ℝ)*P.Y0) ∧
      ‖∫ q : ℝ, kPhysical P t q‖^2 ≤
        C^2 * x^((8*(J0+3) : ℕ)*eta) *
          ((coefficientMass P * (512/P.Y0^2)) * ((255/16 : ℝ)*P.Y0))^2 := by
  obtain ⟨C,hC,hbudget⟩ :=
    PacketData.uniform_xeta_integral_budget (ι := ι) J0
  refine ⟨C,hC,?_⟩
  intro P t x hx eta heta hrho hrX hsigma
  obtain ⟨hlin,hsq⟩ := hbudget (withKKernel P t) x hx eta heta hrho hrX hsigma
  change ‖∫ q : ℝ, (withKKernel P t).physical q‖ ≤
    C * x^((4*(J0+3) : ℕ)*eta) * (withKKernel P t).mass *
      (volume : Measure ℝ).real P.region at hlin
  change ‖∫ q : ℝ, (withKKernel P t).physical q‖^2 ≤
    C^2 * x^((8*(J0+3) : ℕ)*eta) *
      ((withKKernel P t).mass * (volume : Measure ℝ).real P.region)^2 at hsq
  rw [withKKernel_physical] at hlin hsq
  have hfront : 0 ≤ C * x^((4*(J0+3) : ℕ)*eta) := by positivity
  have hfrontsq : 0 ≤ C^2 * x^((8*(J0+3) : ℕ)*eta) := by positivity
  have hvol : 0 ≤ (volume : Measure ℝ).real P.region := ENNReal.toReal_nonneg
  have hB : 0 ≤ (withKKernel P t).mass * (volume : Measure ℝ).real P.region :=
    mul_nonneg (withKKernel P t).mass_nonneg hvol
  have hD : 0 ≤ (coefficientMass P * (512/P.Y0^2)) *
      (volume : Measure ℝ).real P.region := by
    apply mul_nonneg _ hvol
    exact mul_nonneg (coefficientMass_nonneg P) (by positivity)
  have hBD : (withKKernel P t).mass * (volume : Measure ℝ).real P.region ≤
      (coefficientMass P * (512/P.Y0^2)) * (volume : Measure ℝ).real P.region :=
    mul_le_mul_of_nonneg_right (withKKernel_mass_le P t) hvol
  have hBDsq : ((withKKernel P t).mass * (volume : Measure ℝ).real P.region)^2 ≤
      ((coefficientMass P * (512/P.Y0^2)) * (volume : Measure ℝ).real P.region)^2 := by
    simpa only [pow_two] using mul_le_mul hBD hBD hB hD
  constructor
  · have hbound := hlin.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (withKKernel_mass_le P t) hfront) hvol)
    simpa only [P.region_measure] using hbound
  · have hbound := hsq.trans (mul_le_mul_of_nonneg_left hBDsq hfrontsq)
    simpa only [P.region_measure] using hbound

end
end ImbalancedChen.Part3.ActualKPacketAdapterSourceOnly

/-
REMAINING EXACT BOUNDARY:
1. ROOT must compile the explicit-majorant module and this file. All bodies
   above are source candidates, not a claim of strict compilation.
2. This is a real replacement record, not a theorem about an arbitrary
   original P.kernel. Relating a full Kuznetsov kernel to this integral
   realization requires its independent normalization theorem.
3. The finite sums and coefficients are unchanged; the bound pays their
   complete coefficientMass. It is an absolute interchange budget, not a
   large sieve, a level-average saving or a 7/32 result.
4. No manuscript, actual .lean source, cache or original tail cutoff was edited.
   No hLower/hUpper, supported RowSquareMass -> physical-square comparison,
   regular/exceptional/Plancherel or final spectral target is closed here.
-/
