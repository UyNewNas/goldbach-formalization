import ImbalancedChen.Part3ComplexDispersion
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# One actual smooth weight for every modulus and frequency of an atom

The fixed cutoff, Schwartz realization and Fourier decay below are a
namespace-isolated extraction of LiLiuPrereqFouvrySmoothCutoff.lean from
goldbach commit 09b97db5764ade1246bfb77206baa1b124760958, source SHA256
bf26cc38e366696cab636f34c61741a525d784026aaacaf98a13c7dcd40abd76.
The original explicit Mathlib aggregate import is replaced by the three
targeted Mathlib imports above. This adds no goldbach dependency.

For one actual MediumAtom, U determines both S_U and w_U once, before
any physical modulus, paired beta label or Fourier frequency. The
original alpha carrier lies where this same smooth weight equals one.
The actual complex Cauchy bound therefore receives a proved common
nonnegative smoothing, with its primitive-centre V and U unchanged.

No Poisson identity, reciprocal phase dictionary, gcd aggregate or
distribution estimate is asserted here. In particular an arbitrary
previous weight is not identified with this chosen smooth function.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Set
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform

namespace CommonSmoothCutoff

def dyadicBump : ContDiffBump (3 / 2 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def dyadicCutoff (x : ℝ) : ℝ := dyadicBump x

theorem dyadicCutoff_contDiff : ContDiff ℝ ∞ dyadicCutoff := dyadicBump.contDiff

theorem dyadicCutoff_nonneg (x : ℝ) : 0 ≤ dyadicCutoff x := dyadicBump.nonneg

theorem dyadicCutoff_le_one (x : ℝ) : dyadicCutoff x ≤ 1 := dyadicBump.le_one

theorem dyadicCutoff_eq_one {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    dyadicCutoff x = 1 := by
  apply dyadicBump.one_of_mem_closedBall
  change |x - 3 / 2| ≤ 1 / 2
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem dyadicCutoff_tsupport_subset : tsupport dyadicCutoff ⊆ Icc (1 / 2 : ℝ) 3 := by
  change tsupport (dyadicBump : ℝ → ℝ) ⊆ _
  rw [dyadicBump.tsupport_eq]
  intro x hx
  change |x - 3 / 2| ≤ 1 at hx
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  constructor <;> linarith

theorem dyadicCutoff_hasCompactSupport : HasCompactSupport dyadicCutoff :=
  dyadicBump.hasCompactSupport

def scaledDyadicCutoff (M x : ℝ) : ℝ := dyadicCutoff (x / M)

theorem scaledDyadicCutoff_contDiff (M : ℝ) : ContDiff ℝ ∞ (scaledDyadicCutoff M) :=
  dyadicCutoff_contDiff.comp (contDiff_id.div_const M)

theorem scaledDyadicCutoff_nonneg (M x : ℝ) : 0 ≤ scaledDyadicCutoff M x :=
  dyadicCutoff_nonneg _

theorem scaledDyadicCutoff_le_one (M x : ℝ) : scaledDyadicCutoff M x ≤ 1 :=
  dyadicCutoff_le_one _

theorem scaledDyadicCutoff_eq_one {M x : ℝ} (hM : 0 < M)
    (hx : x ∈ Icc M (2 * M)) : scaledDyadicCutoff M x = 1 := by
  apply dyadicCutoff_eq_one
  exact ⟨(le_div_iff₀ hM).mpr (by simpa using hx.1), (div_le_iff₀ hM).mpr hx.2⟩

theorem scaledDyadicCutoff_tsupport_subset {M : ℝ} (hM : 0 < M) :
    tsupport (scaledDyadicCutoff M) ⊆ Icc (M / 2) (3 * M) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx' : x / M ∈ tsupport dyadicCutoff :=
    subset_closure (show x / M ∈ Function.support dyadicCutoff from hx)
  obtain ⟨h1, h2⟩ := dyadicCutoff_tsupport_subset hx'
  constructor
  · have := (le_div_iff₀ hM).mp h1
    linarith
  · exact (div_le_iff₀ hM).mp h2

theorem scaledDyadicCutoff_hasCompactSupport {M : ℝ} (hM : 0 < M) :
    HasCompactSupport (scaledDyadicCutoff M) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (scaledDyadicCutoff_tsupport_subset hM)

def dyadicCutoffSchwartz : 𝓢(ℝ, ℂ) :=
  (dyadicCutoff_hasCompactSupport.comp_left (g := Complex.ofRealCLM) (map_zero _)).toSchwartzMap
    (by exact Complex.ofRealCLM.contDiff.comp dyadicCutoff_contDiff)

@[simp] theorem dyadicCutoffSchwartz_apply (x : ℝ) :
    dyadicCutoffSchwartz x = (dyadicCutoff x : ℂ) := rfl

def scaledDyadicCutoffSchwartz (M : ℝ) (hM : 0 < M) : 𝓢(ℝ, ℂ) :=
  ((scaledDyadicCutoff_hasCompactSupport hM).comp_left
    (g := Complex.ofRealCLM) (map_zero _)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (scaledDyadicCutoff_contDiff M))

@[simp] theorem scaledDyadicCutoffSchwartz_apply (M : ℝ) (hM : 0 < M) (x : ℝ) :
    scaledDyadicCutoffSchwartz M hM x = (scaledDyadicCutoff M x : ℂ) := rfl

theorem scaledDyadicCutoff_fourier {M : ℝ} (hM : 0 < M) (frequency : ℝ) :
    𝓕 (fun x ↦ (scaledDyadicCutoff M x : ℂ)) frequency =
      M • (𝓕 dyadicCutoffSchwartz) (M * frequency) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq, Real.fourier_real_eq]
  have hphase (x : ℝ) : x / M * (M * frequency) = x * frequency := by field_simp
  calc
    _ = ∫ x : ℝ, Real.fourierChar (-(x / M * (M * frequency))) •
        dyadicCutoffSchwartz (x / M) := by
      simp only [hphase, dyadicCutoffSchwartz_apply, scaledDyadicCutoff]
    _ = |M| • ∫ x : ℝ, Real.fourierChar (-(x * (M * frequency))) •
        dyadicCutoffSchwartz x :=
      MeasureTheory.Measure.integral_comp_div
        (fun x : ℝ ↦ Real.fourierChar (-(x * (M * frequency))) • dyadicCutoffSchwartz x) M
    _ = _ := by rw [abs_of_pos hM]

theorem schwartz_norm_le_rapidDecay (f : 𝓢(ℝ, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ k := by
  let bound : ℝ := 2 ^ k *
    (Finset.Iic (k, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) f
  have hbound : 0 ≤ bound := by dsimp [bound]; positivity
  refine ⟨bound + 1, by linarith, fun x ↦ ?_⟩
  apply (le_div_iff₀ (by positivity)).mpr
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f x
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  change (1 + |x|) ^ k * ‖f x‖ ≤ bound at h
  nlinarith

theorem scaledDyadicCutoff_fourier_rapidDecay (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ frequency : ℝ,
      ‖𝓕 (fun x ↦ (scaledDyadicCutoff M x : ℂ)) frequency‖ ≤
        C * M / (1 + |M * frequency|) ^ k := by
  obtain ⟨C, hC, hbound⟩ := schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) k
  refine ⟨C, hC, fun M hM frequency ↦ ?_⟩
  rw [scaledDyadicCutoff_fourier hM, norm_smul, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * (C / (1 + |M * frequency|) ^ k) :=
      mul_le_mul_of_nonneg_left (hbound (M * frequency)) hM.le
    _ = _ := by ring

end CommonSmoothCutoff

def MediumAtom.commonSmoothCarrier (d : MediumAtom) : Finset ℕ :=
  Finset.Icc 0 (Nat.ceil (3 * d.U))

def MediumAtom.commonSmoothWeight (d : MediumAtom) (n : ℕ) : ℝ :=
  CommonSmoothCutoff.scaledDyadicCutoff d.U (n : ℝ)

theorem MediumAtom.commonSmoothWeight_nonneg (d : MediumAtom) (n : ℕ) :
    0 ≤ d.commonSmoothWeight n := CommonSmoothCutoff.scaledDyadicCutoff_nonneg _ _

/-- Every actual alpha integer lies in the plateau of the one fixed bump. -/
theorem MediumAtom.commonSmoothWeight_eq_one_on_alpha
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {n : ℕ} (hn : n ∈ d.alphaCarrier) :
    d.commonSmoothWeight n = 1 := by
  have hU : 1 ≤ d.U := hd.1
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hlo : d.U ≤ (n : ℝ) := (Nat.le_ceil d.U).trans (by exact_mod_cast hnlo)
  have hhi : (n : ℝ) ≤ 2 * d.U :=
    (show (n : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by exact_mod_cast hnhi).trans
      (Nat.floor_le (by linarith : 0 ≤ 2 * d.U))
  exact CommonSmoothCutoff.scaledDyadicCutoff_eq_one (by linarith) ⟨hlo, hhi⟩

theorem MediumAtom.commonSmoothWeight_support_subset
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {n : ℕ}
    (hn : d.commonSmoothWeight n ≠ 0) : n ∈ d.commonSmoothCarrier := by
  have hU : 0 < d.U := lt_of_lt_of_le zero_lt_one hd.1
  have hs : (n : ℝ) ∈ tsupport (CommonSmoothCutoff.scaledDyadicCutoff d.U) :=
    subset_closure hn
  have hupper := (CommonSmoothCutoff.scaledDyadicCutoff_tsupport_subset hU hs).2
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.zero_le _, ?_⟩
  exact_mod_cast hupper.trans (Nat.le_ceil (3 * d.U))

theorem MediumAtom.alphaCarrier_subset_commonSmoothCarrier
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.alphaCarrier ⊆ d.commonSmoothCarrier := by
  intro n hn
  apply MediumAtom.commonSmoothWeight_support_subset hd
  rw [MediumAtom.commonSmoothWeight_eq_one_on_alpha hd hn]
  norm_num

/-- The actual complex source receives one proved smooth weight and one
finite carrier, independent of every later modulus and spectral height. -/
theorem MediumAtom.signedError_norm_sq_le_commonSmoothDispersion
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ‖d.signedError‖ ^ 2 ≤
      (∑ n ∈ d.alphaCarrier, ‖d.alpha n‖ ^ 2) *
        (d.complexDispersionW d.commonSmoothCarrier d.commonSmoothWeight -
          2 * d.complexDispersionV d.commonSmoothCarrier d.commonSmoothWeight +
            d.complexDispersionU d.commonSmoothCarrier d.commonSmoothWeight) := by
  apply d.signedError_norm_sq_le_smoothedComplexDispersion
    d.commonSmoothCarrier d.commonSmoothWeight
  · exact MediumAtom.alphaCarrier_subset_commonSmoothCarrier hd
  · intro n _
    exact d.commonSmoothWeight_nonneg n
  · intro n hn
    exact (MediumAtom.commonSmoothWeight_eq_one_on_alpha hd hn).ge

end

end ImbalancedChen.Part3
