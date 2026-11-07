import Mathlib
import ImbalancedChen.Part3TwoLongQuantitativeTransitionProfiles
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual compact-Schwartz profile rescaling and double affine Poisson
periodization used inside P1. Neither hP1 nor hP2 is assumed. This does
not yet identify the original complete AP count-minus-coprime mean with
the finite unit-residue combination of these periodizations.
-/
namespace ImbalancedChen.Part3.TwoLongActualDoublePeriodization
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators Topology SchwartzMap FourierTransform
open ImbalancedChen.Part3.TwoLongQuantitativeTransitionProfiles

/-- Exact scalar dilation as a homeomorphism; support transport is real. -/
def divideHomeomorph (M : ℝ) (hM : 0 < M) : ℝ ≃ₜ ℝ where
  toEquiv :=
    { toFun := fun x => x/M
      invFun := fun x => M*x
      left_inv := by intro x; field_simp [hM.ne']
      right_inv := by intro x; field_simp [hM.ne'] }
  continuous_toFun := continuous_id.div_const M
  continuous_invFun := continuous_const.mul continuous_id

def scaleProfile (F : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (F : ℝ → ℂ))
    (M : ℝ) (hM : 0 < M) : 𝓢(ℝ, ℂ) :=
  (hc.comp_homeomorph (divideHomeomorph M hM)).toSchwartzMap
    (F.smooth'.comp (contDiff_id.div_const M))

@[simp] theorem scaleProfile_apply (F : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (F : ℝ → ℂ)) (M : ℝ) (hM : 0 < M) (x : ℝ) :
    scaleProfile F hc M hM x = F (x/M) := rfl

/-- The exact Fourier normalization of the original normalized f(n/U). -/
theorem scaleProfile_fourier (F : 𝓢(ℝ, ℂ)) {M : ℝ} (hM : 0 < M) (t : ℝ) :
    𝓕 (fun x : ℝ => F (x/M)) t = M • (𝓕 F) (M*t) := by
  rw [SchwartzMap.fourier_coe,Real.fourier_real_eq,Real.fourier_real_eq]
  have hp (x : ℝ) : (x/M)*(M*t)=x*t := by field_simp [hM.ne']
  calc
    _ = ∫ x : ℝ, Real.fourierChar (-(x/M*(M*t))) • F (x/M) := by simp only [hp]
    _ = |M| • ∫ x : ℝ, Real.fourierChar (-(x*(M*t))) • F x :=
      MeasureTheory.Measure.integral_comp_div
        (fun x : ℝ => Real.fourierChar (-(x*(M*t))) • F x) M
    _ = _ := by rw [abs_of_pos hM]

def progressionPeriodization (F : 𝓢(ℝ, ℂ)) (M D b : ℝ) : ℂ :=
  ∑' z : ℤ, F ((b+D*(z : ℝ))/M)

def poissonMode (F : 𝓢(ℝ, ℂ)) (M D b : ℝ) (h : ℤ) : ℂ :=
  (M/D) • (𝓕 F) ((M/D)*(h : ℝ)) * fourier h (b/D : UnitAddCircle)

/-- Actual Mathlib Poisson on the affine lattice, now for the original
C-infinity compact long profiles, not only one old fixed cutoff. -/
theorem affine_periodization_poisson (F : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (F : ℝ → ℂ)) {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D) (b : ℝ) :
    progressionPeriodization F M D b = ∑' h : ℤ, poissonMode F M D b h := by
  have hMD : 0 < M/D := div_pos hM hD
  have hs (z : ℤ) : (b/D+(z : ℝ))/(M/D)=(b+D*(z : ℝ))/M := by
    field_simp [hM.ne',hD.ne']
  convert (scaleProfile F hc (M/D) hMD).tsum_eq_tsum_fourier (b/D) using 1
  · apply tsum_congr
    intro z
    simp only [scaleProfile_apply,hs,progressionPeriodization]
  · apply tsum_congr
    intro h
    rw [SchwartzMap.fourier_coe]
    have hcoef := scaleProfile_fourier F hMD (h : ℝ)
    simpa only [poissonMode,scaleProfile_apply] using
      congrArg (fun z : ℂ => z * fourier h (b/D : UnitAddCircle)) hcoef.symm

/-- The exact Poisson sequence is absolutely summable, including all
zero/nonzero modes and every positive ratio M/D. -/
theorem poissonMode_norm_summable (F : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (F : ℝ → ℂ)) {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D) (b : ℝ) :
    Summable (fun h : ℤ => ‖poissonMode F M D b h‖) := by
  let S := scaleProfile F hc (M/D) (div_pos hM hD)
  have hN : Summable (fun h : ℤ => ‖(𝓕 S) (h : ℝ)‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 S).isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite)
  apply hN.congr
  intro h
  have hcF : (𝓕 S) (h : ℝ) = (M/D) • (𝓕 F) ((M/D)*(h : ℝ)) := by
    rw [SchwartzMap.fourier_coe]
    exact scaleProfile_fourier F (div_pos hM hD) _
  rw [hcF]
  simp only [poissonMode,norm_mul,fourier_apply,Circle.norm_coe,mul_one]

/-- The actual two-coordinate affine periodization has the original
UV/D^2 factor, with both real Fourier arguments and both phases retained. -/
theorem double_periodization_poisson (F G : 𝓢(ℝ, ℂ))
    (hF : HasCompactSupport (F : ℝ → ℂ)) (hG : HasCompactSupport (G : ℝ → ℂ))
    {U V D : ℝ} (hU : 0 < U) (hV : 0 < V) (hD : 0 < D) (a b : ℝ) :
    progressionPeriodization F U D a * progressionPeriodization G V D b =
      ∑' j : ℤ, ∑' k : ℤ,
        (((U*V/D^2 : ℝ) : ℂ) * (𝓕 F) ((U/D)*(j : ℝ)) *
          (𝓕 G) ((V/D)*(k : ℝ)) * fourier j (a/D : UnitAddCircle) *
            fourier k (b/D : UnitAddCircle)) := by
  rw [affine_periodization_poisson F hF hU hD,
    affine_periodization_poisson G hG hV hD]
  calc
    _ = ∑' j : ℤ, poissonMode F U D a j * ∑' k : ℤ, poissonMode G V D b k :=
      tsum_mul_right.symm
    _ = ∑' j : ℤ, ∑' k : ℤ, poissonMode F U D a j * poissonMode G V D b k := by
      apply tsum_congr
      intro j
      exact tsum_mul_left.symm
    _ = _ := by
      apply tsum_congr
      intro j
      apply tsum_congr
      intro k
      simp only [poissonMode,smul_eq_mul]
      push_cast
      field_simp [hD.ne']
      ring

/-- The actual fourth-batch upper profile, with no Schwartz regularity
hypothesis left to the caller. -/
def actualUpperSchwartz {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) : 𝓢(ℝ, ℂ) :=
  let f : ℝ → ℂ := fun x => (upper delta x : ℂ)
  let hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp (upper_smooth delta)
  let hc : HasCompactSupport f := by
    change IsCompact (closure (Function.support f))
    have hsup : Function.support f ⊆ Icc (1/2 : ℝ) (5/2) := by
      intro x hx
      exact upper_support hd hs (by simpa [f] using hx)
    exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hsup isClosed_Icc)
  hc.toSchwartzMap hf

def actualGapSchwartz {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) : 𝓢(ℝ, ℂ) :=
  let f : ℝ → ℂ := fun x => (gap delta x : ℂ)
  let hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp (gap_smooth delta)
  let hc : HasCompactSupport f := by
    change IsCompact (closure (Function.support f))
    have hsup : Function.support f ⊆ Icc (1/2 : ℝ) (5/2) := by
      intro x hx
      exact gap_support hd hs (by simpa [f] using hx)
    exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hsup isClosed_Icc)
  hc.toSchwartzMap hf

@[simp] theorem actualUpperSchwartz_apply {delta : ℝ} (hd : 0 < delta)
    (hs : delta ≤ 1/4) (x : ℝ) : actualUpperSchwartz hd hs x = (upper delta x : ℂ) := rfl

@[simp] theorem actualGapSchwartz_apply {delta : ℝ} (hd : 0 < delta)
    (hs : delta ≤ 1/4) (x : ℝ) : actualGapSchwartz hd hs x = (gap delta x : ℂ) := rfl

theorem actualUpperSchwartz_compact {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) :
    HasCompactSupport (actualUpperSchwartz hd hs : ℝ → ℂ) := by
  change IsCompact (closure (Function.support (fun x => (upper delta x : ℂ))))
  have hsup : Function.support (fun x => (upper delta x : ℂ)) ⊆ Icc (1/2 : ℝ) (5/2) := by
    intro x hx
    exact upper_support hd hs (by simpa using hx)
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hsup isClosed_Icc)

theorem actualGapSchwartz_compact {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) :
    HasCompactSupport (actualGapSchwartz hd hs : ℝ → ℂ) := by
  change IsCompact (closure (Function.support (fun x => (gap delta x : ℂ))))
  have hsup : Function.support (fun x => (gap delta x : ℂ)) ⊆ Icc (1/2 : ℝ) (5/2) := by
    intro x hx
    exact gap_support hd hs (by simpa using hx)
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hsup isClosed_Icc)

/-- Actual upper-upper, left-gap-upper, upper-right-gap choices. -/
def leftSchwartz {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) (label : Fin 3) : 𝓢(ℝ, ℂ) :=
  if label=1 then actualGapSchwartz hd hs else actualUpperSchwartz hd hs

def rightSchwartz {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4) (label : Fin 3) : 𝓢(ℝ, ℂ) :=
  if label=2 then actualGapSchwartz hd hs else actualUpperSchwartz hd hs

/-- The actual three smooth profile pairs have proved Poisson expansion;
regularity and compactness are constructed, not P1-shaped premises. -/
theorem actual_three_double_periodization {delta U V D : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V) (hD : 0 < D)
    (label : Fin 3) (a b : ℝ) :
    progressionPeriodization (leftSchwartz hd hs label) U D a *
      progressionPeriodization (rightSchwartz hd hs label) V D b =
      ∑' j : ℤ, ∑' k : ℤ,
        (((U*V/D^2 : ℝ) : ℂ) * (𝓕 (leftSchwartz hd hs label)) ((U/D)*(j : ℝ)) *
          (𝓕 (rightSchwartz hd hs label)) ((V/D)*(k : ℝ)) *
            fourier j (a/D : UnitAddCircle) * fourier k (b/D : UnitAddCircle)) := by
  apply double_periodization_poisson
  · by_cases h : label=1
    · simpa [leftSchwartz,h] using actualGapSchwartz_compact hd hs
    · simpa [leftSchwartz,h] using actualUpperSchwartz_compact hd hs
  · by_cases h : label=2
    · simpa [rightSchwartz,h] using actualGapSchwartz_compact hd hs
    · simpa [rightSchwartz,h] using actualUpperSchwartz_compact hd hs
  · exact hU
  · exact hV
  · exact hD


end
end ImbalancedChen.Part3.TwoLongActualDoublePeriodization
