import ImbalancedChen.Part3CommonSmoothCutoff
import ImbalancedChen.Part3ComplexCRTConsumer
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Actual common smoothing: natural progressions and complete Poisson series

The natural-to-integer support bijection is extracted from fixed goldbach
09b97db5764ade1246bfb77206baa1b124760958, ArithmeticPoisson.lean:35,
SHA256 77b57886ffe1f40e80f3e53de860323fff67d0705cabf342afeacd1ddc1dd72c.
The affine Schwartz rescaling follows its Poisson.lean:17,
SHA256 a365f5a2cc1f33fb38dbeeb57206b8c8958b49b0f60ce0713172e94360d0e974.
Both source blobs were compared with that exact commit. Names are isolated
and the only new direct Mathlib import is PoissonSummation.

The atom chooses U, its common finite carrier and its common smooth weight
before any modulus or frequency. All original complex gamma/beta labels
remain in the W sum. Its zero mode is displayed separately from the exact
nonzero integer-frequency remainder; V and U keep their primitive centers.
No zero-mode cancellation, reciprocal dictionary or analytic estimate is
assumed or concluded.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators SchwartzMap FourierTransform
open Classical

namespace CommonSmoothCutoff

/-- Every nonzero point of the fixed cutoff lies on its positive support. -/
theorem scaledDyadicCutoff_mem_Icc_of_ne_zero {M x : ℝ} (hM : 0 < M)
    (hx : scaledDyadicCutoff M x ≠ 0) : x ∈ Set.Icc (M / 2) (3 * M) :=
  scaledDyadicCutoff_tsupport_subset hM (subset_closure hx)

/-- A genuine support bijection, including negative residue representatives. -/
theorem scaledDyadicCutoff_finset_progression_eq_tsum
    {M : ℝ} (hM : 0 < M) (S : Finset ℕ)
    (hS : ∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S)
    {q : ℕ} (hq : 0 < q) (a : ℤ) :
    (∑ m ∈ S, if Int.ModEq q (m : ℤ) a
      then (scaledDyadicCutoff M m : ℂ) else 0) =
        ∑' z : ℤ, (scaledDyadicCutoff M ((a : ℝ) + q * z) : ℂ) := by
  let f : ℕ → ℂ := fun m ↦
    if Int.ModEq q (m : ℤ) a then (scaledDyadicCutoff M m : ℂ) else 0
  let g : ℤ → ℂ := fun z ↦ (scaledDyadicCutoff M ((a : ℝ) + q * z) : ℂ)
  have hnonneg (z : Function.support g) : 0 ≤ a + (q : ℤ) * z.val := by
    have hz : scaledDyadicCutoff M ((a : ℝ) + q * z.val) ≠ 0 := by
      simpa only [g, Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using z.property
    have hp := (scaledDyadicCutoff_mem_Icc_of_ne_zero hM hz).1
    have hp' : (0 : ℝ) ≤ a + (q : ℝ) * z.val := by linarith
    exact_mod_cast hp'
  let i : Function.support g → ℕ := fun z ↦ (a + (q : ℤ) * z.val).toNat
  have hcast (z : Function.support g) : (i z : ℤ) = a + (q : ℤ) * z.val :=
    Int.toNat_of_nonneg (hnonneg z)
  have hi : Function.Injective i := by
    intro z z' h
    have he := congrArg (fun n : ℕ ↦ (n : ℤ)) h
    rw [hcast, hcast] at he
    apply Subtype.ext
    exact mul_left_cancel₀ (by exact_mod_cast hq.ne') (add_left_cancel he)
  have hf : Function.support f ⊆ Set.range i := by
    intro m hm
    have hm' : Int.ModEq q (m : ℤ) a ∧ scaledDyadicCutoff M m ≠ 0 := by
      simpa only [f, Function.mem_support, ne_eq, ite_eq_right_iff,
        Complex.ofReal_eq_zero, Classical.not_imp] using hm
    obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp hm'.1.symm
    have he : a + (q : ℤ) * z = m := by linarith
    have heR : (a : ℝ) + (q : ℝ) * z = m := by exact_mod_cast he
    have hg : z ∈ Function.support g := by
      simpa only [Function.mem_support, g, heR, ne_eq, Complex.ofReal_eq_zero] using hm'.2
    refine ⟨⟨z, hg⟩, ?_⟩
    simp only [i, he, Int.toNat_natCast]
  have hfg (z : Function.support g) : f (i z) = g z := by
    have hc : Int.ModEq q (i z : ℤ) a := by
      rw [hcast]
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-z.val, by ring⟩
    have hr : (i z : ℝ) = (a : ℝ) + (q : ℝ) * z.val := by
      exact_mod_cast hcast z
    simp only [f, hc, if_pos, hr, g]
  calc
    _ = ∑' m : ℕ, f m := by
      symm
      apply tsum_eq_sum
      intro m hm
      have hw : scaledDyadicCutoff M m = 0 := by
        by_contra hw
        exact hm (hS m hw)
      simp [f, hw]
    _ = _ := tsum_eq_tsum_of_ne_zero_bij i hi hf hfg

/-- Schwartz Poisson on the actual affine lattice, retaining every frequency. -/
theorem scaledDyadicCutoff_poisson_rescaled {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (b : ℝ) :
    (∑' z : ℤ, (scaledDyadicCutoff M (b + D * z) : ℂ)) =
      ∑' h : ℤ, (M / D) • (𝓕 dyadicCutoffSchwartz) ((M / D) * h) *
        fourier h (b / D : UnitAddCircle) := by
  have hMD : 0 < M / D := div_pos hM hD
  have hscale (z : ℤ) :
      (b / D + (z : ℝ)) / (M / D) = (b + D * z) / M := by field_simp
  convert (scaledDyadicCutoffSchwartz (M / D) hMD).tsum_eq_tsum_fourier (b / D)
      using 1
  · apply tsum_congr
    intro z
    simp only [scaledDyadicCutoffSchwartz_apply, scaledDyadicCutoff, hscale]
  · apply tsum_congr
    intro h
    rw [SchwartzMap.fourier_coe]
    exact congrArg (fun v : ℂ ↦ v * fourier h (b / D : UnitAddCircle))
      (scaledDyadicCutoff_fourier hMD h).symm

/-- The complete Poisson series is absolutely summable for every positive mesh. -/
theorem poissonFrequency_summable_norm {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun h : ℤ ↦
      ‖t • (𝓕 dyadicCutoffSchwartz) (t * h) * fourier h (x : UnitAddCircle)‖) := by
  let f := scaledDyadicCutoffSchwartz t ht
  have hnorm : Summable (fun h : ℤ ↦ ‖(𝓕 f) (h : ℝ)‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 f).isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto
        Int.tendsto_coe_cofinite)
  have hcoef (h : ℤ) :
      (𝓕 f) (h : ℝ) = t • (𝓕 dyadicCutoffSchwartz) (t * h) := by
    rw [SchwartzMap.fourier_coe]
    exact scaledDyadicCutoff_fourier ht h
  apply hnorm.congr
  intro h
  rw [hcoef]
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

def poissonNonzeroFrequency (t x : ℝ) (h : ℤ) : ℂ :=
  if h = 0 then 0 else
    t • (𝓕 dyadicCutoffSchwartz) (t * h) * fourier h (x : UnitAddCircle)

@[simp] theorem poissonNonzeroFrequency_zero (t x : ℝ) :
    poissonNonzeroFrequency t x 0 = 0 := rfl

theorem poissonNonzeroFrequency_summable_norm {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun h : ℤ ↦ ‖poissonNonzeroFrequency t x h‖) := by
  apply (poissonFrequency_summable_norm ht x).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro h
  by_cases hh : h = 0
  · simp only [poissonNonzeroFrequency, if_pos hh, norm_zero]
    exact norm_nonneg _
  · simp only [poissonNonzeroFrequency, if_neg hh, le_refl]

/-- The zero frequency is removed by a proved summability fact. -/
theorem scaledDyadicCutoff_poisson_mainTerm {M D : ℝ} (hM : 0 < M) (hD : 0 < D)
    (b : ℝ) :
    (∑' z : ℤ, (scaledDyadicCutoff M (b + D * z) : ℂ)) -
        (M / D) • (𝓕 dyadicCutoffSchwartz) 0 =
      ∑' h : ℤ, poissonNonzeroFrequency (M / D) (b / D) h := by
  have hr := (poissonNonzeroFrequency_summable_norm (div_pos hM hD) (b / D)).of_norm
  let f : ℤ → ℂ := fun h ↦
    (M / D) • (𝓕 dyadicCutoffSchwartz) ((M / D) * h) *
      fourier h (b / D : UnitAddCircle)
  have hs : Summable (Function.update f 0 0) := by
    apply hr.congr
    intro h
    by_cases hh : h = 0 <;> simp [f, poissonNonzeroFrequency, hh]
  have heq := Summable.tsum_eq_add_tsum_ite' (f := f) 0 hs
  rw [scaledDyadicCutoff_poisson_rescaled hM hD]
  change (∑' h : ℤ, f h) - _ = _
  rw [heq]
  simp only [f, Int.cast_zero, mul_zero, fourier_zero, mul_one,
    add_sub_cancel_left, poissonNonzeroFrequency]

def cutoffMass : ℝ := ((𝓕 dyadicCutoffSchwartz) 0).re

theorem scaledDyadicCutoff_finset_progression_eq_main_add_fourier
    {M : ℝ} (hM : 0 < M) (S : Finset ℕ)
    (hS : ∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S)
    {q : ℕ} (hq : 0 < q) (b : ℤ) :
    (∑ m ∈ S, if Int.ModEq q (m : ℤ) b then scaledDyadicCutoff M m else 0) =
      (M / q) * cutoffMass +
        (∑' h : ℤ, poissonNonzeroFrequency (M / q) ((b : ℝ) / q) h).re := by
  have he := congrArg Complex.re
    (scaledDyadicCutoff_poisson_mainTerm (D := (q : ℝ)) hM
      (by exact_mod_cast hq) (b : ℝ))
  rw [← scaledDyadicCutoff_finset_progression_eq_tsum hM S hS hq b] at he
  simp only [Complex.sub_re, Complex.re_sum, apply_ite, Complex.ofReal_re,
    Complex.zero_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

end CommonSmoothCutoff

private theorem commonPoisson_pair_lcm_pos
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.complexRowLabels) (hl' : l' ∈ d.complexRowLabels) :
    0 < (complexFactorModulus l.1).lcm (complexFactorModulus l'.1) := by
  obtain ⟨_, _, hQ1, hQ2, hQ3, _⟩ := hd
  have factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {q : ℕ}
      (hq : q ∈ factorCarrier Q) : 0 < q := by
    have hlo := (Finset.mem_Icc.mp hq).1
    have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
    omega
  have hmod {k : (ℕ × ℕ × ℕ) × ℕ} (hk : k ∈ d.complexRowLabels) :
      0 < complexFactorModulus k.1 := by
    have hf := (Finset.mem_product.mp hk).1
    obtain ⟨hf1, hf23⟩ := Finset.mem_product.mp hf
    obtain ⟨hf2, hf3⟩ := Finset.mem_product.mp hf23
    exact Nat.mul_pos (Nat.mul_pos (factor_pos hQ1 hf1) (factor_pos hQ2 hf2))
      (factor_pos hQ3 hf3)
  exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hmod hl).ne' (hmod hl').ne')

def MediumAtom.complexCRTSmoothZeroPart (d : MediumAtom) : ℂ :=
  ∑ l ∈ d.complexRowLabels, ∑ l' ∈ d.complexRowLabels,
    d.complexBetaCoefficient l * star (d.complexBetaCoefficient l') *
      (if ComplexCRT.Compatible (complexFactorModulus l.1)
        (complexFactorModulus l'.1) l.2 l'.2 then
          ((d.U / (complexFactorModulus l.1).lcm (complexFactorModulus l'.1)) *
            CommonSmoothCutoff.cutoffMass : ℝ) else 0)

/-- The exact signed nonzero-frequency remainder of the one common smoothing. -/
def MediumAtom.complexCRTSmoothNonzeroPart (d : MediumAtom) : ℂ :=
  ∑ l ∈ d.complexRowLabels, ∑ l' ∈ d.complexRowLabels,
    d.complexBetaCoefficient l * star (d.complexBetaCoefficient l') *
      (if ComplexCRT.Compatible (complexFactorModulus l.1)
        (complexFactorModulus l'.1) l.2 l'.2 then
          (∑' h : ℤ, CommonSmoothCutoff.poissonNonzeroFrequency
            (d.U / (complexFactorModulus l.1).lcm (complexFactorModulus l'.1))
            ((ComplexCRT.residue (complexFactorModulus l.1)
              (complexFactorModulus l'.1) l.2 l'.2 d.residue : ℝ) /
                (complexFactorModulus l.1).lcm (complexFactorModulus l'.1)) h).re
      else 0 : ℝ)

/-- Every actual complete lcm receives the same scale and support; the
constructed CRT output and the complete Poisson series are proved here. -/
theorem MediumAtom.complexDispersionW_commonSmooth_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.complexDispersionW d.commonSmoothCarrier d.commonSmoothWeight : ℂ) =
      d.complexCRTSmoothZeroPart + d.complexCRTSmoothNonzeroPart := by
  rw [MediumAtom.complexDispersionW_eq_constructedCRT hd]
  unfold MediumAtom.complexCRTSmoothZeroPart MediumAtom.complexCRTSmoothNonzeroPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l' hl'
  unfold ComplexCRT.constructedProgressionWeight
  by_cases hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2
  · simp only [hc, if_true]
    have he := CommonSmoothCutoff.scaledDyadicCutoff_finset_progression_eq_main_add_fourier
      (lt_of_lt_of_le zero_lt_one hd.1) d.commonSmoothCarrier
      (fun m hm ↦ MediumAtom.commonSmoothWeight_support_subset hd hm)
      (commonPoisson_pair_lcm_pos hd hl hl')
      (ComplexCRT.residue (complexFactorModulus l.1)
        (complexFactorModulus l'.1) l.2 l'.2 d.residue)
    simp only [MediumAtom.commonSmoothWeight] at *
    rw [he, Complex.ofReal_add]
    ring
  · simp only [hc, if_false, Complex.ofReal_zero, mul_zero, add_zero]

/-- No cancellation with the primitive center has been imposed on the
raw zero mode. The entire nonzero series remains an exact separate term. -/
theorem MediumAtom.complex_dispersion_identity_with_commonPoisson
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ((∑ n ∈ d.commonSmoothCarrier,
      d.commonSmoothWeight n * ‖d.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      (d.complexCRTSmoothZeroPart -
        2 * (d.complexDispersionV d.commonSmoothCarrier d.commonSmoothWeight : ℂ) +
          (d.complexDispersionU d.commonSmoothCarrier d.commonSmoothWeight : ℂ)) +
        d.complexCRTSmoothNonzeroPart := by
  rw [MediumAtom.complex_dispersion_identity]
  push_cast
  rw [MediumAtom.complexDispersionW_commonSmooth_eq_zero_add_nonzero hd]
  ring

end

end ImbalancedChen.Part3
