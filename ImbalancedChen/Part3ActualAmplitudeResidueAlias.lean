import ImbalancedChen.Part3ActualCompletedPairSharpL2

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Actual ALL-integer amplitude residue alias from the native PLUS-sign affine
Poisson formula. Finite additive orthogonality gives the NEGATIVE inverse
character and exact 1/q. Absolute summability is proved before interchange.
No finite completed-frequency window or arbitrary modulation is bounded.
-/
namespace ImbalancedChen.Part3.ActualCompletedLeftAlias20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.FiniteSource20261026b
open OriginalSmoothPoissonTail.FiniteOperator20261026b
open scoped BigOperators SchwartzMap FourierTransform

/-- The actual unmodulated all-m residue fibre, before inverse-z pullback. -/
def aliasCoefficient (q : ℕ) [NeZero q] (M : ℝ) (r : ZMod q) : ℂ :=
  ∑' m : ℤ,if (m : ZMod q)=r then frequencyAmplitude M q m else 0

/-- Actual physical common-cutoff mass in a residue class. -/
def physicalResidueMass (q : ℕ) [NeZero q] (M : ℝ) (b : ZMod q) : ℝ :=
  ∑ n ∈ Physical.naturalSupport M,
    if (n : ZMod q)=b then scaledDyadicCutoff M n else 0

theorem norm_stdAddChar (q : ℕ) [NeZero q] (u : ZMod q) : ‖ZMod.stdAddChar u‖=1 := by
  simpa only [ZMod.stdAddChar_apply] using Circle.norm_coe (ZMod.toCircle u)

/-- The true scalar Fourier amplitude is absolutely summable. -/
theorem amplitude_summable_norm (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) :
    Summable (fun m : ℤ => ‖frequencyAmplitude M q m‖) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h := poissonFrequency_summable_norm (div_pos hM hq) (0 : ℝ)
  simpa only [frequencyAmplitude,norm_mul,fourier_apply,Circle.norm_coe,mul_one] using h

theorem alias_summable_norm (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) (r : ZMod q) :
    Summable (fun m : ℤ => ‖if (m : ZMod q)=r then frequencyAmplitude M q m else 0‖) := by
  apply (amplitude_summable_norm q hM).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  split_ifs <;> simp only [le_refl,norm_zero,norm_nonneg]

private theorem fourier_eq_residue_char (q : ℕ) [NeZero q] (m : ℤ) (b : ZMod q) :
    fourier m (((b.val : ℝ)/(q : ℝ)) : UnitAddCircle) =
      ZMod.stdAddChar ((m : ZMod q)*b) := by
  have hb : ((m*(b.val : ℤ) : ℤ) : ZMod q)=(m : ZMod q)*b := by
    simp only [Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val]
  rw [← hb,ZMod.stdAddChar_coe,fourier_coe_apply]
  push_cast
  congr 1
  ring

private theorem natural_class_iff (q : ℕ) [NeZero q] (n : ℕ) (b : ZMod q) :
    Int.ModEq q (n : ℤ) (b.val : ℤ) ↔ (n : ZMod q)=b := by
  simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using
    (ZMod.intCast_eq_intCast_iff (n : ℤ) (b.val : ℤ) q).symm

/-- Native PLUS-sign Poisson formula for EACH physical residue, before
inverse finite Fourier transformation. The arithmetic cutoff is actual. -/
theorem physicalResidueMass_poisson (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) (b : ZMod q) :
    (physicalResidueMass q M b : ℂ) =
      ∑' m : ℤ,frequencyAmplitude M q m*ZMod.stdAddChar ((m : ZMod q)*b) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  calc
    _ = ∑ n ∈ Physical.naturalSupport M,
        if Int.ModEq q (n : ℤ) (b.val : ℤ) then (scaledDyadicCutoff M n : ℂ) else 0 := by
      simp only [physicalResidueMass,Complex.ofReal_sum,apply_ite,Complex.ofReal_zero,
        natural_class_iff]
    _ = ∑' k : ℤ,(scaledDyadicCutoff M ((b.val : ℝ)+(q : ℝ)*k) : ℂ) :=
      by simpa only [Int.cast_natCast] using
        scaledDyadicCutoff_finset_progression_eq_tsum hM (Physical.naturalSupport M)
          (Physical.mem_naturalSupport hM) (NeZero.pos q) (b.val : ℤ)
    _ = _ := by
      rw [scaledDyadicCutoff_poisson_rescaled hM hq]
      apply tsum_congr
      intro m
      rw [fourier_eq_residue_char q m b]
      rfl

/-- Multiplying the actual alias by q gives the negative DFT of physical
residue masses. Both finite/tsum exchange and orthogonality are proved. -/
theorem negative_dft_physicalResidueMass (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) (r : ZMod q) :
    (∑ b : ZMod q,(physicalResidueMass q M b : ℂ)*ZMod.stdAddChar (-r*b)) =
      (q : ℂ)*aliasCoefficient q M r := by
  have hs (b : ZMod q) : Summable (fun m : ℤ =>
      frequencyAmplitude M q m*ZMod.stdAddChar ((m : ZMod q)*b)*ZMod.stdAddChar (-r*b)) := by
    apply Summable.of_norm
    apply (amplitude_summable_norm q hM).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro m
    simp only [norm_mul,norm_stdAddChar,mul_one,le_refl]
  calc
    _ = ∑ b : ZMod q,∑' m : ℤ,
        frequencyAmplitude M q m*ZMod.stdAddChar ((m : ZMod q)*b)*ZMod.stdAddChar (-r*b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [physicalResidueMass_poisson q hM b,tsum_mul_right]
    _ = ∑' m : ℤ,∑ b : ZMod q,
        frequencyAmplitude M q m*ZMod.stdAddChar ((m : ZMod q)*b)*ZMod.stdAddChar (-r*b) :=
      (Summable.tsum_finsetSum (fun b _ => hs b)).symm
    _ = ∑' m : ℤ,frequencyAmplitude M q m*
        (∑ b : ZMod q,ZMod.stdAddChar (b*((m : ZMod q)-r))) := by
      apply tsum_congr
      intro m
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_assoc,← ZMod.stdAddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑' m : ℤ,frequencyAmplitude M q m*
        (if (m : ZMod q)=r then (q : ℂ) else 0) := by
      apply tsum_congr
      intro m
      rw [ImbalancedChen.Part3.sum_stdAddChar_mul_eq]
      simp only [sub_eq_zero]
    _ = ∑' m : ℤ,(q : ℂ)*(if (m : ZMod q)=r then frequencyAmplitude M q m else 0) := by
      apply tsum_congr
      intro m
      split_ifs <;> ring
    _ = _ := by rw [tsum_mul_left];rfl

/-- Exact inverse-DFT form, including modulus q=1. -/
theorem aliasCoefficient_eq_negative_dft (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) (r : ZMod q) :
    aliasCoefficient q M r = (1/(q : ℂ))*
      ∑ b : ZMod q,(physicalResidueMass q M b : ℂ)*ZMod.stdAddChar (-r*b) := by
  rw [negative_dft_physicalResidueMass q hM r]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp [hq]
  <;> ring

/-- The exact all-m alias identity in physical cutoff variables. The
negative sign and 1/q are forced by native PLUS-sign Poisson summation. -/
theorem aliasCoefficient_fourier (q : ℕ) [NeZero q] {M : ℝ} (hM : 0 < M) (r : ZMod q) :
    aliasCoefficient q M r = (1/(q : ℂ))*
      ∑ n ∈ Physical.naturalSupport M,(scaledDyadicCutoff M n : ℂ)*
        ZMod.stdAddChar (-r*(n : ZMod q)) := by
  rw [aliasCoefficient_eq_negative_dft q hM r]
  congr 1
  simp only [physicalResidueMass,Complex.ofReal_sum,apply_ite,Complex.ofReal_zero,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp only [ite_mul,zero_mul]
  simp

end
end ImbalancedChen.Part3.ActualCompletedLeftAlias20261026b
