import ImbalancedChen.Part3OriginalExceptionalMellinCeiling

/-! The unmodulated positive majorant and the Mellin ceiling on
the native complementary spectrum, including the exterior cosine. -/
namespace ImbalancedChen.Part3.OriginalExceptionalNativeEnvelope20261113
noncomputable section
open Finset Set Complex
open scoped Classical BigOperators
open CommonSmoothCutoff (dyadicCutoff)
open OriginalSwitchedMellinRows20261113 (wave)
open ActualPrescribedPositiveJ20261112 (exceptionalWeight)
open ActualPositiveNativeDiagonal20261112 (nativeWeight complementaryHeight complementary_range)
open OriginalExceptionalJNativeCompletion20261110
open OriginalExceptionalTestFloor20261113 OriginalExceptionalMellinCeiling20261113

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- All constants precede the native level and multiplicity slot.
The band of native orders covered by this estimate is explicit. -/
theorem native_band {T : ℝ} (t0 : 0≤T) (t1 : T<1) :
    ∃ c K Y₀ : ℝ,0<c ∧ 0<K ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ (z : ℕ+) (i : ↥(exceptional z)),
      tau z i.val≤T →
      c*Y^(tau z i.val)≤(nativeWeight z.val (fun x => (dyadicCutoff (Y*x):ℂ)) i.val).re ∧
      ∀ t : ℝ,‖nativeWeight z.val (fun x => (dyadicCutoff (Y*x):ℂ)*wave x (-t)) i.val‖≤
        K*(1+Real.log (4*Y))*Y^(tau z i.val) := by
  obtain ⟨c,X,cp,x1,f⟩ := tested_floor t0 t1
  obtain ⟨K,Z,kp,z1,g⟩ := tested_ceiling t0 t1
  let D := Real.cos (Real.pi*(T/2))
  have dp : 0<D := Real.cos_pos_of_mem_Ioo ⟨by nlinarith only [Real.pi_pos,mul_nonneg Real.pi_pos.le t0],
    by nlinarith only [mul_lt_mul_of_pos_left t1 Real.pi_pos]⟩
  refine ⟨c,K/D,max X Z,cp,div_pos kp dp,x1.trans (le_max_left _ _),fun Y hy z i st => ?_⟩
  have ex := ((mem_exceptional z i.val).mp i.property).2
  let a := complementaryHeight z.val i.val
  have ra := complementary_range z.val ex
  have a0 : 0<a := ra.1
  have cp' : 0<Real.cos (Real.pi*a) := ra.2.2
  have s2 : tau z i.val/2=a := by unfold tau a complementaryHeight; ring
  have sp : 0<tau z i.val := by linarith only [s2,a0]
  have Yp : 0<Y := zero_lt_one.trans_le (x1.trans ((le_max_left _ _).trans hy))
  have lo := f Y ((le_max_left _ _).trans hy) _ sp st
  rw [s2] at lo
  have co : D≤Real.cos (Real.pi*a) := Real.cos_le_cos_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le a0.le) (by nlinarith only [Real.pi_pos,mul_lt_mul_of_pos_left t1 Real.pi_pos])
    (mul_le_mul_of_nonneg_left (by linarith only [s2,st]) Real.pi_pos.le)
  simp only [nativeWeight,if_pos ex,Complex.div_ofReal_re,norm_div,Complex.norm_real,Real.norm_of_nonneg cp'.le]
  constructor
  · apply (le_div_iff₀ cp').mpr
    exact (mul_le_of_le_one_right (mul_nonneg cp.le (Real.rpow_nonneg Yp.le _)) (Real.cos_le_one _)).trans lo
  · intro t
    have hi := g Y ((le_max_right _ _).trans hy) _ sp st t
    rw [s2] at hi
    have ly : 0≤Real.log (4*Y) := Real.log_nonneg (by linarith [x1.trans ((le_max_left _ _).trans hy)])
    calc
      _ ≤ (K*(1+Real.log (4*Y))*Y^(tau z i.val))/D := div_le_div₀ (by positivity) hi dp co
      _ = _ := by ring

/-- Every exceptional row on each of the finitely many selected
levels is retained. The constants in this statement may depend on S. -/
theorem finite_native_floor (S : Finset ℕ+) :
    ∃ c Y₀ : ℝ,0<c ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ (j : ℕ) (ω : ℝ),
      c*pascadiJ S Y j ω ≤ 4*∑ z ∈ S,∑ i : ↥(exceptional z),
        (nativeWeight z.val (fun x => (dyadicCutoff (Y*x):ℂ)) i.val).re*
          ‖fullM j ω z i.val‖^2 := by
  classical
  let orders := insert (0:ℝ) (S.biUnion (fun z => (exceptional z).image (tau z)))
  have ne : orders.Nonempty := ⟨0,mem_insert_self _ _⟩
  let T := orders.max' ne
  have tm : T∈orders := max'_mem _ _
  have t0 : 0≤T := le_max' _ _ (mem_insert_self _ _)
  have t1 : T<1 := by
    rcases mem_insert.mp tm with h|h
    · rw [h];norm_num
    · obtain ⟨z,_,h⟩ := mem_biUnion.mp h
      obtain ⟨i,hi,e⟩ := mem_image.mp h
      have b := (complementary_range z.val ((mem_exceptional z i).mp hi).2).2.1
      rw [←e]
      change 2*complementaryHeight z.val i<1
      linarith
  obtain ⟨c,K,Y₀,cp,_,y1,H⟩ := native_band t0 t1
  refine ⟨c,Y₀,cp,y1,fun Y hy j ω => ?_⟩
  rw [pascadiJ_eq_four_mul,show c*(4*fullJ S Y j ω)=4*(c*fullJ S Y j ω) by ring]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simp only [fullJ,Finset.mul_sum]
  apply sum_le_sum
  intro z hz
  apply sum_le_sum
  intro i _
  have o : tau z i.val∈orders := mem_insert_of_mem (mem_biUnion.mpr ⟨z,hz,mem_image_of_mem _ i.property⟩)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (H Y hy z i (le_max' _ _ o)).1 (sq_nonneg ‖fullM j ω z i.val‖)

end
end ImbalancedChen.Part3.OriginalExceptionalNativeEnvelope20261113
