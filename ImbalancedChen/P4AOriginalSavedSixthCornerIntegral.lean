import ImbalancedChen.P4AOriginalSavedSixthPlanes

/-! The 64-vertex mean of the actual sixth gap, including its negative
vertices. The nonnegative part is taken before imposing the lower
physical measure and the two residual upper bounds. -/
namespace ImbalancedChen.P4AOriginalSavedSixthCornerIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P4AOriginalSavedSixthPlanes
open P4AOriginalSavedSixthArchive (Row word endpoint oldUpper)
open Certificates.P2OriginalSixthElevenLogSemantics (Physical)
open P5OldFifthFiveCoordinateBarycentric (integral_fraction_Ico integral_one_sub_fraction_Ico)

def frac (i : Row) (t : Physical) (j : Fin 6) : ℝ :=
  (t j-lift (lowerQ i) j)/(lift (upperQ i) j-lift (lowerQ i) j)
def factor (i : Row) (t : Physical) (j : Fin 6) (b : Bool) : ℝ :=
  if b then frac i t j else 1-frac i t j
def weight (i : Row) (b : Corner) (t : Physical) := ∏ j, factor i t j (b j)
def vol (i : Row) : ℝ := ∏ j, lift (upperQ i) j-lift (lowerQ i) j
def interp (i : Row) (g : Corner → ℝ) (t : Physical) := ∑ b, weight i b t*g b

theorem width (i : Row) (j : Fin 6) : lift (lowerQ i) j < lift (upperQ i) j := by
  exact_mod_cast width_pos i j

theorem box_closed (i : Row) : box i ⊆ Icc (lift (lowerQ i)) (lift (upperQ i)) := by
  intro t ht
  have h := mem_logPrimeBox.mp ht
  exact ⟨fun j => (h j).1,fun j => (h j).2.le⟩

theorem weight_nonneg (i : Row) (b : Corner) {t : Physical} (ht : t ∈ box i) : 0 ≤ weight i b t := by
  apply Finset.prod_nonneg
  intro j _
  have hj := mem_logPrimeBox.mp ht j
  by_cases h : b j
  · simpa [factor,h,frac] using div_nonneg (sub_nonneg.mpr hj.1) (sub_nonneg.mpr (width i j).le)
  · have hu : frac i t j ≤ 1 := (div_le_one (sub_pos.mpr (width i j))).mpr (by linarith only [hj.2])
    simpa [factor,h] using sub_nonneg.mpr hu

private theorem factor_sum (i : Row) (t : Physical) (j : Fin 6) :
    ∑ b : Bool,factor i t j b = 1 := by simp [factor,Fintype.sum_bool]

theorem weight_sum (i : Row) (t : Physical) : ∑ b : Corner, weight i b t = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp only [factor_sum,Finset.prod_const_one]

private theorem corner_coord (i : Row) (b : Corner) (j : Fin 6) :
    lift (vertexQ i b) j = if b j then lift (upperQ i) j else lift (lowerQ i) j := by
  cases h : b j <;> simp [vertexQ,lift,h]

theorem coord_sum (i : Row) (t : Physical) (j : Fin 6) :
    ∑ b : Corner, weight i b t*lift (vertexQ i b) j = t j := by
  let c (k : Fin 6) (b : Bool) := if b then lift (upperQ i) k else lift (lowerQ i) k
  have one (b : Corner) : weight i b t*lift (vertexQ i b) j =
      ∏ k,factor i t k (b k)*(if k=j then c k (b k) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [weight,c,corner_coord]
  have hom (k : Fin 6) :
      (∑ b : Bool, factor i t k b*(if k=j then c k b else 1)) = if k=j then t k else 1 := by
    by_cases h : k=j
    · subst k
      simp [c,Fintype.sum_bool,factor,frac]
      field_simp [(sub_pos.mpr (width i j)).ne'] <;> ring
    · simp [h,factor_sum]
  simp_rw [one]
  rw [← Fintype.prod_sum]
  simp [hom]

theorem interp_affine (i : Row) (p : Plane) (t : Physical) :
    interp i (fun b => p.eval (lift (vertexQ i b))) t = p.eval t := by
  unfold interp Plane.eval
  simp_rw [mul_add,Finset.mul_sum]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,weight_sum,one_mul,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ b : Corner, weight i b t*((p.coeff j:ℝ)*lift (vertexQ i b) j)) =
      (p.coeff j:ℝ)*∑ b : Corner,weight i b t*lift (vertexQ i b) j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    _ = _ := by rw [coord_sum]

theorem integral_weight (i : Row) (b : Corner) :
    (∫ t in box i, weight i b t) = vol i/64 := by
  unfold weight factor frac box logPrimeBox
  rw [volume_pi,Measure.restrict_pi_pi,integral_fintype_prod_eq_prod]
  have hm (j : Fin 6) :
      (∫ x in Ico (lift (lowerQ i) j) (lift (upperQ i) j),
        if b j then (x-lift (lowerQ i) j)/(lift (upperQ i) j-lift (lowerQ i) j)
        else 1-(x-lift (lowerQ i) j)/(lift (upperQ i) j-lift (lowerQ i) j)) =
          (lift (upperQ i) j-lift (lowerQ i) j)/2 := by
    cases h : b j
    · simpa [h] using integral_one_sub_fraction_Ico (width i j)
    · simpa [h] using integral_fraction_Ico (width i j)
  simp_rw [hm]
  simp [vol,Finset.prod_div_distrib,Fin.prod_univ_succ] <;> ring

theorem integrable_weight (i : Row) (b : Corner) : IntegrableOn (weight i b) (box i) := by
  unfold IntegrableOn weight factor frac box logPrimeBox
  rw [volume_pi,Measure.restrict_pi_pi]
  apply Integrable.fintype_prod
  intro j
  have h : Continuous (fun x : ℝ => if b j then
      (x-lift (lowerQ i) j)/(lift (upperQ i) j-lift (lowerQ i) j)
      else 1-(x-lift (lowerQ i) j)/(lift (upperQ i) j-lift (lowerQ i) j)) := by
    cases h : b j <;> simp [h] <;> fun_prop
  exact h.integrableOn_Icc.mono_set Ico_subset_Icc_self

theorem integrable_interp (i : Row) (g : Corner → ℝ) : IntegrableOn (interp i g) (box i) :=
  integrable_finset_sum _ (fun b _ => (integrable_weight i b).mul_const _)

theorem integral_interp (i : Row) (g : Corner → ℝ) :
    (∫ t in box i, interp i g t) = (vol i/64)*(∑ b,g b) := by
  unfold interp
  rw [integral_finset_sum _ (fun b _ => (integrable_weight i b).mul_const _)]
  simp_rw [integral_mul_const,integral_weight]
  rw [Finset.mul_sum]

theorem row_interp_le (i : Row) (hg : word i 0 = 400) {t : Physical} (ht : t ∈ box i) :
    interp i (fun b => (gapQ i (vertexQ i b):ℝ)) t ≤ endpoint i t-oldUpper i t := by
  let g (b : Corner) : ℝ := (gapQ i (vertexQ i b):ℝ)
  have h (b : Bool) (m : Fin 32) : interp i g t ≤ (newFace i b).eval t-(oldFace i m).eval t := by
    rw [← eval_sub,← interp_affine i ((newFace i b).sub (oldFace i m)) t]
    apply Finset.sum_le_sum
    intro w _
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg i w ht)
    have hn : endpoint i (lift (vertexQ i w)) ≤ (newFace i b).eval (lift (vertexQ i w)) := by
      rw [← new_min]; cases b <;> first | apply min_le_left | apply min_le_right
    simpa only [g,literal_gap i hg,eval_sub] using sub_le_sub hn (oldFace_le i hg m (lift (vertexQ i w)))
  have ho : oldUpper i t ≤ endpoint i t-interp i g t := by
    apply oldUpper_le i hg
    intro m
    rw [← new_min]
    apply (le_sub_iff_add_le).mpr
    exact le_min (by linarith only [h false m]) (by linarith only [h true m])
  linarith only [ho]

/-- A continuous physical test supported on the archived rectangle can
be integrated independently of the choice of an actual fifth winner.
The original arithmetic comparison later bounds this explicit test. -/
def oldContinuous (i : Row) : List (Fin 32) → Physical → ℝ
  | [],t => rescue.eval t
  | m::ms,t => max ((oldFace i m).eval t) (oldContinuous i ms t)
def gap (i : Row) (t : Physical) : ℝ := endpoint i t-oldUpper i t
theorem continuous_plane (p : Plane) : Continuous p.eval := by unfold Plane.eval; fun_prop
theorem continuous_oldContinuous (i : Row) (ms : List (Fin 32)) : Continuous (oldContinuous i ms) := by
  induction ms with
  | nil => exact continuous_plane rescue
  | cons m ms ih => exact (continuous_plane _).max ih

private theorem oldContinuous_le_iff (i : Row) (ms : List (Fin 32)) (t : Physical) (R : ℝ) :
    oldContinuous i ms t ≤ R ↔ rescue.eval t ≤ R ∧ ∀ m ∈ ms, (oldFace i m).eval t ≤ R := by
  induction ms with
  | nil => simp [oldContinuous]
  | cons m ms ih => simp [oldContinuous,ih,and_assoc,and_left_comm,and_comm]

theorem continuous_gap (i : Row) (hg : word i 0 = 400) : Continuous (gap i) := by
  have hEq : oldUpper i = oldContinuous i (Finset.univ : Finset (Fin 32)).toList := by
    funext t
    let s := (Finset.univ : Finset (Fin 32)).toList
    apply le_antisymm
    · apply oldUpper_le i hg
      intro m
      exact ((oldContinuous_le_iff i s t _).mp le_rfl).2 m (by simp [s])
    · apply (oldContinuous_le_iff i s t _).mpr
      exact ⟨by simpa [oldFace] using oldFace_le i hg (0 : Fin 32) t,fun m _ => oldFace_le i hg m t⟩
  have hnew : Continuous (endpoint i) := by
    have he : endpoint i = fun t => min ((newFace i false).eval t) ((newFace i true).eval t) := by
      funext t; exact (new_min i t).symm
    rw [he]; exact (continuous_plane _).min (continuous_plane _)
  unfold gap
  rw [hEq]
  exact hnew.sub (continuous_oldContinuous i _)

theorem corner_average_positive_gap (i : Row) (hg : word i 0 = 400) :
    (vol i/64)*(∑ b : Corner,(gapQ i (vertexQ i b):ℝ)) ≤ ∫ t in box i,max 0 (gap i t) := by
  rw [← integral_interp]
  apply setIntegral_mono_on (integrable_interp i _)
    ((continuous_const.max (continuous_gap i hg)).integrableOn_Icc.mono_set (box_closed i))
    (measurableSet_logPrimeBox _ _)
  intro t ht
  exact (row_interp_le i hg ht).trans (le_max_right _ _)

end
end ImbalancedChen.P4AOriginalSavedSixthCornerIntegral
