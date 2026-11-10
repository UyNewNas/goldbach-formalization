import ImbalancedChen.P2OriginalFourthCapProducerInterface
import ImbalancedChen.P5OldFifthFiveCoordinateBarycentric

/-! Four-dimensional rectangle interpolation for the manuscript's six
upper affine pieces. Only the established one-coordinate Ico affine
moment is needed. The integral of each of the sixteen true product
weights is exactly one sixteenth of the original rectangle's volume. -/
namespace ImbalancedChen.P1OriginalFourthCornerIntegration
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P5OldFifthFiveCoordinateBarycentric (integral_fraction_Ico integral_one_sub_fraction_Ico)

abbrev Word := Bool × Bool × Bool × Bool
def slot (w : Word) : Fin 4 → Bool := ![w.1,w.2.1,w.2.2.1,w.2.2.2]
def corner (a b : Point) (w : Word) : Point := fun i => if slot w i then b i else a i
def frac (a b : Point) (t : Point) (i : Fin 4) : ℝ := (t i-a i)/(b i-a i)
def weight (a b : Point) (w : Word) (t : Point) : ℝ :=
  ∏ i, if slot w i then frac a b t i else 1-frac a b t i
def vol (a b : Point) : ℝ := ∏ i, b i-a i
def interp (a b : Point) (g : Word → ℝ) (t : Point) : ℝ := ∑ w, weight a b w t*g w

theorem weight_nonneg (a b : Point) (hab : ∀ i, a i < b i) (w : Word)
    {t : Point} (ht : t ∈ Icc a b) : 0 ≤ weight a b w t := by
  apply Finset.prod_nonneg
  intro i _
  by_cases h : slot w i
  · simpa [h,frac] using div_nonneg (sub_nonneg.mpr (ht.1 i)) (sub_nonneg.mpr (hab i).le)
  · have h1 : frac a b t i ≤ 1 := (div_le_one (sub_pos.mpr (hab i))).mpr (by linarith [ht.2 i])
    simpa [h] using sub_nonneg.mpr h1

/-- Independent affine functions interpolate exactly. The four coordinate
identities do not involve smoothness of the coupled minimum/maximum. -/
theorem interp_affine (a b : Point) (hab : ∀ i, a i < b i) (A : Affine) (t : Point) :
    interp a b (fun w => A.eval (corner a b w)) t = A.eval t := by
  have hcoord (i : Fin 4) : (1-frac a b t i)*a i + frac a b t i*b i = t i := by
    unfold frac
    field_simp [(sub_pos.mpr (hab i)).ne'] <;> ring
  calc
    _ = (A.constant:ℝ) + ∑ i, (A.coefficient i:ℝ)*((1-frac a b t i)*a i+frac a b t i*b i) := by
      simp [interp,weight,corner,slot,Affine.eval,Fintype.sum_prod_type,Fintype.sum_bool,
        Fin.sum_univ_succ,Fin.prod_univ_succ]
      <;> ring
    _ = _ := by simp only [hcoord,Affine.eval]

theorem integrable_weight (a b : Point) (w : Word) :
    IntegrableOn (weight a b w) (logPrimeBox a b) := by
  unfold IntegrableOn weight frac logPrimeBox
  rw [volume_pi,Measure.restrict_pi_pi]
  apply Integrable.fintype_prod
  intro i
  have hc : Continuous (fun x : ℝ =>
      if slot w i then (x-a i)/(b i-a i) else 1-(x-a i)/(b i-a i)) := by
    by_cases hi : slot w i <;> simp [hi] <;> fun_prop
  exact hc.integrableOn_Icc.mono_set Ico_subset_Icc_self

theorem integral_weight (a b : Point) (hab : ∀ i, a i < b i) (w : Word) :
    (∫ t in logPrimeBox a b, weight a b w t) = vol a b/16 := by
  unfold weight frac logPrimeBox
  rw [volume_pi,Measure.restrict_pi_pi,integral_fintype_prod_eq_prod]
  have hm (i : Fin 4) :
      (∫ x in Ico (a i) (b i), if slot w i then (x-a i)/(b i-a i)
        else 1-(x-a i)/(b i-a i)) = (b i-a i)/2 := by
    by_cases hi : slot w i
    · simpa [hi] using integral_fraction_Ico (hab i)
    · simpa [hi] using integral_one_sub_fraction_Ico (hab i)
  simp_rw [hm]
  simp [vol,Finset.prod_div_distrib,Fin.prod_univ_succ]
  <;> ring

theorem integrable_interp (a b : Point) (g : Word → ℝ) :
    IntegrableOn (interp a b g) (logPrimeBox a b) :=
  integrable_finset_sum _ (fun w _ => (integrable_weight a b w).mul_const (g w))

theorem integral_interp (a b : Point) (hab : ∀ i, a i < b i) (g : Word → ℝ) :
    (∫ t in logPrimeBox a b, interp a b g t) = vol a b*(∑ w, g w)/16 := by
  unfold interp
  rw [integral_finset_sum _ (fun w _ => (integrable_weight a b w).mul_const (g w))]
  simp_rw [integral_mul_const,integral_weight a b hab]
  rw [← Finset.mul_sum]
  ring

theorem corner_gap_le_actual (I : Finset (Fin 4)) (pick : Fin 6 → Bool) (a b : Point)
    (hab : ∀ i, a i < b i) (g : Word → ℝ)
    (hg : ∀ w j s, g w ≤ ((tentPlane I s).sub (oldPiece j (pick j))).eval (corner a b w))
    (t : Point) (ht : t ∈ Icc a b) :
    interp a b g t ≤ newCap I t-oldCap t := by
  have h (j : Fin 6) (s : Bool) : interp a b g t ≤ (tentPlane I s).eval t-(oldPiece j (pick j)).eval t := by
    rw [← Affine.eval_sub,← interp_affine a b hab]
    exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hg w j s) (weight_nonneg a b hab w ht))
  have ho : oldCap t ≤ newCap I t-interp a b g t := by
    apply oldCap_le_of_components
    intro j
    have hchoose : oldComponent t j ≤ (oldPiece j (pick j)).eval t := by
      cases hp : pick j <;> simp only [oldComponent,hp] <;> first | apply min_le_left | apply min_le_right
    have h0 := h j false
    have h1 := h j true
    change oldComponent t j ≤ min _ _ - interp a b g t
    apply (le_sub_iff_add_le).mpr
    exact le_min (by linarith only [hchoose,h0]) (by linarith only [hchoose,h1])
  linarith only [ho]

end
end ImbalancedChen.P1OriginalFourthCornerIntegration
