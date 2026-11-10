import ImbalancedChen.P4AOriginalSavedSixthBank
import ImbalancedChen.CurrentUpperEighteenBudget

/-! Authentic saved G4 endpoint and its physical row integrals. The
test on each unit grid-400 rectangle is the actual positive saved gap
divided by the two certified residual bounds and the six coordinate
upper endpoints. On a positive gap it is below the same-node gain of
every admitted fifth cap between the old cube and the original U5. -/
namespace ImbalancedChen.P4AOriginalSavedSixthIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P4AOriginalSavedSixthPlanes
open P4AOriginalSavedSixthBank
open P4AOriginalSavedSixthArchive (Row endpoint oldUpper)
open P4AOriginalSavedSixthCornerIntegral (gap vol corner_average_positive_gap box_closed)
open Certificates.P2OriginalSixthElevenLogSemantics (Physical S6)

def prefQ (i : Row) : ℚ := 4/(oldResidual i*newResidual i*∏ j,upperQ i j)
def rowTest (i : Row) (t : Physical) : ℝ := (prefQ i:ℝ)*max 0 (gap i t)
def rowIntegral (i : Row) : ℝ := ∫ t in box i,rowTest i t

theorem grid (i : Row) : P4AOriginalSavedSixthArchive.word i 0 = 400 := by
  simpa only [P4AOriginalSavedSixthWordAccess.word_eq] using (facts i).grid
theorem residuals_pos (i : Row) : 0 < oldResidual i ∧ 0 < newResidual i := by
  have ho := (facts i).oldPos
  have hn := (facts i).newPos
  unfold oldResidual newResidual unit
  exact ⟨div_pos (by exact_mod_cast ho) (by norm_num),div_pos (by exact_mod_cast hn) (by norm_num)⟩
theorem low (i : Row) (j : Fin 6) : (1/50 : ℚ) ≤ lowerQ i j := by
  dsimp [lowerQ]
  have h := (facts i).left j
  change 8 ≤ P4AOriginalSavedSixthWordAccess.word i ⟨j.val+1,by omega⟩ at h
  exact (le_div_iff₀ (by norm_num : (0:ℚ)<400)).mpr (by norm_num; exact_mod_cast h)
theorem upper_pos (i : Row) (j : Fin 6) : 0 < upperQ i j :=
  ((by norm_num : (0:ℚ)<1/50).trans_le (low i j)).trans (width_pos i j)
theorem pref_pos (i : Row) : 0 < prefQ i :=
  div_pos (by norm_num) (mul_pos (mul_pos (residuals_pos i).1 (residuals_pos i).2)
    (Finset.prod_pos (fun j _ => upper_pos i j)))

theorem volume_value (i : Row) : vol i = (1/400 : ℝ)^6 := by
  have hw (j : Fin 6) : lift (upperQ i) j-lift (lowerQ i) j = (1/400 : ℝ) := by
    simp [lift,upperQ,lowerQ]; ring
  simp only [vol,hw,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem budget_formula (i : Row) :
    budgetQ i = prefQ i*((1/400:ℚ)^6/64)*(ds i/unit) := by
  have hprod : (∏ j, upperQ i j) = (∏ j, ((lo i j:ℚ)+1))/400^6 := by
    simp [upperQ,lo,Finset.prod_div_distrib]
  have hu : (∏ j,((lo i j:ℚ)+1)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro j _
    have h : 8 ≤ lo i j := (facts i).left j
    linarith only [show (8:ℚ) ≤ (lo i j:ℚ) by exact_mod_cast h]
  have ho : (P4AOriginalSavedSixthWordAccess.word i 9:ℚ) ≠ 0 := by
    exact_mod_cast (facts i).oldPos.ne'
  have hn : (P4AOriginalSavedSixthWordAccess.word i 10:ℚ) ≠ 0 := by
    exact_mod_cast (facts i).newPos.ne'
  unfold budgetQ prefQ oldResidual newResidual unit
  rw [hprod]
  field_simp [hu,ho,hn] <;> ring

theorem row_floor_le_integral (i : Row) : (floor80 i:ℝ)/2^80 ≤ rowIntegral i := by
  have hgap : (ds i:ℝ)/(unit:ℝ) = ∑ b : Corner,(gapQ i (vertexQ i b):ℝ) := by
    have h := congrArg (fun x : ℚ => (x:ℝ)) (facts i).gapSum
    push_cast at h
    apply (div_eq_iff (by norm_num [unit] : (unit:ℝ) ≠ 0)).mpr
    linarith only [h]
  have hpoly := mul_le_mul_of_nonneg_left (corner_average_positive_gap i (grid i))
    (show 0 ≤ (prefQ i:ℝ) by exact_mod_cast (pref_pos i).le)
  have hfloor : (floor80 i:ℝ) ≤ (2^80:ℝ)*(budgetQ i:ℝ) := by
    exact_mod_cast Int.floor_le ((2^80:ℚ)*budgetQ i)
  have hQ : (budgetQ i:ℝ) = (prefQ i:ℝ)*((vol i/64)*∑ b : Corner,(gapQ i (vertexQ i b):ℝ)) := by
    rw [budget_formula,volume_value,←hgap]
    push_cast
    ring
  rw [rowIntegral,rowTest,integral_const_mul]
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2^80)).mpr
  calc
    _ ≤ 2^80*(budgetQ i:ℝ) := hfloor
    _ = 2^80*((prefQ i:ℝ)*((vol i/64)*∑ b : Corner,(gapQ i (vertexQ i b):ℝ))) := by rw [hQ]
    _ ≤ _ := by simpa only [mul_comm (2^80:ℝ)] using mul_le_mul_of_nonneg_left hpoly (by norm_num : (0:ℝ) ≤ 2^80)

theorem original_floor_le_sum :
    (145496122603609407505 : ℝ)/151115727451828646838272 ≤ ∑ i : Row,rowIntegral i := by
  calc
    _ = (1163968980828875260040 : ℝ)/2^80 := by norm_num
    _ = (∑ i : Row,(floor80 i:ℝ))/2^80 := by
      exact congrArg (fun x : ℝ => x/2^80) (by exact_mod_cast all_floor_total.symm)
    _ = ∑ i : Row,(floor80 i:ℝ)/2^80 := Finset.sum_div _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => row_floor_le_integral i)

theorem slot_four : currentUpperEighteenGains 3 =
    (145496122603609407505 : ℝ)/151115727451828646838272 := by
  norm_num [currentUpperEighteenGains]

theorem row_integrable (i : Row) : IntegrableOn (rowTest i) (box i) :=
  (continuous_const.mul (continuous_const.max
    (P4AOriginalSavedSixthCornerIntegral.continuous_gap i (grid i)))).integrableOn_Icc.mono_set (box_closed i)

theorem box_disjoint {i j : Row} (hij : i ≠ j) : Disjoint (box i) (box j) := by
  refine Set.disjoint_left.mpr ?_
  intro t hi hj
  apply hij
  apply unique_corner
  funext k
  have hai := mem_logPrimeBox.mp hi k
  have haj := mem_logPrimeBox.mp hj k
  have h1 : (lo i k:ℝ)<(lo j k:ℝ)+1 := by
    have h : (lo i k:ℝ)/400 < ((lo j k:ℝ)+1)/400 := by
      simpa [lift,lowerQ,upperQ,lo] using hai.1.trans_lt haj.2
    exact (div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ)<400)).mp h
  have h2 : (lo j k:ℝ)<(lo i k:ℝ)+1 := by
    have h : (lo j k:ℝ)/400 < ((lo i k:ℝ)+1)/400 := by
      simpa [lift,lowerQ,upperQ,lo] using haj.1.trans_lt hai.2
    exact (div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ)<400)).mp h
  have h1' : lo i k < lo j k+1 := by exact_mod_cast h1
  have h2' : lo j k < lo i k+1 := by exact_mod_cast h2
  omega

theorem above_at (i : Row) (p q : Plane) (d : ℚ) (h : above i p q d)
    {t : Physical} (ht : t ∈ box i) : q.eval t+(d:ℝ) ≤ p.eval t := by
  have hh := lower_le_eval (p.sub q) (box_closed i ht)
  simp only [eval_sub] at hh
  have hc : (d:ℝ) ≤ (lowerBound (p.sub q) (lowerQ i) (upperQ i):ℝ) := by exact_mod_cast h
  linarith
theorem below_at (i : Row) (p : Plane) (d : ℚ) (h : below i p d)
    {t : Physical} (ht : t ∈ box i) : p.eval t ≤ (d:ℝ) :=
  (eval_le_upper p (box_closed i ht)).trans (by exact_mod_cast h)

theorem residual_ceiling (i : Row) {t : Physical} (ht : t ∈ box i) :
    endpoint i t-S6 t ≤ (newResidual i:ℝ) ∧
    (oldUpper i t ≤ endpoint i t → oldUpper i t-S6 t ≤ (oldResidual i:ℝ)) ∧
    endpoint i t-S6 t ≤ 3*t 5 := by
  have LL (b : Bool) : endpoint i t ≤ (newFace i b).eval t := by
    rw [←new_min]; cases b <;> first | apply min_le_left | apply min_le_right
  obtain ⟨bn,hn⟩ := (facts i).newBound
  obtain ⟨bc,hc⟩ := (facts i).cube
  have hnr := below_at i _ _ hn ht
  have hcube := below_at i _ _ hc ht
  simp only [eval_sub,eval_total,eval_scale,eval_coord,Rat.cast_ofNat,Rat.cast_zero] at hnr hcube
  refine ⟨by linarith only [LL bn,hnr],?_,by linarith only [LL bc,hcube]⟩
  intro hgap
  rcases (facts i).oldBound with ho | ⟨b,h⟩
  · apply (sub_le_iff_le_add).mpr
    apply oldUpper_le i (grid i)
    intro m
    have h := below_at i _ _ (ho m) ht
    simp only [eval_sub,eval_total] at h
    linarith
  · have hh := below_at i _ _ h ht
    simp only [eval_sub,eval_total] at hh
    linarith only [LL b,hgap,hh]

/-- Bound the literal signed ordinary rational difference against this
row's own positive mass on the active region. Both denominator upper
bounds and all six coordinate weights are applied after taking the
positive gap. -/
theorem rowTest_le_actual_ordinary (i : Row) {t : Physical} (ht : t ∈ box i) {L : ℝ}
    (hstrict : oldUpper i t < endpoint i t) (hparent : L ≤ oldUpper i t)
    (hres : 0 < L-S6 t) :
    rowTest i t ≤ 4*(endpoint i t-L)/((L-S6 t)*(endpoint i t-S6 t)*(∏ j,t j)) := by
  have htpos (j : Fin 6) : 0 < t j := by
    have hx : (1/50:ℝ) ≤ lift (lowerQ i) j := by exact_mod_cast low i j
    exact (by norm_num : (0:ℝ)<1/50).trans_le (hx.trans (mem_logPrimeBox.mp ht j).1)
  have hQ : 0 < ∏ j,t j := Finset.prod_pos (fun j _ => htpos j)
  have hP := residual_ceiling i ht
  have ho : L-S6 t ≤ (oldResidual i:ℝ) := (sub_le_sub_right hparent _).trans (hP.2.1 hstrict.le)
  have hr : 0 < endpoint i t-S6 t := hres.trans_le (sub_le_sub_right (hparent.trans hstrict.le) _)
  have hM : ∏ j,t j ≤ ∏ j,lift (upperQ i) j :=
    Finset.prod_le_prod (fun j _ => (htpos j).le) (fun j _ => (mem_logPrimeBox.mp ht j).2.le)
  have hden : (L-S6 t)*(endpoint i t-S6 t)*(∏ j,t j) ≤
      (oldResidual i:ℝ)*(newResidual i:ℝ)*(∏ j,lift (upperQ i) j) :=
    mul_le_mul (mul_le_mul ho hP.1 hr.le (hres.le.trans ho)) hM hQ.le
      (mul_nonneg (hres.le.trans ho) (hr.le.trans hP.1))
  have hd0 := mul_pos (mul_pos hres hr) hQ
  have hnum : 0 ≤ 4*(endpoint i t-oldUpper i t) := by linarith
  calc
    _ = 4*(endpoint i t-oldUpper i t)/
      ((oldResidual i:ℝ)*(newResidual i:ℝ)*(∏ j,lift (upperQ i) j)) := by
        simp [rowTest,prefQ,gap,max_eq_right (sub_nonneg.mpr hstrict.le),lift] <;> ring
    _ ≤ 4*(endpoint i t-oldUpper i t)/((L-S6 t)*(endpoint i t-S6 t)*(∏ j,t j)) :=
      div_le_div_of_nonneg_left hnum hd0 hden
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hd0.le

end
end ImbalancedChen.P4AOriginalSavedSixthIntegral
