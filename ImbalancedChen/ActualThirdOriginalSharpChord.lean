import ImbalancedChen.ActualThirdOriginalLocalCurvature
import Mathlib.Analysis.Convex.Deriv

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Sharp endpoint-chord error from actual original-cell curvature.
Append this tail after the actual-local-curvature SOURCEONLY supplier, with
Mathlib.Analysis.Convex.Deriv imported at the top of the standalone file.
The endpoint chord uses the actual L/H endpoint values, not supplied node
intervals. No desired query enclosure or numerical curvature is a premise.
-/
namespace ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

noncomputable section
open Set

/-- The affine chord of the actual endpoint values. -/
def endpointChord (f : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  (b-t)/(b-a)*f a + (t-a)/(b-a)*f b

theorem endpointChord_neg (f : ℝ → ℝ) (a b t : ℝ) :
    endpointChord (fun x => -f x) a b t = -endpointChord f a b t := by
  unfold endpointChord
  ring

/-- A local analytic lemma with derivatives only in the open cell. Closed-cell
continuity supplies both endpoints, so endpoint C2 is never required. -/
theorem concave_chord_of_local_second_bounds
    {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hab : a < b) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Ioo a b, -M ≤ f'' x ∧ f'' x ≤ 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ f t - endpointChord f a b t ∧
    f t - endpointChord f a b t ≤ M*(t-a)*(b-t)/2 ∧
    M*(t-a)*(b-t)/2 ≤ M*(b-a)^2/8 := by
  have hc : ConcaveOn ℝ (Icc a b) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f') (f'' := f'')
      (convex_Icc a b) hf
    · intro x hx
      exact (hf' x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      exact (hf'' x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      exact (hbound x (by simpa only [interior_Icc] using hx)).2
  have hg : ConvexOn ℝ (Icc a b) (fun x => f x + M*x^2/2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun x => f' x + M*x) (f'' := fun x => f'' x + M)
      (convex_Icc a b)
    · exact hf.add ((((continuous_id.pow 2).const_mul M).div_const 2).continuousOn)
    · intro x hx
      have hxi : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
      have hd := (hf' x hxi).add
        ((((hasDerivAt_id x).pow 2).const_mul M).div_const 2)
      have hd' : HasDerivAt (fun u => f u + M*u^2/2) (f' x + M*x) x := by
        apply hd.congr_deriv
        change f' x + M*((2 : ℝ)*x^(2-1)*1)/2 = f' x + M*x
        ring
      exact hd'.hasDerivWithinAt
    · intro x hx
      have hxi : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
      have hd := (hf'' x hxi).add ((hasDerivAt_id x).const_mul M)
      have hd' : HasDerivAt (fun u => f' u + M*u) (f'' x + M) x := by
        simpa only [mul_one, id_eq] using! hd
      exact hd'.hasDerivWithinAt
    · intro x hx
      have h := (hbound x (by simpa only [interior_Icc] using hx)).1
      linarith only [h]
  let w0 : ℝ := (b-t)/(b-a)
  let w1 : ℝ := (t-a)/(b-a)
  have hd : 0 < b-a := sub_pos.mpr hab
  have hw0 : 0 ≤ w0 := div_nonneg (sub_nonneg.mpr ht.2) hd.le
  have hw1 : 0 ≤ w1 := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hsum : w0+w1=1 := by
    dsimp [w0, w1]
    field_simp [ne_of_gt hd]
    ring
  have harg : w0*a+w1*b=t := by
    dsimp [w0, w1]
    field_simp [ne_of_gt hd]
    ring
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hlo := hc.2 ha hb hw0 hw1 hsum
  have hhi := hg.2 ha hb hw0 hw1 hsum
  simp only [smul_eq_mul, harg] at hlo hhi
  have hchord : w0*f a+w1*f b = endpointChord f a b t := rfl
  rw [hchord] at hlo
  have hquadratic : w0*(f a+M*a^2/2)+w1*(f b+M*b^2/2)-M*t^2/2 =
      endpointChord f a b t + M*(t-a)*(b-t)/2 := by
    dsimp [w0, w1, endpointChord]
    field_simp [ne_of_gt hd]
    ring
  refine ⟨sub_nonneg.mpr hlo, ?_, ?_⟩
  · linarith only [hhi, hquadratic]
  · nlinarith [mul_nonneg hM (sq_nonneg (2*t-a-b))]

/-- The convex counterpart is the same analytic argument applied to -f. -/
theorem convex_chord_of_local_second_bounds
    {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hab : a < b) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Ioo a b, 0 ≤ f'' x ∧ f'' x ≤ M)
    {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ endpointChord f a b t - f t ∧
    endpointChord f a b t - f t ≤ M*(t-a)*(b-t)/2 ∧
    M*(t-a)*(b-t)/2 ≤ M*(b-a)^2/8 := by
  have h := concave_chord_of_local_second_bounds
    (f := fun x => -f x) (f' := fun x => -f' x) (f'' := fun x => -f'' x)
    hab hM hf.neg (fun x hx => (hf' x hx).neg) (fun x hx => (hf'' x hx).neg)
    (fun x hx => ⟨neg_le_neg (hbound x hx).2, neg_nonpos.mpr (hbound x hx).1⟩) ht
  have heq : -f t - endpointChord (fun x => -f x) a b t =
      endpointChord f a b t - f t := by
    rw [endpointChord_neg]
    ring
  rw [heq] at h
  exact h

/-- Literal original grid geometry and its original local curvature. -/
def cellLeft (i : ℕ) : ℝ := (i : ℝ)/16384
def cellRight (i : ℕ) : ℝ := ((i : ℝ)+1)/16384
def cellCurvature (i : ℕ) : ℝ := 1/(cellLeft i-1)

theorem original_cell_width (i : ℕ) : cellRight i-cellLeft i = 1/16384 := by
  unfold cellRight cellLeft
  ring

theorem original_cell_lt (i : ℕ) : cellLeft i < cellRight i := by
  have h := original_cell_width i
  linarith

theorem original_cell_curvature_nonneg (i : ℕ) (hi : 32768 ≤ i) :
    0 ≤ cellCurvature i := by
  have hiR : (32768 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  unfold cellCurvature cellLeft
  apply div_nonneg (by norm_num)
  linarith

theorem original_cell_allowance (i : ℕ) (hi : 32768 ≤ i) :
    cellCurvature i*(cellRight i-cellLeft i)^2/8 =
      1/(8*16384*((i : ℝ)-16384)) := by
  rw [original_cell_width]
  exact original_cell_curvature_allowance i hi

/-- Actual sharp lower-numerator chord remainder on EVERY original cell.
The only hypotheses are an integer cell index and membership in that cell.
All function/curvature/continuity inputs are supplied by the genuine source. -/
theorem original_L_cell_chord (i : ℕ) (hi : 32768 ≤ i)
    {t : ℝ} (ht : t ∈ Icc (cellLeft i) (cellRight i)) :
    0 ≤ L t-endpointChord L (cellLeft i) (cellRight i) t ∧
    L t-endpointChord L (cellLeft i) (cellRight i) t ≤
      cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ∧
    cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ≤
      1/(8*16384*((i : ℝ)-16384)) := by
  have hc : ContinuousOn L (Icc (cellLeft i) (cellRight i)) := by
    apply continuousOn_L.mono
    intro x hx
    have hiR : (32768 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    change 2 ≤ x
    dsimp [cellLeft, cellRight] at hx
    linarith [hx.1]
  have h := concave_chord_of_local_second_bounds
    (f := L) (f' := fun s => upper (s-1)) (f'' := Lcurvature)
    (original_cell_lt i) (original_cell_curvature_nonneg i hi) hc
    (fun s hs => (original_L_cell_curvature i hi hs).1)
    (fun s hs => (original_L_cell_curvature i hi hs).2.1)
    (fun s hs => (original_L_cell_curvature i hi hs).2.2) ht
  refine ⟨h.1, h.2.1, ?_⟩
  calc
    _ ≤ cellCurvature i*(cellRight i-cellLeft i)^2/8 := h.2.2
    _ = _ := original_cell_allowance i hi

/-- Actual sharp upper-numerator chord remainder on every nonconstant cell.
Below the upper cutoff3, the already proved H_eq_one supplies the exact value. -/
theorem original_H_nonconstant_cell_chord (i : ℕ) (hi : 49152 ≤ i)
    {t : ℝ} (ht : t ∈ Icc (cellLeft i) (cellRight i)) :
    0 ≤ endpointChord H (cellLeft i) (cellRight i) t-H t ∧
    endpointChord H (cellLeft i) (cellRight i) t-H t ≤
      cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ∧
    cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ≤
      1/(8*16384*((i : ℝ)-16384)) := by
  have hi2 : 32768 ≤ i := by omega
  have hc : ContinuousOn H (Icc (cellLeft i) (cellRight i)) := by
    apply continuousOn_H.mono
    intro x hx
    have hiR : (49152 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    change 3 ≤ x
    dsimp [cellLeft, cellRight] at hx
    linarith [hx.1]
  have h := convex_chord_of_local_second_bounds
    (f := H) (f' := fun s => lower (s-1)) (f'' := Hcurvature)
    (original_cell_lt i) (original_cell_curvature_nonneg i hi2) hc
    (fun s hs => (original_H_cell_curvature i hi hs).1)
    (fun s hs => (original_H_cell_curvature i hi hs).2.1)
    (fun s hs => (original_H_cell_curvature i hi hs).2.2) ht
  refine ⟨h.1, h.2.1, ?_⟩
  calc
    _ ≤ cellCurvature i*(cellRight i-cellLeft i)^2/8 := h.2.2
    _ = _ := original_cell_allowance i hi2


/-- In the original upper initial cells all actual endpoint/interior values
are exactly one, so the chord error is exactly zero. -/
theorem original_H_initial_cell_chord (i : ℕ) (hi : 32768 ≤ i) (hi3 : i < 49152)
    {t : ℝ} (ht : t ∈ Icc (cellLeft i) (cellRight i)) :
    endpointChord H (cellLeft i) (cellRight i) t = H t := by
  have hiR : (32768 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hi3R : (i : ℝ)+1 ≤ 49152 := by exact_mod_cast (show i+1 ≤ 49152 by omega)
  have ha1 : 1 < cellLeft i := by dsimp [cellLeft]; linarith
  have hb3 : cellRight i ≤ 3 := by dsimp [cellRight]; linarith
  have hab := original_cell_lt i
  have ha := H_eq_one ha1 (hab.le.trans hb3)
  have hb := H_eq_one (ha1.trans hab) hb3
  have hv := H_eq_one (ha1.trans_le ht.1) (ht.2.trans hb3)
  have hd : cellRight i-cellLeft i ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  unfold endpointChord
  rw [ha, hb, hv]
  field_simp [hd]
  ring

/-- All original H cells, including the constant initial cells below3.
Together with original_L_cell_chord this covers every original [2,12] cell. -/
theorem original_H_cell_chord (i : ℕ) (hi : 32768 ≤ i)
    {t : ℝ} (ht : t ∈ Icc (cellLeft i) (cellRight i)) :
    0 ≤ endpointChord H (cellLeft i) (cellRight i) t-H t ∧
    endpointChord H (cellLeft i) (cellRight i) t-H t ≤
      cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ∧
    cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ≤
      1/(8*16384*((i : ℝ)-16384)) := by
  by_cases hi3 : 49152 ≤ i
  · exact original_H_nonconstant_cell_chord i hi3 ht
  · have hz := original_H_initial_cell_chord i hi (by omega) ht
    have hzero : endpointChord H (cellLeft i) (cellRight i) t-H t = 0 := by
      rw [hz]
      ring
    have hM := original_cell_curvature_nonneg i hi
    have hp : 0 ≤ cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 :=
      div_nonneg (mul_nonneg (mul_nonneg hM (sub_nonneg.mpr ht.1))
        (sub_nonneg.mpr ht.2)) (by norm_num)
    have hmax : cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ≤
        cellCurvature i*(cellRight i-cellLeft i)^2/8 := by
      nlinarith [mul_nonneg hM (sq_nonneg (2*t-cellLeft i-cellRight i))]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hzero] using (le_refl (0 : ℝ))
    · rw [hzero]
      exact hp
    · calc
        _ ≤ cellCurvature i*(cellRight i-cellLeft i)^2/8 := hmax
        _ = _ := original_cell_allowance i hi

theorem original_L_cell_chord_abs (i : ℕ) (hi : 32768 ≤ i)
    {t : ℝ} (ht : t ∈ Icc (cellLeft i) (cellRight i)) :
    |L t-endpointChord L (cellLeft i) (cellRight i) t| ≤
      cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ∧
    cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ≤
      1/(8*16384*((i : ℝ)-16384)) := by
  have h := original_L_cell_chord i hi ht
  rw [abs_of_nonneg h.1]
  exact h.2

theorem original_H_cell_chord_abs (i : ℕ) (hi : 32768 ≤ i)
    {t : ℝ} (ht : t ∈ Icc (cellLeft i) (cellRight i)) :
    |H t-endpointChord H (cellLeft i) (cellRight i) t| ≤
      cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ∧
    cellCurvature i*(t-cellLeft i)*(cellRight i-t)/2 ≤
      1/(8*16384*((i : ℝ)-16384)) := by
  have h := original_H_cell_chord i hi ht
  rw [abs_sub_comm, abs_of_nonneg h.1]
  exact h.2

/-- Exact112-bit unrounded upper bound for the original lower-numerator
interpolation error. Its integer ceiling remains the original local ceiling. -/
theorem original_L_cell_chord_112bit (i : ℕ) (hi : 32768 ≤ i)
    {t : ℝ} (ht : t ∈ Icc (cellLeft i) (cellRight i)) :
    (2^112 : ℝ)*(L t-endpointChord L (cellLeft i) (cellRight i) t) ≤
      (2^112 : ℝ)/(8*16384*((i : ℝ)-16384)) := by
  have h := original_L_cell_chord i hi ht
  have hm := mul_le_mul_of_nonneg_left (h.2.1.trans h.2.2)
    (by positivity : (0 : ℝ) ≤ 2^112)
  simpa only [mul_one_div] using hm

theorem original_H_cell_chord_112bit (i : ℕ) (hi : 32768 ≤ i)
    {t : ℝ} (ht : t ∈ Icc (cellLeft i) (cellRight i)) :
    (2^112 : ℝ)*(endpointChord H (cellLeft i) (cellRight i) t-H t) ≤
      (2^112 : ℝ)/(8*16384*((i : ℝ)-16384)) := by
  have h := original_H_cell_chord i hi ht
  have hm := mul_le_mul_of_nonneg_left (h.2.1.trans h.2.2)
    (by positivity : (0 : ℝ) ≤ 2^112)
  simpa only [mul_one_div] using hm

end
end ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
