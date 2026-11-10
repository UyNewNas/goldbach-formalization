import ImbalancedChen.P1OriginalFourthRowSubintervals
import ImbalancedChen.P1OriginalFourthCornerIntegration

/-! Original center picks, sixteen integer corner values and the larger
of the independent correlated margin and the rounded corner mean. -/
namespace ImbalancedChen.P1OriginalFourthRowGap
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P2OriginalFourthCapProducerInterface
open P1OriginalFourthIntegerGapSemantics P1OriginalFourthIntegerGeometryAdmission
open P1OriginalFourthCornerIntegration P1OriginalFourthAllRowsAdmission
open P5OriginalFourthFifthSourceInputs

def left (r : FourthWireRow) : Point := fun i => (r.toProducerRow.lower i:ℝ)
def right (r : FourthWireRow) : Point := fun i => (r.toProducerRow.upper i:ℝ)
def box (r : FourthWireRow) : Set Point := logPrimeBox (left r) (right r)
def gap (r : FourthWireRow) (t : Point) : ℝ := r.toProducerRow.candidate t-oldCap t
def atInteger (a : IntegerAffine) (x : Fin 4 → ℕ) : ℤ :=
  a.constant+∑ i, a.coefficient i*(x i:ℤ)
def midpoint (r : FourthWireRow) : Fin 4 → ℕ := fun i => (r.lo i+r.hi i)/2
def pick (r : FourthWireRow) (j : Fin 6) : Bool :=
  decide (atInteger (sourceOld j true) (midpoint r) < atInteger (sourceOld j false) (midpoint r))
def vertex (r : FourthWireRow) (w : Word) : Fin 4 → ℕ := fun i => if slot w i then r.hi i else r.lo i
def chosenOld (r : FourthWireRow) (w : Word) (j : Fin 6) : ℤ :=
  atInteger (sourceOld j (pick r j)) (vertex r w)
def cornerUnits (r : FourthWireRow) (w : Word) : ℤ :=
  min (atInteger (sourceTent r.toProducerRow.selected false) (vertex r w))
      (atInteger (sourceTent r.toProducerRow.selected true) (vertex r w)) -
    Finset.univ.sup' (show (Finset.univ : Finset (Fin 6)).Nonempty from ⟨0,by simp⟩) (chosenOld r w)
def cornerMean (r : FourthWireRow) : ℤ := ⌊(∑ w, (cornerUnits r w:ℚ))/16⌋
def averageUnits (r : FourthWireRow) : ℤ := max (integerDelta r) (cornerMean r)

theorem box_subset (r : FourthWireRow) : box r ⊆ r.toProducerRow.box := by
  intro t ht
  exact ⟨fun i => (mem_logPrimeBox.mp ht i).1,fun i => (mem_logPrimeBox.mp ht i).2.le⟩

theorem width (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) (i : Fin 4) :
    left r i < right r i := by
  have h := (all_original_rows_geometry r hr).2.2.1 i
  simp only [left,right,fourth_lower,fourth_upper,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]
  exact div_lt_div_of_pos_right (by exact_mod_cast h) (by norm_num)

theorem box_mass (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) :
    volume.real (box r) = vol (left r) (right r) := by
  rw [Measure.real,box,logPrimeBox,volume_pi_pi]
  simp only [Real.volume_Ico,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact ENNReal.toReal_ofReal (sub_pos.mpr (width r hr i)).le

theorem candidate_continuous (r : FourthWireRow) : Continuous r.toProducerRow.candidate := by
  simp only [ProducerRow.candidate,newCap,Affine.eval]
  fun_prop

theorem old_continuous : Continuous oldCap := by
  exact VariableEnvelope.continuous_six.comp
    (show Continuous (fun t : Point => (t 0,t 1,t 2)) by fun_prop)

theorem gap_integrable (r : FourthWireRow) : IntegrableOn (gap r) (box r) :=
  ((candidate_continuous r).sub old_continuous).integrableOn_Icc.mono_set
    (show box r ⊆ Icc (left r) (right r) from box_subset r)

theorem vertex_cast (r : FourthWireRow) (w : Word) (i : Fin 4) :
    corner (left r) (right r) w i = (vertex r w i:ℝ)/204800 := by
  by_cases h : slot w i <;> simp [corner,left,right,vertex,h]

theorem eval_corner (r : FourthWireRow) (w : Word) (a : IntegerAffine) :
    a.toAffine.eval (corner (left r) (right r) w) = (atInteger a (vertex r w):ℝ)/6553600 := by
  simp only [Affine.eval,IntegerAffine.toAffine,vertex_cast,atInteger,Fin.sum_univ_succ]
  push_cast
  ring

theorem corner_le_plane (r : FourthWireRow) (w : Word) (j : Fin 6) (s : Bool) :
    (cornerUnits r w:ℝ)/6553600 ≤ ((tentPlane r.toProducerRow.selected s).sub (oldPiece j (pick r j))).eval
      (corner (left r) (right r) w) := by
  have hold := Finset.le_sup' (chosenOld r w) (Finset.mem_univ j)
  have hnew : min (atInteger (sourceTent r.toProducerRow.selected false) (vertex r w))
        (atInteger (sourceTent r.toProducerRow.selected true) (vertex r w)) ≤
      atInteger (sourceTent r.toProducerRow.selected s) (vertex r w) := by
    cases s <;> first | apply min_le_left | apply min_le_right
  have h : cornerUnits r w ≤ atInteger (sourceTent r.toProducerRow.selected s) (vertex r w) -
      atInteger (sourceOld j (pick r j)) (vertex r w) := sub_le_sub hnew hold
  rw [Affine.eval_sub,← sourceTent_toAffine,← sourceOld_toAffine,eval_corner,eval_corner,← sub_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast h

private def pairUnits (r : FourthWireRow) (j : Fin 6) (s : Bool) : ℤ :=
  max (((sourceTent r.toProducerRow.selected s).sub (programOldPiece j false)).lower r.lo r.hi)
      (((sourceTent r.toProducerRow.selected s).sub (programOldPiece j true)).lower r.lo r.hi)

private theorem pair_scaled (r : FourthWireRow) (j : Fin 6) (s : Bool) :
    gapPiece r.toProducerRow.selected r.toProducerRow.lower r.toProducerRow.upper (pythonToCommon j) s =
      (pairUnits r j s:ℝ)/6553600 := by
  have hs (b : Bool) := congrArg (fun q : ℚ => (q:ℝ))
    (lower_scaled ((sourceTent r.toProducerRow.selected s).sub (programOldPiece j b)) r.lo r.hi)
  simp only [programOldPiece,toAffine_sub,sourceTent_toAffine,sourceOld_toAffine,
    Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] at hs
  change max _ _ = _
  simp only [hs,pairUnits,programOldPiece,Int.cast_max,max_div_div_right (by norm_num : (0:ℝ) ≤ 6553600)]

theorem correlated_le_gap (r : FourthWireRow) (t : Point) (ht : t ∈ r.toProducerRow.box) :
    (integerDelta r:ℝ)/6553600 ≤ gap r t := by
  refine le_trans ?_ (gapLower_le_actual_gap r.toProducerRow.selected _ _ t ht.1 ht.2)
  unfold gapLower
  apply Finset.le_inf'
  intro j _
  have h := Finset.inf'_le (fun x => min (pairUnits r x false) (pairUnits r x true))
    (Finset.mem_univ (commonToPython j))
  have hh (s : Bool) : integerDelta r ≤ pairUnits r (commonToPython j) s := by
    cases s
    · exact h.trans (min_le_left _ _)
    · exact h.trans (min_le_right _ _)
  have hp (s : Bool) := pair_scaled r (commonToPython j) s
  simp only [pythonToCommon_commonToPython] at hp
  apply le_min
  · rw [hp]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hh false) (by norm_num)
  · rw [hp]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hh true) (by norm_num)

theorem original_average_gap (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) :
    vol (left r) (right r)*((averageUnits r:ℝ)/6553600) ≤ ∫ t in box r, gap r t := by
  let V := vol (left r) (right r)
  have hV : 0 ≤ V := Finset.prod_nonneg (fun i _ => (sub_pos.mpr (width r hr i)).le)
  have hm := measurableSet_logPrimeBox (left r) (right r)
  have hconst : V*((integerDelta r:ℝ)/6553600) ≤ ∫ t in box r, gap r t := by
    have hc : IntegrableOn (fun _ : Point => (integerDelta r:ℝ)/6553600) (box r) :=
      continuous_const.integrableOn_Icc.mono_set
        (show box r ⊆ Icc (left r) (right r) from box_subset r)
    have h := setIntegral_mono_on hc (gap_integrable r) hm
      (fun t ht => correlated_le_gap r t (box_subset r ht))
    simpa only [setIntegral_const,box_mass r hr,smul_eq_mul,V] using h
  have hcorn : V*((cornerMean r:ℝ)/6553600) ≤ ∫ t in box r, gap r t := by
    let g (w : Word) := (cornerUnits r w:ℝ)/6553600
    have h := setIntegral_mono_on (integrable_interp (left r) (right r) g) (gap_integrable r) hm
      (fun t ht => corner_gap_le_actual _ (pick r) (left r) (right r) (width r hr) g
        (corner_le_plane r) t (box_subset r ht))
    rw [integral_interp _ _ (width r hr) g] at h
    have hf : (cornerMean r:ℝ) ≤ (∑ w, (cornerUnits r w:ℝ))/16 := by
      exact_mod_cast (Int.floor_le ((∑ w, (cornerUnits r w:ℚ))/16))
    have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hf (by norm_num : (0:ℝ)≤6553600)) hV
    refine hh.trans (le_trans (le_of_eq ?_) h)
    dsimp only [V,g]
    rw [← Finset.sum_div]
    ring
  by_cases h : integerDelta r ≤ cornerMean r
  · simpa only [averageUnits,max_eq_right h] using hcorn
  · simpa only [averageUnits,max_eq_left (le_of_not_ge h)] using hconst

end
end ImbalancedChen.P1OriginalFourthRowGap
