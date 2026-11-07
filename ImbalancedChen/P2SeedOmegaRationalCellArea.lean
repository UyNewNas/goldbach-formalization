import ImbalancedChen.P2SeedOmegaFiniteCellSum

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact rational geometry of the original bad-domain/mesh intersections.
Fubini identifies each ACTUAL cell volume with its clipped v-length.
The original one-third split then gives a rational squared-positivepart
formula, including cells crossing that split. Top singleton areas were
paid separately in FiniteCellSum. No area/sample/passing bound is evaluated.
-/

namespace ImbalancedChen.P2SeedOmegaRationalCellArea
noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators Interval
open P2SeedOmegaLiteralFibre
open P2SeedOmegaBadCellSemantics (actualBadKernel)
open P2SeedOmegaBadUniformIntegralError
open P2SeedOmegaFiniteMesh
open P2SeedOmegaMeshAdmissibility
open P2SeedOmegaFiniteMeshLimit
open P2SeedOmegaAffineClipArea
open P2SeedOmegaFiniteCellSum

def hiNode (n : ℕ) (j : Fin (n+1)) : ℝ := logPrimeMeshPoint corner a2 n (j.val+1)

def splitArea (a b c d : ℝ) : ℝ :=
  if b≤(1/3:ℝ) then risingArea a b c d else
  if (1/3:ℝ)≤a then fallingArea a b c d else
    risingArea a (1/3) c d+fallingArea (1/3) b c d

theorem integral_original_clipped_area {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) :
    (∫ u in a..b,max 0 (d-max c (badLower u)))=splitArea a b c d := by
  have hfirst : ∀ l r : ℝ,l≤r→r≤(1/3:ℝ)→
      (∫ u in l..r,max 0 (d-max c (badLower u)))=risingArea l r c d := by
    intro l r hlr hr
    calc
      _ = ∫ u in l..r,max 0 (d-max c (1-2*u)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hlr] at hu
        rw [badLower,bad_first_lower (hu.2.trans hr)]
      _ = _ := integral_first_piece_clipped hlr hcd
  have hsecond : ∀ l r : ℝ,l≤r→(1/3:ℝ)≤l→
      (∫ u in l..r,max 0 (d-max c (badLower u)))=fallingArea l r c d := by
    intro l r hlr hl
    calc
      _ = ∫ u in l..r,max 0 (d-max c u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hlr] at hu
        rw [badLower,bad_second_lower (hl.trans hu.1)]
      _ = _ := integral_second_piece_clipped hlr hcd
  unfold splitArea
  split_ifs with hb ha
  · exact hfirst a b hab hb
  · exact hsecond a b hab ha
  · have ha0 : a≤(1/3:ℝ) := (lt_of_not_ge ha).le
    have hb0 : (1/3:ℝ)≤b := (lt_of_not_ge hb).le
    have hc : Continuous (fun u : ℝ =>max 0 (d-max c (badLower u))) := by
      unfold badLower
      fun_prop
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable a (1/3:ℝ)) (hc.intervalIntegrable (1/3:ℝ) b)
    rw [←hs,hfirst a (1/3) ha0 le_rfl,hsecond (1/3) b hb0 le_rfl]

theorem weight_eq_clipped_integral (n : ℕ) (i j : Fin (n+1)) :
    weight n (some i) (some j)=
      ∫ u in node n i..hiNode n i,max 0 (hiNode n j-max (node n j) (badLower u)) := by
  have hi := logPrimeMeshLoHi_bounds (d:=1) (by norm_num [corner,a2] : corner<a2)
    n (fun _ =>i) 0
  have hj := logPrimeMeshLoHi_bounds (d:=1) (by norm_num [corner,a2] : corner<a2)
    n (fun _ =>j) 0
  let F := (cell n (some i) (some j)).indicator (fun _ : ℝ×ℝ =>(1:ℝ))
  have hF : Integrable F := cell_constant_integrable n (some i) (some j) 1
  have hf (u : ℝ) : (∫ v : ℝ,F (u,v))=
      (scalarCell n i).indicator
        (fun u =>max 0 (hiNode n j-max (node n j) (badLower u))) u := by
    by_cases hu : u ∈ scalarCell n i
    · rw [indicator_of_mem hu]
      have hU : u ∈ Icc corner a2 := band_mem_range (i:=some i) hu
      have hmem (v : ℝ) : (u,v) ∈ cell n (some i) (some j) ↔
          v ∈ Ico (max (node n j) (badLower u)) (hiNode n j) := by
        constructor
        · intro hv
          exact ⟨max_le_iff.mpr ⟨hv.2.2.1,hv.1.2⟩,hv.2.2.2⟩
        · intro hv
          have hv0 := (max_le_iff.mp hv.1).1
          have hvg := (max_le_iff.mp hv.1).2
          have hV : v ∈ Icc (badLower u) a2 := ⟨hvg,hv.2.le.trans hj.2.2⟩
          exact ⟨(badClosed_dictionary u v).mpr ⟨hU,hV⟩,hu,⟨hv0,hv.2⟩⟩
      have he (v : ℝ) : F (u,v)=
          (Ico (max (node n j) (badLower u)) (hiNode n j)).indicator (fun _ =>(1:ℝ)) v := by
        by_cases hv : v ∈ Ico (max (node n j) (badLower u)) (hiNode n j)
        · simp only [F,indicator_of_mem ((hmem v).mpr hv),indicator_of_mem hv]
        · simp only [F,indicator_of_notMem (fun h =>hv ((hmem v).mp h)),indicator_of_notMem hv]
      simp_rw [he]
      rw [integral_indicator measurableSet_Ico,setIntegral_const,smul_eq_mul]
      simp only [Measure.real,Real.volume_Ico,ENNReal.toReal_ofReal',mul_one,max_comm]
    · rw [indicator_of_notMem hu]
      have he : (fun v : ℝ =>F (u,v))=0 := by
        funext v
        exact indicator_of_notMem (fun h =>hu h.2.1) _
      rw [he]
      simp
  calc
    _ = ∫ p : ℝ×ℝ,F p := by
      symm
      simpa only [one_mul] using integral_cell_constant n (some i) (some j) (1:ℝ)
    _ = ∫ u : ℝ,∫ v : ℝ,F (u,v) := integral_prod F hF
    _ = _ := by
      simp_rw [hf]
      rw [integral_indicator measurableSet_Ico,integral_Ico_eq_integral_Ioc,
        ←intervalIntegral.integral_of_le hi.2.1.le]

def risingQ (a b c d : ℚ) : ℚ :=
  ((max 0 (d-1+2*b))^2-(max 0 (d-1+2*a))^2-
    (max 0 (c-1+2*b))^2+(max 0 (c-1+2*a))^2)/4
def fallingQ (a b c d : ℚ) : ℚ :=
  ((max 0 (d-a))^2-(max 0 (d-b))^2-
    (max 0 (c-a))^2+(max 0 (c-b))^2)/2
def splitAreaQ (a b c d : ℚ) : ℚ :=
  if b≤(1/3:ℚ) then risingQ a b c d else
  if (1/3:ℚ)≤a then fallingQ a b c d else
    risingQ a (1/3) c d+fallingQ (1/3) b c d
def rationalHi (n : ℕ) (j : Fin (n+1)) : ℚ :=
  19/58+((j.val+1:ℕ):ℚ)*((10/29-19/58)/(n+1:ℚ))
def rationalArea (n : ℕ) (i j : Fin (n+1)) : ℚ :=
  splitAreaQ (rationalNode n i) (rationalHi n i) (rationalNode n j) (rationalHi n j)

theorem risingQ_cast (a b c d : ℚ) :
    (risingQ a b c d:ℝ)=risingArea a b c d := by
  simp only [risingQ,risingArea,positive,Rat.cast_div,Rat.cast_add,Rat.cast_sub,
    Rat.cast_mul,Rat.cast_pow,Rat.cast_max,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one]

theorem fallingQ_cast (a b c d : ℚ) :
    (fallingQ a b c d:ℝ)=fallingArea a b c d := by
  simp only [fallingQ,fallingArea,positive,Rat.cast_div,Rat.cast_add,Rat.cast_sub,
    Rat.cast_pow,Rat.cast_max,Rat.cast_ofNat,Rat.cast_zero]

theorem splitAreaQ_cast (a b c d : ℚ) :
    (splitAreaQ a b c d:ℝ)=splitArea a b c d := by
  by_cases hb : b≤(1/3:ℚ)
  · have hbR : (b:ℝ)≤(1/3:ℝ) := by exact_mod_cast hb
    simp only [splitAreaQ,splitArea,if_pos hb,if_pos hbR,risingQ_cast]
  · have hbR : ¬(b:ℝ)≤(1/3:ℝ) := by exact_mod_cast hb
    by_cases ha : (1/3:ℚ)≤a
    · have haR : (1/3:ℝ)≤(a:ℝ) := by exact_mod_cast ha
      simp only [splitAreaQ,splitArea,if_neg hb,if_neg hbR,if_pos ha,if_pos haR,fallingQ_cast]
    · have haR : ¬(1/3:ℝ)≤(a:ℝ) := by exact_mod_cast ha
      simp only [splitAreaQ,splitArea,if_neg hb,if_neg hbR,if_neg ha,if_neg haR,
        Rat.cast_add,risingQ_cast,fallingQ_cast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]

theorem rationalHi_cast (n : ℕ) (j : Fin (n+1)) :
    (rationalHi n j:ℝ)=hiNode n j := by
  simp only [rationalHi,hiNode,logPrimeMeshPoint,logPrimeMeshStep,corner,a2,
    Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_natCast,
    Rat.cast_ofNat,Rat.cast_one,Nat.cast_add,Nat.cast_one]

/-- Exact rational AREA of the actual original bad-domain cell,
including the cell that crosses u=1/3. No cell is sampled for its area. -/
theorem actual_weight_eq_rationalArea (n : ℕ) (i j : Fin (n+1)) :
    weight n (some i) (some j)=(rationalArea n i j:ℝ) := by
  have hi := logPrimeMeshLoHi_bounds (d:=1) (by norm_num [corner,a2] : corner<a2)
    n (fun _ =>i) 0
  have hj := logPrimeMeshLoHi_bounds (d:=1) (by norm_num [corner,a2] : corner<a2)
    n (fun _ =>j) 0
  rw [weight_eq_clipped_integral,integral_original_clipped_area hi.2.1.le hj.2.1.le]
  symm
  simp only [rationalArea,splitAreaQ_cast,rationalNode_cast,rationalHi_cast]

/-- Actual mesh integral = an explicit finite sum with exact rational
geometric weights and true Buchstab values at rational original nodes. -/
theorem meshCost_eq_rational_weight_sum (alpha : ℝ) (n : ℕ) :
    meshCost n alpha=∑ i : Fin (n+1),∑ j : Fin (n+1),
      actualBadKernel alpha (node n i) (node n j)*(rationalArea n i j:ℝ) := by
  have hL (i : BandIndex n) : weight n none i=0 := (top_band_weights_zero n i).1
  have hR (i : BandIndex n) : weight n i none=0 := (top_band_weights_zero n i).2
  rw [meshCost_eq_finite_sum]
  simp only [Fintype.sum_option,hL,hR,mul_zero,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [actual_weight_eq_rationalArea]
  rfl

theorem actual_bad_cost_explicit_finite_sum_error (n : ℕ) {alpha : ℝ} (ha : 2≤alpha) :
    |P2SeedOmegaBadGlobalCost.actualBadCost alpha-
      (∑ i : Fin (n+1),∑ j : Fin (n+1),
        actualBadKernel alpha (node n i) (node n j)*(rationalArea n i j:ℝ))|≤8192*step n := by
  rw [←meshCost_eq_rational_weight_sum]
  exact actual_finite_mesh_error n ha

end
end ImbalancedChen.P2SeedOmegaRationalCellArea
