import ImbalancedChen.P5ZU1011OriginalFifteenNativeGridCells
import ImbalancedChen.P5ZU1011OriginalSixteenEligibilityGridCompleteness

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Coverage for the SEPARATE gate-upper/cap-lower Boolean test actually used
by the original15 fixed-cell native dispatcher. This is stronger than
merely checking a correlated cap-minus-gate form. Both separate endpoint
errors are paid, giving48 times the coordinate width. A true eligible
point whose owner box fails the concrete test lies in a thin strip of one
of the SAME proper original eligibility walls. No coverage, strip-volume,
uniform family, AP or mean estimate is a premise. W16 is excluded.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenSeparateGridCoverage

noncomputable section
open scoped BigOperators
open Classical
open Set U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalFifteenNativeGridCells
open P2OriginalFourthCapProducerInterface

def lhsPiece (p : Policy) : Gate → Affine
  | .half => halfPiece
  | .full j => fullSquarePiece j
  | .selected j => selectedSquarePiece p j
  | .wExtra => wExtraPiece
  | .wX => wXSlack

private theorem mask_margin_eq (p : Policy) (hp : p.val < 15) (left : Bool) (g : Gate)
    (hg : Required p g) : margin p left g = (capPiece p left).sub (lhsPiece p g) := by
  cases g <;> try rfl
  exact (hg hp).elim

theorem cap_coefficient_bound (p : Policy) (left : Bool) (i : Fin 4) :
    |((capPiece p left).coefficient i : ℝ)| ≤ 6 := by
  by_cases hp : p.val < 15 <;> cases left <;>
    simp [capPiece,hp] <;> split_ifs <;> norm_num

theorem lhs_coefficient_bound (p : Policy) (g : Gate) (i : Fin 4) :
    |((lhsPiece p g).coefficient i : ℝ)| ≤ 6 := by
  cases g <;> simp [lhsPiece,halfPiece,fullSquarePiece,selectedSquarePiece,wExtraPiece,wXSlack] <;>
    split_ifs <;> norm_num

private def lowerCorner (a : Affine) (B : Box) (i : Fin 4) : ℚ :=
  if 0 ≤ a.coefficient i then B.lo i else B.hi i

private theorem lower_endpoint_error (a : Affine) (B : Box) (v : LogFour) (eps : ℝ)
    (hv : v ∈ B.region) (hw : WidthLe B eps)
    (hc : ∀ i, |(a.coefficient i : ℝ)| ≤ 6) :
    |a.eval v - (a.lower B.lo B.hi : ℝ)| ≤ 24 * eps := by
  have hdist (i : Fin 4) : |v i - (lowerCorner a B i : ℝ)| ≤ eps := by
    by_cases h : 0 ≤ a.coefficient i
    · simp only [lowerCorner,if_pos h]
      rw [abs_of_nonneg (sub_nonneg.mpr (hv.1 i))]
      linarith [hv.2 i,hw i]
    · simp only [lowerCorner,if_neg h]
      rw [abs_of_nonpos (sub_nonpos.mpr (hv.2 i))]
      linarith [hv.1 i,hw i]
  have heval : (a.lower B.lo B.hi : ℝ) = a.eval (fun i => (lowerCorner a B i : ℝ)) := by
    simp only [Affine.lower,Affine.eval,Rat.cast_add,Rat.cast_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : 0 ≤ a.coefficient i <;> simp [lowerCorner,h]
  rw [heval]
  have hdiff : a.eval v - a.eval (fun i => (lowerCorner a B i : ℝ)) =
      ∑ i : Fin 4, (a.coefficient i : ℝ) * (v i - (lowerCorner a B i : ℝ)) := by
    simp only [Affine.eval,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  calc
    _ ≤ ∑ i : Fin 4, |(a.coefficient i : ℝ) * (v i - (lowerCorner a B i : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, 6 * eps := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hc i) (hdist i) (abs_nonneg _) (by norm_num)
    _ = 24 * eps := by norm_num <;> ring

private theorem upper_endpoint_error (a : Affine) (B : Box) (v : LogFour) (eps : ℝ)
    (hv : v ∈ B.region) (hw : WidthLe B eps)
    (hc : ∀ i, |(a.coefficient i : ℝ)| ≤ 6) :
    |a.eval v - (a.upper B.lo B.hi : ℝ)| ≤ 24 * eps := by
  have hn : ∀ i, |(a.neg.coefficient i : ℝ)| ≤ 6 := by
    intro i
    simpa only [Affine.neg,Rat.cast_neg,abs_neg] using hc i
  have h := lower_endpoint_error a.neg B v eps hv hw hn
  rw [Affine.eval_neg] at h
  have heq : -a.eval v - (a.neg.lower B.lo B.hi : ℝ) =
      -(a.eval v + (a.neg.lower B.lo B.hi : ℝ)) := by ring
  rw [heq,abs_neg] at h
  simpa only [Affine.upper,Rat.cast_neg,sub_neg_eq_add] using h

/-- Exact separate min-cap lower endpoint, with both original tent
branches present; no correlated difference is substituted for this. -/
theorem capLower_eq_piece_min (p : Policy) (hp : p.val < 15) (B : Box) :
    capLower p B = min ((capPiece p true).lower B.lo B.hi) ((capPiece p false).lower B.lo B.hi) := by
  by_cases h0 : Selected p 0 <;> by_cases h1 : Selected p 1 <;>
    by_cases h2 : Selected p 2 <;> by_cases h3 : Selected p 3 <;>
    simp [capLower,capPiece,Affine.lower,selectedMassQ,hp,Fin.sum_univ_succ,h0,h1,h2,h3] <;>
    congr 1 <;> ring

private theorem separate_margin_positive (p : Policy) (hp : p.val < 15) (B : Box)
    (v : LogFour) (eps : ℝ) (hv : v ∈ B.region) (hw : WidthLe B eps)
    (g : Gate) (hg : Required p g)
    (hm : ∀ left : Bool, 48 * eps < (margin p left g).eval v) :
    (lhsPiece p g).upper B.lo B.hi < capLower p B := by
  rw [capLower_eq_piece_min p hp B,lt_min_iff]
  have hall (left : Bool) : (lhsPiece p g).upper B.lo B.hi < (capPiece p left).lower B.lo B.hi := by
    have hc := lower_endpoint_error (capPiece p left) B v eps hv hw (cap_coefficient_bound p left)
    have hl := upper_endpoint_error (lhsPiece p g) B v eps hv hw (lhs_coefficient_bound p g)
    have hm' := hm left
    rw [mask_margin_eq p hp left g hg,Affine.eval_sub] at hm'
    have hc' := (abs_le.mp hc).2
    have hl' := (abs_le.mp hl).1
    have hgap : ((lhsPiece p g).upper B.lo B.hi : ℝ) < ((capPiece p left).lower B.lo B.hi : ℝ) := by
      linarith
    exact_mod_cast hgap
  exact ⟨hall true,hall false⟩

/--48-width positive margins force the CONCRETE separate Boolean test
used by fixed-cell native families, not merely the correlated test. -/
theorem wholeBoxTest_of_large_actual_margins (p : Policy) (hp : p.val < 15)
    (B : Box) {v : LogFour} (eps : ℝ) (hv : v ∈ B.region) (hw : WidthLe B eps)
    (hm : ∀ g : Gate, Required p g → ∀ left : Bool, 48 * eps < (margin p left g).eval v) :
    wholeBoxEligibleTest p B = true := by
  have hhalf := separate_margin_positive p hp B v eps hv hw .half trivial (hm .half trivial)
  have hfull (j : Fin 4) := separate_margin_positive p hp B v eps hv hw (.full j) trivial (hm (.full j) trivial)
  have hselected (j : Fin 4) (hj : ¬Selected p j) :=
    separate_margin_positive p hp B v eps hv hw (.selected j) ⟨hp,hj⟩ (hm (.selected j) ⟨hp,hj⟩)
  have hel : WholeBoxEligible p B := by
    refine ⟨?_,?_,?_⟩
    · simpa [lhsPiece,halfPiece,Affine.upper,Affine.neg,Affine.lower] using hhalf
    · intro j
      exact hfull j
    · simp only [if_pos hp]
      exact hselected
  exact decide_eq_true hel

/-- Failure at a true eligible point has an actual proper-wall strip
witness. No arithmetic wall tuple is erased by Lebesgue nullity. -/
theorem eligible_failed_box_in_proper_strip (p : Policy) (hp : p.val < 15)
    (B : Box) {v : LogFour} (eps : ℝ) (hv : v ∈ B.region) (hw : WidthLe B eps)
    (he : TypedEligible p v) (hfail : wholeBoxEligibleTest p B = false) :
    ∃ g : Gate, Required p g ∧ ∃ left : Bool, wall p left g ≠ 0 ∧
      |wall p left g v - wallOffset p left g| ≤ 48 * eps := by
  have hnot : ¬∀ g : Gate, Required p g → ∀ left : Bool,
      48 * eps < (margin p left g).eval v := by
    intro hm
    have ht := wholeBoxTest_of_large_actual_margins p hp B eps hv hw hm
    rw [hfail] at ht
    cases ht
  push_neg at hnot
  obtain ⟨g,hg,left,hle⟩ := hnot
  have hpos := (typedEligible_iff_positive_margins p v).mp he g hg left
  have habs : |(margin p left g).eval v| ≤ 48 * eps := by rw [abs_of_pos hpos]; exact hle
  rw [margin_eq_actual_wall p left g hg v] at habs
  exact ⟨g,hg,left,actual_wall_ne_zero p left g hg,by simpa only [abs_sub_comm] using habs⟩

theorem grid_width (n : ℕ) (j : Grid n) :
    WidthLe (gridBox n j) (logPrimeMeshStep (lower : ℝ) (upper : ℝ) n) := by
  intro i
  rw [cast_grid_hi,cast_grid_lo,logPrimeMeshHi_eq_lo_add_step]
  linarith

def properStrips (n : ℕ) : Set LogFour := {v | ∃ p : Policy, p.val < 15 ∧
  ∃ g : Gate, Required p g ∧ ∃ left : Bool, wall p left g ≠ 0 ∧
    |wall p left g v - wallOffset p left g| ≤
      48 * logPrimeMeshStep (lower : ℝ) (upper : ℝ) n}

/-- Every true original-mask eligible cube point outside the explicit
proper strips is covered by its UNIQUE owner cell's actual native family. -/
theorem eligible_owner_active (n : ℕ) (p : Policy) (hp : p.val < 15)
    {v : LogFour} (hv : v ∈ cube) (he : TypedEligible p v) (haway : v ∉ properStrips n) :
    (⟨p.val,hp⟩,owner n v) ∈ activeCells n := by
  have hcell := owner_mem n hv
  have hbox := cell_subset_closed_box n (owner n v) hcell
  have htest : wholeBoxEligibleTest p (gridBox n (owner n v)) = true := by
    by_contra hn
    have hf : wholeBoxEligibleTest p (gridBox n (owner n v)) = false := Bool.eq_false_iff.mpr hn
    obtain ⟨g,hg,left,hproper,hstrip⟩ := eligible_failed_box_in_proper_strip p hp
      (gridBox n (owner n v)) (logPrimeMeshStep (lower : ℝ) (upper : ℝ) n)
      hbox (grid_width n (owner n v)) he hf
    exact haway ⟨p,hp,g,hg,left,hproper,hstrip⟩
  exact (mem_activeCells _).mpr htest

end
end ImbalancedChen.P5Z.U1011OriginalFifteenSeparateGridCoverage
