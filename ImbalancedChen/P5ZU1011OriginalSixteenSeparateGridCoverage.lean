import ImbalancedChen.P5ZU1011OriginalFifteenSeparateGridCoverage

/-!
The missing W16 separate-box coverage. Unlike a selected tent cap, W has
one decreasing z cap. Its required half/full/extra-A differences attain
their lower endpoint at the same upper corner as the separate cap-lower
and gate-upper test. These are literal rational circuit identities.
The x ceiling retains its own strict upper-coordinate test.

This supplies the true W wholeBoxEligibleTest from actual large margins,
and hence an actual proper-wall witness on every failed eligible W box.
The original15 supplier is reused for the resulting all16 statements.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenSeparateGridCoverage

open Set
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open P2OriginalFourthCapProducerInterface
open scoped BigOperators

noncomputable section

theorem W_margin_lower_half (B : Box) (left : Bool) :
    (margin wPolicy left .half).lower B.lo B.hi=capLower wPolicy B-1/2 := by
  cases left <;> norm_num [margin,capPiece,wPolicy,Affine.sub,Affine.lower,
    halfPiece,capLower,Fin.sum_univ_succ] <;> ring

theorem W_margin_lower_full (B : Box) (left : Bool) (j : Fin 4) :
    (margin wPolicy left (.full j)).lower B.lo B.hi=
      capLower wPolicy B-(fullSquarePiece j).upper B.lo B.hi := by
  fin_cases j <;> cases left <;>
    norm_num [margin,capPiece,wPolicy,Affine.sub,Affine.lower,Affine.upper,Affine.neg,
      fullSquarePiece,capLower,Fin.sum_univ_succ] <;> ring

theorem W_margin_lower_extra (B : Box) (left : Bool) :
    (margin wPolicy left .wExtra).lower B.lo B.hi=
      capLower wPolicy B-wExtraPiece.upper B.lo B.hi := by
  cases left <;> norm_num [margin,capPiece,wPolicy,Affine.sub,Affine.lower,Affine.upper,
    Affine.neg,wExtraPiece,capLower,Fin.sum_univ_succ] <;> ring

theorem W_margin_lower_x (B : Box) (left : Bool) :
    (margin wPolicy left .wX).lower B.lo B.hi=25/128-B.hi 0 := by
  norm_num [margin,wXSlack,Affine.lower,Fin.sum_univ_succ]
  <;> ring

/-- This is the concrete SEPARATE test used by the native W family,
not a substituted correlated certificate. -/
theorem W_wholeBoxTest_of_large_actual_margins (B : Box) {v : LogFour}
    (eps : ℝ) (hv : v∈B.region) (hw : WidthLe B eps)
    (hm : ∀ g : Gate,Required wPolicy g → ∀ left : Bool,
      48*eps<(margin wPolicy left g).eval v) :
    wholeBoxEligibleTest wPolicy B=true := by
  have heps : 0≤eps := by
    have hwidth:=hw 0
    have hlow:=hv.1 0
    have hhigh:=hv.2 0
    linarith
  have hLower (g : Gate) (hg : Required wPolicy g) (left : Bool) :
      0<(margin wPolicy left g).lower B.lo B.hi := by
    have herr:=(margin_endpoint_errors wPolicy left g B eps hv hw).1
    have hdiff:=(abs_le.mp herr).2
    have hmargin:=hm g hg left
    have hR : (0:ℝ)<((margin wPolicy left g).lower B.lo B.hi:ℝ) := by linarith
    exact_mod_cast hR
  have hhalf:=hLower .half trivial true
  have hfull (j : Fin 4):=hLower (.full j) trivial true
  have hreq : ¬wPolicy.val<15 := by norm_num [wPolicy]
  have hextra:=hLower .wExtra hreq true
  have hx:=hLower .wX hreq true
  rw [W_margin_lower_half] at hhalf
  simp only [W_margin_lower_full] at hfull
  rw [W_margin_lower_extra] at hextra
  rw [W_margin_lower_x] at hx
  have hwhole : WholeBoxEligible wPolicy B := by
    refine ⟨by linarith,fun j=>by have h:=hfull j;linarith,?_⟩
    simp only [if_neg hreq]
    exact ⟨by linarith,by linarith⟩
  exact decide_eq_true hwhole

/-- Every original policy now uses the SAME real48-width margin premise
and the SAME concrete separate whole-box Boolean test. -/
theorem all_sixteen_wholeBoxTest_of_large_actual_margins (p : Policy)
    (B : Box) {v : LogFour} (eps : ℝ) (hv : v∈B.region) (hw : WidthLe B eps)
    (hm : ∀ g : Gate,Required p g → ∀ left : Bool,48*eps<(margin p left g).eval v) :
    wholeBoxEligibleTest p B=true := by
  by_cases hp : p.val<15
  · exact U1011OriginalFifteenSeparateGridCoverage.wholeBoxTest_of_large_actual_margins
      p hp B eps hv hw hm
  · have hpW : p=wPolicy := by
      apply Fin.ext
      have hp16:=p.isLt
      dsimp [wPolicy]
      omega
    subst p
    exact W_wholeBoxTest_of_large_actual_margins B eps hv hw hm

/-- A failed actual test at a genuinely eligible point has a genuine
required original wall witness, including W16 and all endpoint equalities. -/
theorem all_sixteen_eligible_failed_box_in_proper_strip (p : Policy)
    (B : Box) {v : LogFour} (eps : ℝ) (hv : v∈B.region) (hw : WidthLe B eps)
    (he : TypedEligible p v) (hfail : wholeBoxEligibleTest p B=false) :
    ∃ g : Gate,Required p g ∧ ∃ left : Bool,wall p left g≠0 ∧
      |wall p left g v-wallOffset p left g|≤48*eps := by
  have hn : ¬∀ g : Gate,Required p g → ∀ left : Bool,48*eps<(margin p left g).eval v := by
    intro hm
    have ht:=all_sixteen_wholeBoxTest_of_large_actual_margins p B eps hv hw hm
    rw [hfail] at ht
    cases ht
  push_neg at hn
  obtain ⟨g,hg,left,hle⟩:=hn
  have hpos:=(typedEligible_iff_positive_margins p v).mp he g hg left
  have habs : |(margin p left g).eval v|≤48*eps := by rw [abs_of_pos hpos];exact hle
  rw [margin_eq_actual_wall p left g hg v] at habs
  exact ⟨g,hg,left,actual_wall_ne_zero p left g hg,by simpa only [abs_sub_comm] using habs⟩

end

end ImbalancedChen.P5Z.U1011OriginalSixteenSeparateGridCoverage
