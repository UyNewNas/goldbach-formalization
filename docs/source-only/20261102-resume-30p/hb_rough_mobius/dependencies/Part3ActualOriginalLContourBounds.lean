import ImbalancedChen.Part3ActualRoughAsymmetricContour

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual original-character L and reciprocal bounds. Genuine primitive
Siegel/induction nonvanishing from21 is consumed inside the proof. The
conductor-log value bound is discharged on the complete anchor disk.
A constructed holomorphic logarithm and the primary small-disk derivative
estimate, integrated over a path of length<=delta, give the explicit
reciprocal cost (4/delta)*(128D/delta)^40. D is logarithmic in the ORIGINAL
modulus and enlarged finite height. No hzero/unknown left norm is public.
-/

namespace ImbalancedChen.Part3.ActualOriginalLContourBounds20261026b
noncomputable section
open Classical Complex Metric Set
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaZeroContribution
open DirichletLGlobalConductorLogValueBound
open RoughQuadraticLowRectangle20261026b
open ActualRoughContourHolomorphic20261026b

def originalReciprocalCost (q : ℕ) (H δ : ℝ) : ℝ :=
  Real.exp (40*Real.log (128*rectangleLog q H/δ)-Real.log (δ/4))

private theorem norm_L_on_disk {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) {H δ t : ℝ}
    (hδ : 0<δ) (hδ1 : δ≤1/4) (hsmall : δ≤1/rectangleLog q H)
    (ht : |t|≤H) {w : ℂ}
    (hw : w∈ball ((1+δ/2 : ℝ)+I*t) (3*δ/2)) :
    ‖χ.LFunction w‖≤32*rectangleLog q H := by
  obtain ⟨hwlo,hwhi,hwim⟩ := Eq21FiniteLogDerivative.anchor_disk_subset_rectangle hδ hδ1 ht hw
  have hlog:=heightLog_le_rectangleLog χ hχ hwim
  have hlogpos:=log_conductorHeightCutoff_pos χ hχ w.im
  have hinv : 1/rectangleLog q H≤1/Real.log (dirichletLConductorHeightCutoff q w.im) :=
    one_div_le_one_div_of_le hlogpos (by linarith)
  have hv:=norm_LFunction_le_thirtytwo_mul_one_add_log_conductorHeightCutoff χ hχ
    (by linarith : 1/2≤w.re) hwhi (by linarith [hsmall.trans hinv])
  have hrepr : (w.re : ℂ)+I*w.im=w := by simpa only [mul_comm I] using w.re_add_im
  rw [hrepr] at hv
  exact hv.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

/-- Constants precede every original modulus, character, height, strip
width and moving evaluation point. All nonvanishing inputs are supplied
by the genuine primitive theorem and quantitative induction. -/
theorem exists_actual_original_L_contour_bounds (η : ℝ) (hη : 0<η) :
    ∃ c A : ℝ,0<c ∧ 0<A ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q),χ≠1 → ∀ (H δ β t : ℝ),
      0≤H → 0<δ → δ≤conductorWidth c A η χ H →
      δ≤1/rectangleLog q H → |t|≤H → 1-δ/2≤β → β≤1+δ →
      ‖χ.LFunction ((β : ℂ)+I*t)‖≤32*rectangleLog q H ∧
      ‖(χ.LFunction ((β : ℂ)+I*t))⁻¹‖≤originalReciprocalCost q H δ := by
  obtain ⟨c,A,hc,hA,hzero⟩:=exists_original_contour_zero_free η hη
  refine ⟨c,A,hc,hA,?_⟩
  intro q _ χ hχ H δ β t hH hδ hwidth hsmall ht hβlo hβhi
  have hδ1 : δ≤1/4:=hwidth.trans (conductorWidth_le_quarter c A η χ H)
  let a : ℂ:=(1+δ/2 : ℝ)+I*t
  let z : ℂ:=(β : ℂ)+I*t
  let b : ℝ:=δ/4
  let B : ℝ:=32*rectangleLog q H
  have hb : 0<b:=by dsimp [b]; positivity
  have hD:=one_le_rectangleLog q H
  have hbB : b<B:=by dsimp [b,B]; linarith
  have hB : 0<B:=hb.trans hbB
  have hR : 0<3*δ/2:=by positivity
  have ha : a∈ball a (3*δ/2):=mem_ball_self hR
  have hzdist : dist z a≤δ:=by
    dsimp [z,a]
    rw [dist_add_right,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hzmem : z∈ball a (3*δ/2):=mem_ball.mpr (hzdist.trans_lt (by linarith))
  have hzeroDisk : ∀ w∈ball a (3*δ/2),χ.LFunction w≠0:=by
    intro w hw
    obtain ⟨hwlo,hwhi,hwim⟩:=Eq21FiniteLogDerivative.anchor_disk_subset_rectangle hδ hδ1 ht hw
    exact hzero q χ hχ H hH w (by linarith) hwhi hwim
  have hbound : ∀ w∈ball a (3*δ/2),‖χ.LFunction w‖≤B:=
    fun w hw=>norm_L_on_disk χ hχ hδ hδ1 hsmall ht hw
  have hanchor : b≤‖χ.LFunction a‖:=Eq21LocalLog.delta_quarter_le_norm_LFunction_anchor χ hδ hδ1 t
  obtain ⟨h,hh,hexp⟩:=exists_holomorphicLog_on_ball χ.LFunction a hR
    (χ.differentiable_LFunction hχ).differentiableOn hzeroDisk
  have hre : ∀ w∈ball a (3*δ/2),(h w).re=Real.log ‖χ.LFunction w‖:=by
    intro w hw
    rw [← hexp hw,Complex.norm_exp,Real.log_exp]
  let E:=Real.log (B/b)
  have hE : 0<E:=Real.log_pos ((one_lt_div hb).2 hbB)
  have hosc : ∀ w∈ball a (3*δ/2),(h w).re-(h a).re≤E:=by
    intro w hw
    rw [hre w hw,hre a ha]
    dsimp only [E]
    rw [Real.log_div hB.ne' hb.ne']
    exact sub_le_sub (Real.log_le_log (norm_pos_iff.mpr (hzeroDisk w hw)) (hbound w hw))
      (Real.log_le_log hb hanchor)
  have hsegment : segment ℝ a z⊆closedBall a δ:=
    (convex_closedBall a δ).segment_subset (mem_closedBall_self hδ.le) (mem_closedBall.mpr hzdist)
  have hlogdiff : ‖h z-h a‖≤40*E:=by
    have hmain : ‖h z-h a‖≤(40*E/δ)*‖z-a‖:=
      (convex_segment (𝕜:=ℝ) a z).norm_image_sub_le_of_norm_fderiv_le
        (𝕜:=ℂ) (f:=h) (C:=40*E/δ)
        (fun w hw=>by
          have hd:=mem_closedBall.mp (hsegment hw)
          have hm : w∈ball a (3*δ/2):=mem_ball.mpr (hd.trans_lt (by linarith))
          exact (hh w hm).differentiableAt (isOpen_ball.mem_nhds hm))
        (fun w hw=>by
          rw [← norm_deriv_eq_norm_fderiv]
          exact Eq21LocalLog.norm_deriv_le_small_disk h a w hδ hE hh hosc
            (mem_closedBall.mp (hsegment hw)))
        (left_mem_segment ℝ a z) (right_mem_segment ℝ a z)
    have hn : ‖z-a‖≤δ:=by simpa only [dist_eq_norm] using hzdist
    exact hmain.trans ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq
      (by field_simp [hδ.ne']))
  have hreAnchor : Real.log b≤(h a).re:=by
    rw [hre a ha]
    exact Real.log_le_log hb hanchor
  have hreDiff : (h a).re-(h z).re≤40*E:=by
    have hRe:=(abs_le.mp (Complex.abs_re_le_norm (h z-h a))).1
    simp only [sub_re] at hRe
    linarith
  refine ⟨hbound z hzmem,?_⟩
  have hinv : ‖(χ.LFunction z)⁻¹‖=Real.exp (-(h z).re):=by
    rw [← hexp hzmem,norm_inv,Complex.norm_exp,Real.exp_neg]
  rw [hinv]
  unfold originalReciprocalCost
  have heq : 40*E-Real.log b=
      40*Real.log (128*rectangleLog q H/δ)-Real.log (δ/4):=by
    dsimp only [E,B,b]
    congr 2
    field_simp
    ring
  rw [← heq]
  exact Real.exp_le_exp.mpr (by linarith)

end
end ImbalancedChen.Part3.ActualOriginalLContourBounds20261026b
