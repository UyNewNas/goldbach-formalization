import ImbalancedChen.Part3ActualRoughSmoothedContourBudget
import ImbalancedChen.Part3ActualConductorWidthThreshold
import ImbalancedChen.Part3ActualRoughAsymmetricParameters
import ImbalancedChen.Part3ActualRoughAmplitudePayment

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- Genuine zero-cutoff specialization of the archived actual contour budget.
-- Adapted from 20261027-RoughSW-PerronContour's smoothed source: its final
-- theorem fixes roughZ x, so importing that conclusion cannot give mu.
-- Here only the cutoff is changed to zero. The actual generic Perron budget
-- is reused; its amplitude and Euler-width gates are proved below at zero.
-- The old fixed-cutoff source and all dependencies remain frozen/held.
-- No character cancellation or desired log saving is a hypothesis.

namespace ImbalancedChen.Part3.UnroughMobiusSmoothed20261102
noncomputable section
open Classical Complex Set MeasureTheory Filter Topology
open ActualRoughSmoothedContourBudget20261027
open ActualRoughContourHolomorphic20261026b
open ActualRoughContourIntegrandBounds20261026b
open ActualConductorWidthThreshold20261026b
open ActualRoughContourParameters20261026b
open ActualRoughAsymmetricParameters20261026b
open ActualRoughAmplitudePayment20261026b
open RoughSlotSmoothedPerron20261026b

private theorem scalar_horizontal_payment
    {A M C K P X x s : ℝ} (hlog : 2 ≤ Real.log x)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hP : 0 ≤ P) (hX : 0 ≤ X)
    (hs : s ≤ 1) (hPs : P ≤ K*(1+Real.log x)^M)
    (hexp : M-2*C ≤ -A) :
    P*Real.exp 1*X*s/(Real.pi*(contourT C x)^2) ≤
      (K*2^M*Real.exp 1/Real.pi)*X*(Real.log x)^(-A) := by
  let l := Real.log x
  have hl : 1 ≤ l := by dsimp [l]; linarith
  have hlp : 0 < l := zero_lt_one.trans_le hl
  have hW : (1+Real.log x)^M ≤ 2^M*l^M := by
    calc
      _ ≤ (2*l)^M := Real.rpow_le_rpow (by dsimp [l]; linarith)
        (by dsimp [l]; linarith) hM
      _ = _ := Real.mul_rpow (by norm_num) hlp.le
  have hP' : P ≤ (K*2^M)*l^M := by
    exact hPs.trans ((mul_le_mul_of_nonneg_left hW hK).trans_eq (by ring))
  have hT : (contourT C x)^2 = l^(2*C) := by
    dsimp [contourT,l]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlp.le]
    congr 1
    ring
  have hnum : P*Real.exp 1*X*s ≤ ((K*2^M)*l^M)*Real.exp 1*X := by
    calc
      _ ≤ P*Real.exp 1*X := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hs
          (mul_nonneg (mul_nonneg hP (Real.exp_pos 1).le) hX)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hP' (Real.exp_pos 1).le) hX
  calc
    _ ≤ (((K*2^M)*l^M)*Real.exp 1*X)/(Real.pi*l^(2*C)) := by
      rw [hT]
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ = (K*2^M*Real.exp 1/Real.pi)*X*l^(M-2*C) := by
      rw [Real.rpow_sub hlp]
      field_simp [Real.pi_ne_zero,(Real.rpow_pos_of_pos hlp (2*C)).ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hl hexp) (by positivity)

private theorem scalar_tail_payment
    {A R C Ctail X x : ℝ} (hlog : 2 ≤ Real.log x) (hR : 0 ≤ R)
    (hCtail : 0 ≤ Ctail) (hX : 1 < X) (hXx : X ≤ x)
    (hexp : 1+R-C ≤ -A) :
    Real.exp 1*(1+1/rightOffset X)*X*(Ctail/((Real.log x)^(-R)))/
        (Real.pi*contourT C x) ≤
      (2*Real.exp 1*Ctail/Real.pi)*X*(Real.log x)^(-A) := by
  let l := Real.log x
  have hl : 1 ≤ l := by dsimp [l]; linarith
  have hlp : 0 < l := zero_lt_one.trans_le hl
  have hlogX : Real.log X ≤ l := Real.log_le_log (by linarith) hXx
  have hfactor : 1+1/rightOffset X ≤ 2*l := by
    simp only [rightOffset,one_div,inv_inv]
    linarith
  have heps : Ctail/((Real.log x)^(-R)) = Ctail*l^R := by
    rw [Real.rpow_neg hlp.le]
    simp [l,div_eq_mul_inv]
  have hnum : Real.exp 1*(1+1/rightOffset X)*X*(Ctail*l^R) ≤
      Real.exp 1*(2*l)*X*(Ctail*l^R) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor (Real.exp_pos 1).le)
        (by linarith)) (by positivity)
  rw [heps]
  calc
    _ ≤ (Real.exp 1*(2*l)*X*(Ctail*l^R))/(Real.pi*l^C) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (2*Real.exp 1*Ctail/Real.pi)*X*l^(1+R-C) := by
      rw [Real.rpow_sub hlp,Real.rpow_add hlp,Real.rpow_one]
      field_simp [Real.pi_ne_zero,(Real.rpow_pos_of_pos hlp C).ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hl hexp) (by positivity)

-- All constants and the real threshold precede q, the original character,
-- Mellin frequency, normalization U and interval scale X. The zero cutoff
-- removes every rough exclusion; the Mobius sign is retained literally.
theorem exists_actual_smoothed_unrough_character_SW
    (A B L R θ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hR : 0 < R) (hθ : 0 < θ)
    (ν : ℝ → ℝ) (hν : ContDiff ℝ 1 ν) (hnonneg : ∀ t > 0, 0 ≤ ν t)
    (hsupp : Function.support ν ⊆ Icc (1/2) 2)
    (hmass : (∫ t in Ioi (0 : ℝ), ν t/t) = 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x : ℝ, x0 ≤ x → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ (Real.log x)^B →
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (useMu : Bool) (τ U X : ℝ), |τ| ≤ (Real.log x)^L →
      0 < U → x^θ ≤ X → X ≤ x →
      ‖∑ n ∈ smoothCarrier ν ((Real.log x)^(-R)) X,
        coefficient useMu χ 0 τ U n *
          Smooth1 ν ((Real.log x)^(-R)) (n/X)‖ ≤ K*X*(Real.log x)^(-A) := by
  let η := 1/(28*(B+1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hgap : 14*B*η < 1 := by
    dsimp [η]
    have hden : 0 < 28*(B+1) := by positivity
    have hh : (14*B)/(28*(B+1)) < 1 := (div_lt_one₀ hden).mpr (by nlinarith)
    simpa only [div_eq_mul_inv] using hh
  obtain ⟨c₁,A₁,c₂,A₂,E,hc₁,hA₁,hc₂,hA₂,hE,hbudget⟩ :=
    exists_actual_rough_smoothed_contour_budget η hη
  obtain ⟨Ctail,Cedge,hCtail,hCedge,hbound⟩ := hbudget ν hν hnonneg hsupp hmass
  let C := A+R+L+100
  let M := R+82
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hLC : L ≤ C := by dsimp [C]; linarith
  have hM : 0 ≤ M := by dsimp [M]; linarith
  obtain ⟨Kamp,hKamp,xamp,hxamp,hamp⟩ :=
    exists_actual_contour_amplitude_threshold E Cedge B C L R 1 1
      hE hCedge hB hC hL hLC hR.le (by norm_num)
  obtain ⟨xw₁,hxw₁,hw₁⟩ := exists_actual_conductor_width_threshold
    c₁ A₁ η 1 B C L hc₁ hA₁ hη (by norm_num) hB hC hLC hgap
  obtain ⟨xw₂,hxw₂,hw₂⟩ := exists_actual_conductor_width_threshold
    c₂ A₂ η 1 B C L hc₂ hA₂ hη (by norm_num) hB hC hLC hgap
  obtain ⟨xa,hxa,ha⟩ := exists_actual_asymmetric_threshold 1 θ A M
    (by norm_num) hθ hA hM
  let K := Kamp + Kamp*2^M*Real.exp 1/Real.pi + 2*Real.exp 1*Ctail/Real.pi
  have hK : 0 < K := by dsimp [K]; positivity
  have hevent : ∀ᶠ x : ℝ in atTop,
      xamp ≤ x ∧ xw₁ ≤ x ∧ xw₂ ≤ x ∧ xa ≤ x ∧ 2 ≤ Real.log x := by
    filter_upwards [eventually_ge_atTop xamp,eventually_ge_atTop xw₁,
      eventually_ge_atTop xw₂,eventually_ge_atTop xa,
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))]
      with x h1 h2 h3 h4 h5
    exact ⟨h1,h2,h3,h4,h5⟩
  obtain ⟨r,hr⟩ := eventually_atTop.mp hevent
  refine ⟨K,hK,max r 2,lt_of_lt_of_le (by norm_num : (1 : ℝ)<2) (le_max_right _ _),?_⟩
  intro x hx q _ hq χ hχ useMu τ U X hτ hU hXlo hXhi
  have hg := hr x ((le_max_left _ _).trans hx)
  have hlog : 2 ≤ Real.log x := hg.2.2.2.2
  have hlogpos : 0 < Real.log x := by linarith
  have hwidth₁ := hw₁ x hg.2.1
  have hwidth₂ := hw₂ x hg.2.2.1
  have hwa := hwidth₁.2.2.2 q hq χ τ hτ
  have hwb := hwidth₂.2.2.2 q hq χ τ hτ
  have hscalar := ha x hg.2.2.2.1 X hXlo
  have hXpos : 0 < X := by linarith [hscalar.1]
  have hε : 0 < (Real.log x)^(-R) := Real.rpow_pos_of_pos hlogpos _
  have hε1 : (Real.log x)^(-R) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hT : 0 < contourT C x := Real.rpow_pos_of_pos hlogpos _
  have hz : (0 : ℝ) ≤ 0 := le_rfl
  have hδ := hwidth₁.1
  have hδquarter : roughDelta 1 x ≤ 1/4 :=
    hwa.1.trans (conductorWidth_le_quarter c₁ A₁ η χ (contourT C x+|τ|))
  have hshape : roughDelta 1 x/2+rightOffset X ≤ 1 := by linarith [hscalar.2.2.1]
  let P := contourAmplitude E Cedge q (contourT C x+|τ|) (roughDelta 1 x) 1
    0 ((Real.log x)^(-R))
  have hlogcut : Real.log (max 2 (0 : ℝ)) ≤ Real.log (max 2 (roughZ x)) := by
    apply Real.log_le_log
    · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
    · exact max_le (le_max_left _ _)
        (le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _))
  have hPbound : P ≤ Kamp*(1+Real.log x)^M := by
    refine le_trans ?_ (hamp x hg.1 q inferInstance hq τ hτ)
    dsimp only [P,contourAmplitude]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hCedge.le hε.le)
    apply mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (add_le_add_left hlogcut 1)
        (mul_nonneg (RoughThinEulerUniformComparison20261026b.thinComparison_pos 1).le hE.le))
    have hD := RoughQuadraticLowRectangle20261026b.one_le_rectangleLog q (contourT C x+|τ|)
    dsimp [ActualOriginalLContourBounds20261026b.originalReciprocalCost]
    positivity
  have hP : 0 ≤ P := by
    dsimp [P,contourAmplitude,ActualOriginalLContourBounds20261026b.originalReciprocalCost]
    have hD := RoughQuadraticLowRectangle20261026b.one_le_rectangleLog q (contourT C x+|τ|)
    have hthin := RoughThinEulerUniformComparison20261026b.thinComparison_pos (1 : ℝ)
    have hlogz : 0 ≤ Real.log (max 2 (0 : ℝ)) :=
      Real.log_nonneg ((by norm_num : (1 : ℝ)≤2).trans (le_max_left _ _))
    positivity
  have hcap0 : roughDelta 1 x*Real.log (max 2 (0 : ℝ)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hlogcut hδ.le).trans_eq hwidth₁.2.2.1
  have hraw := hbound q χ hχ useMu 0 τ U (contourT C x) X
    ((Real.log x)^(-R)) (roughDelta 1 x) 1 (rightOffset X)
    hz hU hT (by linarith [hscalar.1]) hε hε1 hδ (by norm_num)
    hwa.1 hwb.1 hwb.2 hcap0
    hscalar.2.1 hscalar.2.2.1 (le_of_eq hscalar.2.2.2.1)
  have hleft : P*X^(1-roughDelta 1 x/2) ≤ Kamp*X*(Real.log x)^(-A) := by
    calc
      _ ≤ (Kamp*(1+Real.log x)^M)*X^(1-roughDelta 1 x/2) :=
        mul_le_mul_of_nonneg_right hPbound (Real.rpow_nonneg hXpos.le _)
      _ = Kamp*X*(X^(-(roughDelta 1 x)/2)*(1+Real.log x)^M) := by
        have he : 1-roughDelta 1 x/2 = 1+(-(roughDelta 1 x)/2) := by ring
        rw [he,Real.rpow_add hXpos,Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscalar.2.2.2.2.2 (by positivity)
  have hhorizontal := scalar_horizontal_payment hlog hM hKamp.le hP hXpos.le hshape hPbound
    (show M-2*C ≤ -A by dsimp [M,C]; linarith)
  have htail := scalar_tail_payment hlog hR.le hCtail.le hscalar.1 hXhi
    (show 1+R-C ≤ -A by dsimp [C]; linarith)
  apply hraw.trans
  calc
    _ ≤ Kamp*X*(Real.log x)^(-A) +
        (Kamp*2^M*Real.exp 1/Real.pi)*X*(Real.log x)^(-A) +
        (2*Real.exp 1*Ctail/Real.pi)*X*(Real.log x)^(-A) :=
      add_le_add (add_le_add hleft hhorizontal) htail
    _ = _ := by dsimp [K]; ring

end
end ImbalancedChen.Part3.UnroughMobiusSmoothed20261102
