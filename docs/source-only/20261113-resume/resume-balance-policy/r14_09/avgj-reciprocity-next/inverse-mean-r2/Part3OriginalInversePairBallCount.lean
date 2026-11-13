import ImbalancedChen.Part3OriginalInversePairFibres

/-! Sum the nonzero and parabolic lower-left-entry fibres in a two-point
hyperbolic ball. The two reduced heights may be different. -/
namespace ImbalancedChen.Part3.OriginalInversePairBallCount20261113
noncomputable section
open Finset Matrix
open scoped MatrixGroups UpperHalfPlane BigOperators
open OriginalInversePairDisplacement20261113 OriginalInversePairFibres20261113

private theorem signed_card (S : Finset (SL(2,ℤ))) (z w : ℍ) (hz : 1/2≤z.im) (hw : 1/2≤w.im)
    (order : z.im≤w.im) {R : ℝ} (hR : 1≤R) (s : Bool)
    (sgn : ∀ g ∈ S, 0<(if s then -(g 1 0) else g 1 0))
    (hball : ∀ g ∈ S, 2*Real.cosh (dist (g • z) w)≤R^2) :
    (S.card:ℝ) ≤ 20*R^2*(1+Real.log (1+2*R)) := by
  have hR0 : 0<R := by linarith
  let P := Real.sqrt (z.im*w.im)
  have hP : 0<P := Real.sqrt_pos.mpr (mul_pos z.im_pos w.im_pos)
  have sq : P^2=z.im*w.im := Real.sq_sqrt (mul_pos z.im_pos w.im_pos).le
  have lo : 1/2 ≤ P := by
    apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤1/2) hP.le).mp
    rw [sq]
    nlinarith only [mul_le_mul hz hw (by norm_num : (0:ℝ)≤1/2) z.im_pos.le]
  have Pz : z.im ≤ P := by
    apply (sq_le_sq₀ z.im_pos.le hP.le).mp
    rw [sq,pow_two]
    exact mul_le_mul_of_nonneg_left order z.im_pos.le
  have Pw : P ≤ w.im := by
    apply (sq_le_sq₀ hP.le w.im_pos.le).mp
    rw [sq,pow_two]
    exact mul_le_mul_of_nonneg_right order w.im_pos.le
  let H := ⌊R/P⌋₊
  let A := R*P/z.im
  let D := R*P/w.im
  have hA : 0≤A := by dsimp [A]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have entry {x : ℝ} (hx : x^2 ≤ R^2*(z.im*w.im)) : |x| ≤ R*P := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_pos hR0 hP).le).mp
    simpa only [sq_abs,mul_pow,sq] using hx
  have cert (g) (hg : g∈S) := reduced_entries g z w (hball g hg)
  have Hc (g) (hg : g∈S) : (g 1 0).natAbs≤H := by
    apply Nat.le_floor
    apply (le_div_iff₀ hP).mpr
    have h := entry (cert g hg).1
    rw [abs_mul,abs_mul,abs_of_pos z.im_pos,abs_of_pos w.im_pos, mul_assoc,← sq] at h
    have h' : |(g 1 0:ℝ)|*P ≤ R := (mul_le_mul_iff_left₀ hP).mp (by nlinarith only [h])
    simpa only [← Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast] using h'
  have Ha (g) (hg : g∈S) : |(g 0 0:ℝ)-w.re*(g 1 0:ℝ)|≤A := by
    apply (le_div_iff₀ z.im_pos).mpr
    simpa only [abs_mul,abs_of_pos z.im_pos,mul_comm z.im] using entry (cert g hg).2.2.1
  have Hd (g) (hg : g∈S) : |(g 1 1:ℝ)-(-(g 1 0:ℝ)*z.re)|≤D := by
    apply (le_div_iff₀ w.im_pos).mpr
    simpa only [neg_mul,sub_neg_eq_add,add_comm (g 1 1:ℝ),abs_mul,abs_of_pos w.im_pos,
      mul_comm w.im] using entry (cert g hg).2.1
  have f := signed_fibres S s H hA hD (fun c => w.re*(c:ℝ)) (fun c => -(c:ℝ)*z.re)
    sgn Hc Ha Hd
  by_cases hzero : S=∅
  · rw [hzero,card_empty,Nat.cast_zero]
    have hl := Real.log_nonneg (by linarith : 1≤1+2*R)
    positivity
  · obtain ⟨g,hg⟩ := nonempty_iff_ne_empty.mpr hzero
    have ne : g 1 0≠0 := by intro he; have e := sgn g hg; simp [he] at e
    have Hpos : 0<H := (Int.natAbs_pos.mpr ne).trans_le (Hc g hg)
    have Hreal : (H:ℝ)≤R/P := Nat.floor_le (div_pos hR0 hP).le
    have P_le : P≤R := by
      have one : (1:ℝ)≤H := by exact_mod_cast Hpos
      simpa only [one_mul] using (le_div_iff₀ hP).mp (one.trans Hreal)
    have Hcap : (H:ℝ)≤2*R := Hreal.trans ((div_le_iff₀ hP).mpr (by nlinarith [mul_le_mul_of_nonneg_left lo hR0.le]))
    have L : 0≤Real.log (1+2*R) := Real.log_nonneg (by linarith)
    have HH : (harmonic H:ℝ)≤1+Real.log (1+2*R) :=
      (harmonic_le_one_add_log H).trans (add_le_add le_rfl
        (Real.log_le_log (by exact_mod_cast Hpos) (by linarith only [Hcap])))
    have HH0 : 0≤(harmonic H:ℝ) := by
      rw [← IntervalHarmonicPairBoundSourceOnly.real_reciprocal_sum_eq_harmonic]
      positivity
    have Dcap : D≤R := (div_le_iff₀ w.im_pos).mpr (mul_le_mul_of_nonneg_left Pw hR0.le)
    have Acap : A≤2*R^2 := (div_le_iff₀ z.im_pos).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left P_le hR0.le,
        mul_le_mul_of_nonneg_left hz (sq_nonneg R)])
    have AD : D*A=R^2 := by
      dsimp [D,A]
      field_simp [z.im_ne_zero,w.im_ne_zero]
      linear_combination R^2*sq
    have P1 : (1+2*D)*(H:ℝ)≤6*R^2 := calc
      _ ≤ (1+2*R)*(2*R) := mul_le_mul (by linarith) Hcap (Nat.cast_nonneg H) (by positivity)
      _ ≤ _ := by nlinarith only [mul_nonneg hR0.le (sub_nonneg.mpr hR)]
    have P2 : (1+2*D)*(2*A) ≤ 8*R^2 := by nlinarith only [AD,Acap]
    apply f.trans
    calc
      _ = (1+2*D)*(H:ℝ)+((1+2*D)*(2*A))*(harmonic H:ℝ) := by ring
      _ ≤ 6*R^2+(8*R^2)*(1+Real.log (1+2*R)) :=
        add_le_add P1 (mul_le_mul P2 HH HH0 (by positivity))
      _ ≤ _ := by nlinarith only [mul_nonneg (sq_nonneg R) L,sq_nonneg R]

private theorem parabolic_card (S : Finset (SL(2,ℤ))) (z w : ℍ) {R : ℝ} (hR : 0≤R)
    (hc : ∀ g ∈ S, g 1 0=0) (e : ℤ) (he : e=1 ∨ e= -1) (hd : ∀ g ∈ S, g 1 1=e)
    (hball : ∀ g ∈ S, 2*Real.cosh (dist (g • z) w)≤R^2) :
    (S.card:ℝ) ≤ 1+2*(R*Real.sqrt (z.im*w.im)) := by
  let P := Real.sqrt (z.im*w.im)
  have hp : 0<P := Real.sqrt_pos.mpr (mul_pos z.im_pos w.im_pos)
  have sq : P^2=z.im*w.im := Real.sq_sqrt (mul_pos z.im_pos w.im_pos).le
  apply parabolic_fibre S he hc hd ((w.re-z.re)*(e:ℝ)) (mul_nonneg hR hp.le)
  intro g hg
  have ha : g 0 0=e := by
    have H : g 0 0*e=1 := by simpa [Matrix.det_fin_two,hc g hg,hd g hg] using g.det_coe
    rcases he with he|he
    · simpa [he] using H
    · rw [he,mul_neg_one] at H
      omega
  have H := (reduced_entries g z w (hball g hg)).2.2.2
  rw [ha,hc g hg,hd g hg,Int.cast_zero,zero_mul,zero_add] at H
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hR hp.le)).mp
  rw [sq_abs,mul_pow,sq]
  nlinarith only [H]

private theorem ordered_card (S : Finset (SL(2,ℤ))) (z w : ℍ) (hz : 1/2≤z.im) (hw : 1/2≤w.im)
    (order : z.im≤w.im) {R : ℝ} (hR : 1≤R)
    (hball : ∀ g ∈ S, 2*Real.cosh (dist (g • z) w)≤R^2) :
    (S.card:ℝ) ≤ 40*R^2*(1+Real.log (1+2*R))+2+4*R*Real.sqrt (z.im*w.im) := by
  classical
  let Z := S.filter (fun g => g 1 0=0)
  let N := S.filter (fun g => ¬g 1 0=0)
  let P := N.filter (fun g => 0<g 1 0)
  let M := N.filter (fun g => ¬0<g 1 0)
  let U := Z.filter (fun g => g 1 1=1)
  let V := Z.filter (fun g => ¬g 1 1=1)
  have hz' : ∀ g ∈ Z, g 1 0=0 := fun _ hg => (mem_filter.mp hg).2
  have hv (g) (hg : g∈V) : g 1 1= -1 := by
    have H : g 0 0*g 1 1=1 := by
      simpa [Matrix.det_fin_two,hz' g (mem_filter.mp hg).1] using g.det_coe
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' H with h|h
    · exact False.elim ((mem_filter.mp hg).2 h.2)
    · exact h.2
  have subset (T : Finset (SL(2,ℤ))) (p q : SL(2,ℤ) → Prop) [DecidablePred p] [DecidablePred q] :
      (T.filter p).filter q ⊆ T := (filter_subset _ _).trans (filter_subset _ _)
  have BP := signed_card P z w hz hw order hR false (fun g hg => (mem_filter.mp hg).2)
    (fun g hg => hball _ (subset S _ _ hg))
  have BM := signed_card M z w hz hw order hR true (by
    intro g hg
    have h := (mem_filter.mp hg).2
    have e := (mem_filter.mp (mem_filter.mp hg).1).2
    change 0 < -(g 1 0)
    omega) (fun g hg => hball _ (subset S _ _ hg))
  have BU := parabolic_card U z w (zero_le_one.trans hR)
    (fun g hg => hz' g (mem_filter.mp hg).1) 1 (Or.inl rfl) (fun _ hg => (mem_filter.mp hg).2)
    (fun g hg => hball _ (subset S _ _ hg))
  have BV := parabolic_card V z w (zero_le_one.trans hR)
    (fun g hg => hz' g (mem_filter.mp hg).1) (-1) (Or.inr rfl) hv
    (fun g hg => hball _ (subset S _ _ hg))
  have split (T : Finset (SL(2,ℤ))) (p : SL(2,ℤ) → Prop) [DecidablePred p] :
      ((T.filter p).card:ℝ)+((T.filter (fun t => ¬p t)).card:ℝ) = (T.card:ℝ) := by
    exact_mod_cast card_filter_add_card_filter_not (s := T) p
  have s₀ : (Z.card:ℝ)+(N.card:ℝ)=(S.card:ℝ) := split S _
  have s₁ : (P.card:ℝ)+(M.card:ℝ)=(N.card:ℝ) := split N _
  have s₂ : (U.card:ℝ)+(V.card:ℝ)=(Z.card:ℝ) := split Z _
  linarith only [BP,BM,BU,BV,s₀,s₁,s₂]

/-- Uniform two-point ball count. Exchanging the two reduced points inverts
every matrix, so the larger of the two column budgets pays the harmonic
progression and the smaller budget counts consecutive integers. -/
theorem ball_card (S : Finset (SL(2,ℤ))) (z w : ℍ) (hz : 1/2≤z.im) (hw : 1/2≤w.im)
    {R : ℝ} (hR : 1≤R) (hball : ∀ g ∈ S, 2*Real.cosh (dist (g • z) w)≤R^2) :
    (S.card:ℝ) ≤ 40*R^2*(1+Real.log (1+2*R))+2+4*R*Real.sqrt (z.im*w.im) := by
  classical
  rcases le_total z.im w.im with h|h
  · exact ordered_card S z w hz hw h hR hball
  · have rev (g : SL(2,ℤ)) : dist (g⁻¹ • w) z = dist (g • z) w := calc
      _ = dist (g⁻¹ • w) (g⁻¹ • (g • z)) := by rw [inv_smul_smul]
      _ = dist w (g • z) := by
        rw [←Gamma0GeneralCuspUnitPeriod20261025a.integralReal_smul g⁻¹ w,
          ←Gamma0GeneralCuspUnitPeriod20261025a.integralReal_smul g⁻¹ (g • z),dist_smul_left]
      _ = _ := dist_comm _ _
    have B := ordered_card (S.image Inv.inv) w z hw hz h hR (by
      intro v hv
      obtain ⟨g,hg,rfl⟩ := mem_image.mp hv
      rw [rev]
      exact hball _ hg)
    simpa only [card_image_of_injective S inv_injective,mul_comm w.im z.im] using B

end
end ImbalancedChen.Part3.OriginalInversePairBallCount20261113
