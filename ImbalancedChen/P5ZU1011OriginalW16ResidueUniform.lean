import ImbalancedChen.P5ZU1011OriginalW16FactorMonomials

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The SAME actual original W16 natural factors work for every residue
exponent alpha=1+3*kappa with0<=kappa<=the constructed source buffer.
The spectral exponent remains the original7/32. The critical-upper loss
and the successful-W logarithmic budget are both proved, not supplied as
spectral/endpoint licences. No AP estimate or modified residual-atom
provenance is inferred from these factor-size statements.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16ResidueUniform
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open U1011OriginalW16NativeInitialization U1011OriginalW16NativeCompletion
open U1011OriginalW16FactorMonomials
open P5U1011JointOverlap
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion

/-- Both original spectral upper constraints are retained when alpha
moves; only the second decreases, by exactly7*kappa/32. -/
theorem critical_upper_residue_loss (nu kappa : ℝ) (hk : 0≤kappa) :
    actualSelectedSubproductUpper 1 nu-7*kappa/32≤
      actualSelectedSubproductUpper (1+3*kappa) nu := by
  have hl := min_le_left ((32-39*nu)/34) ((2-2*nu-7/32)/3)
  have hr := min_le_right ((32-39*nu)/34) ((2-2*nu-7/32)/3)
  unfold actualSelectedSubproductUpper
  apply le_min <;> linarith

/-- The original64delta upper endpoint margin pays the moving residue
in the SUCCESS case, where the middle factor need not be critical. -/
theorem W_success_second_residue {x delta nu kappa A a b c : ℝ}
    (hx : 1<x) (hd : 0≤delta) (hk : kappa≤delta)
    (hA : 0<A) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hnu : nu+64*delta≤(153/256:ℝ))
    (haA : a≤A) (hbB : b≤x^(2*nu-1)) (hcC : c≤x^(1-nu-2*delta)/A) :
    x^(7*(1+3*kappa)/32)*A*a*b^5*c^2≤x^(2-4*delta) := by
  have hx0 : 0<x := zero_lt_one.trans hx
  have hL : 0<Real.log x := Real.log_pos hx
  have hAc : A*c≤x^(1-nu-2*delta) := by
    have h := (le_div_iff₀ hA).1 hcC
    simpa only [mul_comm] using h
  have hlogAc := (Real.le_rpow_iff_log_le (mul_pos hA hc) hx0).1 hAc
  rw [Real.log_mul hA.ne' hc.ne'] at hlogAc
  have hlogb := (Real.le_rpow_iff_log_le hb hx0).1 hbB
  have hloga := (Real.log_le_log_iff ha hA).2 haA
  have hnuL := mul_le_mul_of_nonneg_right hnu hL.le
  have hkL := mul_le_mul_of_nonneg_right hk hL.le
  have hdL := mul_nonneg hd hL.le
  apply Real.le_rpow_of_log_le hx0
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) hA.ne',Real.log_rpow hx0]
  simp only [Real.log_pow]
  nlinarith only [hlogAc,hlogb,hloga,hnuL,hkL,hdL]

/-- Product and positive natural factors are chosen BEFORE kappa. The
same explicit factors then satisfy all three original monomials uniformly
for every alpha=1+3*kappa in the actual source-buffer interval. -/
theorem actual_W16_factors_uniform_residue {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t))
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport ((N:ℝ)^residualExponent (coordinates N t)) tail)
    (hrough : ∀ q ∈ tail, Nat.Prime q ∧ (q:ℝ)<(N:ℝ)^cutoffExponent (coordinates N t)) :
    let abc := completedFactors N t A tail
    let delta := buffer (coordinates N t)
    abc.1*abc.2.1*abc.2.2=fullPrefix t*tail.prod ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀ kappa : ℝ, 0≤kappa → kappa≤delta →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-4*delta) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-4*delta) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*
          (abc.2.2:ℝ)^2≤(N:ℝ)^(2-39*delta/8) := by
  let v := coordinates N t
  let out := completedBins N t A tail
  obtain ⟨hprod,hapos,hbpos,hcpos,hleft,hfirst,hsecond,hthird⟩ :=
    actual_W16_factorization_monomials hN ht he A hA hAupper tail hresidual hrough
  refine ⟨hprod,hapos,hbpos,hcpos,hleft,?_⟩
  intro kappa hk0 hk
  refine ⟨hfirst,?_,hthird⟩
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hApos : 0<A := zero_lt_one.trans_le hA
  have ha : (0:ℝ)<out.left.prod := by exact_mod_cast hapos
  have hb : (0:ℝ)<out.middle.prod := by exact_mod_cast hbpos
  have hc : (0:ℝ)<out.right.prod := by exact_mod_cast hcpos
  have hleft' : (out.left.prod:ℝ)≤A := hleft
  have hbuf := buffer_bounds v he
  have hmargin : theta v+64*buffer v≤(153/256:ℝ) := by
    have h := hbuf.2.2.2
    rw [W_cap] at h
    linarith [coordinate_pos hN ht 2]
  obtain ⟨htrace,hprod',hpositive,hcases⟩ := actual_W16_complete_factors hN ht he A hA hAupper tail hresidual hrough
  rcases hcases with hbounded | ⟨hlower,hupper,hL,hR⟩
  · have hbB : (out.middle.prod:ℝ)≤(N:ℝ)^(2*theta v-1) := by
      simpa only [wp,actualNatList_cast_prod] using hbounded.2.1
    have hcC : (out.right.prod:ℝ)≤(N:ℝ)^(1-theta v-2*buffer v)/A := by
      simpa only [wp,actualNatList_cast_prod] using hbounded.2.2
    exact W_success_second_residue hn hbuf.1.le hk hApos ha hb hc hmargin hleft' hbB hcC
  · have hlower' : (N:ℝ)^(2*theta v-1)≤(out.middle.prod:ℝ) := by
      simpa only [wp,actualNatList_cast_prod] using hlower.le
    have hupper' : (out.middle.prod:ℝ)≤
        (N:ℝ)^actualSelectedSubproductUpper (1+3*kappa) (theta v) := by
      have hloss := critical_upper_residue_loss (theta v) kappa hk0
      have he : actualSelectedSubproductUpper 1 (theta v)-buffer v≤
          actualSelectedSubproductUpper (1+3*kappa) (theta v) := by linarith [hbuf.1]
      have h := hupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le he)
      simpa only [wp,actualNatList_cast_prod] using h
    have hcap : A*(out.middle.prod:ℝ)*(out.right.prod:ℝ)≤(N:ℝ)^(theta v-2*buffer v) := by
      have hh : (out.right.prod:ℝ)≤(N:ℝ)^(theta v-2*buffer v)/(A*(out.middle.prod:ℝ)) := by
        simpa only [wp,actualNatList_cast_prod] using hR
      have h := (le_div_iff₀ (mul_pos hApos hb)).1 hh
      nlinarith only [h]
    exact (selectedPair_monomials (α := 1+3*kappa) hn hApos ha hb hc hcap hlower' hupper' hleft').2.1

end
end ImbalancedChen.P5Z.U1011OriginalW16ResidueUniform
