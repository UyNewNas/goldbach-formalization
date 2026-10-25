import ImbalancedChen.P5ZU1011OriginalFifteenJointSelectedCompletion
import ImbalancedChen.ActualSelectedPairFactorization

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The original15 completed natural factors satisfy the actual alpha=1+3kappa
monomials. The effective theta is nu-2delta+kappa and the proof buffer is
kappa/2, so the physical native run level stays EXACTLY nu-2delta. The A
range is the common kappa range, not an artificially tightened native-delta
range. True64delta cell reserves pay the perturbed selected-product interval.
Both actual capacity branches use their already constructed factors; the
below-one branch uses the genuine full-vector repair. No monomial bound or
factorability is a premise. Beta attachment and analytic licenses are OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenJointKappaMonomials
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalSixteenInteriorArithmetic P5U1011JointOverlap
open U1011OriginalSixteenNearCapBoxProfiles (nu delta G)
open U1011OriginalSixteenJointNearCapCompiler (rowCoefficient)
open U1011OriginalFifteenJointSelectedSupport
open U1011OriginalFifteenJointSelectedCompletion
open U1011OriginalW16AttachedWellSupport (specified)

def effectiveTheta (p : Policy) (B : Box) (eta : ℚ) (kappa : ℝ) : ℝ :=
  (nu p B eta:ℝ)-2*(delta p B eta:ℝ)+kappa

theorem runLevel_exact (p : Policy) (B : Box) (eta : ℚ) (kappa : ℝ) (N : ℕ) :
    runLevel p B eta N=(N:ℝ)^(effectiveTheta p B eta kappa-2*(kappa/2)) := by
  unfold runLevel effectiveTheta
  congr 1
  ring

private theorem mask_cap_le (p : Policy) (hp : p.val<15) (v : LogFour) : cap p v≤(153/256:ℝ) := by
  unfold cap
  rw [if_pos hp]
  by_cases hs : selectedMass p v≤(25/128:ℝ)
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

/-- Both upper constraints of the original selected-subproduct theorem
are proved from the actual corrected cap and its stored64buffer reserve. -/
theorem actual_kappa_critical {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (hp : p.val<15) (B : Box) (eta : ℚ)
    (heta : 0<eta) (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) {kappa : ℝ} (hk0 : 0<kappa)
    (hk : kappa≤(delta p B eta:ℝ)/64) :
    (1/2:ℝ)≤effectiveTheta p B eta kappa ∧ effectiveTheta p B eta kappa≤5/8 ∧
      0<kappa/2 ∧ kappa/2<(1/100000:ℝ) ∧
      (N:ℝ)^(2*effectiveTheta p B eta kappa-1)≤(selectedProduct p t:ℝ) ∧
      (selectedProduct p t:ℝ)≤(N:ℝ)^actualSelectedSubproductUpper (1+3*kappa) (effectiveTheta p B eta kappa) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hm:=U1011OriginalSixteenNearCapBoxProfiles.whole_box_nearcap_margins p B eta hv hw hc heta (coordinates N t) hb
  have hdc : (delta p B eta:ℝ)≤3/4096 := hm.2.1
  have hnu : (nu p B eta:ℝ)+64*(delta p B eta:ℝ)≤153/256 :=
    hm.2.2.1.trans (mask_cap_le p hp _)
  have hhalfQ:=U1011OriginalSixteenNearCapBoxProfiles.half_le_G p B
  have hgateQ:=NearCapRationalParameters.gate_buffer (G p B) (capLower p B) eta
  have hhalf : (1/2:ℝ)≤(G p B:ℝ) := by exact_mod_cast hhalfQ
  have hgate : (G p B:ℝ)+64*(delta p B eta:ℝ)≤(nu p B eta:ℝ) := by exact_mod_cast hgateQ
  have hc' : (nu p B eta:ℝ)+64*(delta p B eta:ℝ)≤
      min ((1+selectedMass p (coordinates N t))/2) ((57/64:ℝ)-(3/2:ℝ)*selectedMass p (coordinates N t)) := by
    simpa only [cap,if_pos hp] using hm.2.2.1
  have hlow:=hc'.trans (min_le_left _ _)
  have hupp:=hc'.trans (min_le_right _ _)
  have hθlo : (1/2:ℝ)≤effectiveTheta p B eta kappa := by dsimp [effectiveTheta];linarith
  have hθhi : effectiveTheta p B eta kappa≤5/8 := by dsimp [effectiveTheta];linarith
  have hl : 2*effectiveTheta p B eta kappa-1≤selectedMass p (coordinates N t) := by dsimp [effectiveTheta];linarith
  have hu : selectedMass p (coordinates N t)≤actualSelectedSubproductUpper (1+3*kappa) (effectiveTheta p B eta kappa) := by
    unfold actualSelectedSubproductUpper effectiveTheta
    apply le_min <;> linarith
  refine ⟨hθlo,hθhi,by linarith,by linarith,?_,?_⟩
  · rw [←selectedProduct_rpow hN ht p]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hl
  · rw [←selectedProduct_rpow hN ht p]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hu

theorem actual_completed_kappa_monomials {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (hp : p.val<15) (B : Box) (eta : ℚ)
    (heta : 0<eta) (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) (hd : rowCoefficient p B eta N d≠0)
    {kappa A : ℝ} (hk0 : 0<kappa) (hk : kappa≤(delta p B eta:ℝ)/64)
    (hAlower : (N:ℝ)^kappa≤A) (hAupper : A≤(N:ℝ)^(1/3-kappa/2)) :
    let abc:=factors p B eta N A t d
    abc.1*abc.2.1*abc.2.2=fullPrefix t*d ∧ (abc.1:ℝ)≤A ∧
      A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-3*kappa/2) ∧
      (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-3*kappa/2) ∧
      (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤(N:ℝ)^(2-kappa) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hA : 1≤A := (Real.one_le_rpow hn.le hk0.le).trans hAlower
  have hApos : 0<A := zero_lt_one.trans_le hA
  have hAup0 : A≤(N:ℝ)^(1/3:ℝ) := hAupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
  have hcomp:=native_completion hN ht p hp B eta heta hv hw hc hb hd A hA hAup0
  have hpos:=completed_factors_positive hN ht p hp B eta heta hv hw hc hb hd A hA hAup0
  have ha : (0:ℝ)<(factors p B eta N A t d).1 := by exact_mod_cast hpos.1
  have hb' : (0:ℝ)<(factors p B eta N A t d).2.1 := by exact_mod_cast hpos.2.1
  have hc' : (0:ℝ)<(factors p B eta N A t d).2.2 := by exact_mod_cast hpos.2.2
  have hcrit:=actual_kappa_critical hN ht p hp B eta heta hv hw hc hb hk0 hk
  have hlevel:=runLevel_exact p B eta kappa N
  by_cases hC : 1≤runLevel p B eta N/(A*(selectedProduct p t:ℝ))
  · have hmiddle : (factors p B eta N A t d).2.1=selectedProduct p t := by
      simpa only [if_pos hC] using hcomp.2.2.2
    have hcap : A*((factors p B eta N A t d).2.1:ℝ)*((factors p B eta N A t d).2.2:ℝ)≤
        (N:ℝ)^(effectiveTheta p B eta kappa-2*(kappa/2)) := by simpa only [hlevel] using hcomp.2.2.1
    have hlo : (N:ℝ)^(2*effectiveTheta p B eta kappa-1)≤((factors p B eta N A t d).2.1:ℝ) := by
      simpa only [hmiddle] using hcrit.2.2.2.2.1
    have hup : ((factors p B eta N A t d).2.1:ℝ)≤(N:ℝ)^actualSelectedSubproductUpper (1+3*kappa) (effectiveTheta p B eta kappa) := by
      simpa only [hmiddle] using hcrit.2.2.2.2.2
    obtain ⟨h1,h2,h3⟩:=selectedPair_monomials hn hApos ha hb' hc' hcap hlo hup hcomp.2.1
    exact ⟨hcomp.1,hcomp.2.1,
      h1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)),
      h2.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)),
      h3.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))⟩
  · have hfull:=native_full_support hN ht p B eta heta hv hw hc hb hd
    have hfull' : actualDwellSupport ((N:ℝ)^(effectiveTheta p B eta kappa-2*(kappa/2))) (fullVector t d) := by
      simpa only [hlevel] using hfull
    have hpositive : ∀q∈fullVector t d,0<q := by
      intro q hq
      rcases List.mem_append.mp hq with hq|hq
      · simp only [specified,List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl|rfl|rfl <;> exact slots_pos ht _
      · exact (Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hq)).pos
    have hAlow : (N:ℝ)^(kappa/2)≤A := (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)).trans hAlower
    have hAup : A≤(N:ℝ)^(1/3-(kappa/2)/2) := hAupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
    have hsmall : (N:ℝ)^(effectiveTheta p B eta kappa-2*(kappa/2))/(A*(selectedProduct p t:ℝ))<1 := by
      rw [←hlevel];exact lt_of_not_ge hC
    have hr:=actualDwell_full_vector_repair_targets hn hcrit.2.2.1 hcrit.2.2.2.1 hcrit.1 hcrit.2.1
      hAlow hAup (fullVector t d) hpositive hfull' (selectedProduct p t) (selectedProduct_pos ht p)
      hcrit.2.2.2.2.2 hsmall
    simpa only [factors,if_neg hC,Nat.cast_one,one_pow,mul_one,fullVector_product p B eta hd,
      show 1-3*(kappa/2)=1-3*kappa/2 by ring,
      show 2-3*(kappa/2)=2-3*kappa/2 by ring,
      show 2-2*(kappa/2)=2-kappa by ring] using hr

end
end ImbalancedChen.P5Z.U1011OriginalFifteenJointKappaMonomials
