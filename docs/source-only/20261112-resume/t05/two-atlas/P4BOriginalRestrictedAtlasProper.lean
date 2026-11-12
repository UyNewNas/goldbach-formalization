import ImbalancedChen.P4BOriginalFiniteProperPayment

/-! Localize the published proper-power estimate to any subset of the same
rectangle. A signed row on a subset need not be smaller than the complete
signed row. The original absolute count of words and the original
subset-uniform row estimates are therefore applied before summation. -/
namespace ImbalancedChen.P4BOriginalRestrictedAtlasProper
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOuterRampRoughness (baseline)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteSignedTrim (pairLicence trimmedWeight)
open P4BOriginalFiniteProperWords
open P4BOriginalFiniteProperArithmetic
open P5Z.ProperPowerSignedMeanHBTransport (signedRow)
open P5Z.ProperPowerPhysicalPolynomialPayment (tau_word_rank_subpower)
open P5Z.ActualCommonRefinedPayments (fullCollisionWords fullCollisionWords_card_le)
open P5Z.ActualDyadicRankPolynomial (bankLogConstant bankLogConstant_pos)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (roughPrimeReserve properPowerReserve)
open P5Z.OriginalPrimeAtlasReserveBranches

theorem eventually_subset_proper (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (b kappa s : ℝ) (hb : 0<b),0<kappa →
      ∀ (hs : 0<s) (hgap : 2*s≤baseline b kappa-exponent),
      ∀ (K : ℕ) (kappa0 : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ)
        (level : ℝ) (S : Finset ℕ),S⊆Q omega N →
      let c := coefficient m r n e q a omega k N level
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      (∑ js∈chartBank N 2,‖properPowerReserve (pairLicence hb hs hgap N)
        K N N kappa0 S (fun d => (c d:ℂ)) js‖)≤delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  let eps : ℝ := exponent/4
  have he : 0<eps := by norm_num [eps,exponent]
  obtain ⟨C,D,hC,hD,rows⟩ := exists_row_costs eps he
  obtain ⟨F,hF,tau⟩ := tau_word_rank_subpower 2 he
  let B := 8*Real.exp 1*bankLogConstant
  have hB : 0<B := by dsimp [B]; have := bankLogConstant_pos; positivity
  have Hoff := eventually_powerLog_le_logAccuracy (B*C) (1-exponent/2+eps) 3 A
    (by norm_num [eps,exponent]) (delta/2) (half_pos hd)
  have Hdiag := eventually_powerLog_le_logAccuracy (F*D) (eps+(modulusExponent+eps)) 0 A
    (by norm_num [eps,exponent,modulusExponent]) (delta/2) (half_pos hd)
  filter_upwards [eventually_active_count,Hoff,Hdiag] with N hc hoff hdiag
  intro b kappa s hb hk hs hgap K kappa0 m r n e q a omega k level S hS
  dsimp only
  intro hrange
  let c := coefficient m r n e q a omega k N level
  let cc : ℕ → ℂ := fun d => (c d:ℂ)
  let L := pairLicence hb hs hgap N
  let P := active L N
  let Dg := P.filter (fun w => w.prod=N)
  have h1 : 1≤N := by have := hc.1; omega
  have hNr : (0:ℝ)<N := by exact_mod_cast h1
  obtain ⟨hr,hrN⟩ := rows N h1 S c
    (fun d hd => Nat.pos_of_ne_zero (P4AUpperTaggedBetaAttachment.support_squarefree
      _ _ _ _ (hS hd)).ne_zero)
    (fun d => P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d) hrange
  have hcard : (P.card:ℝ)≤B*(N:ℝ)^(1-exponent/2)*Real.log (N:ℝ)^3 :=
    hc.2 b kappa s hb hk hs hgap
  have hsub : Dg⊆fullCollisionWords N 2 N := fun w hw =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1,
      (Finset.mem_filter.mp hw).2⟩
  have hdiagCard : (Dg.card:ℝ)≤F*(N:ℝ)^eps := (Nat.cast_le.mpr
    ((Finset.card_le_card hsub).trans (fullCollisionWords_card_le N 2 N (by omega)))).trans
      (tau N 2 h1 le_rfl)
  let X := C*(N:ℝ)^eps
  let Y := D*(N:ℝ)^(modulusExponent+eps)
  have hx : 0≤X := by dsimp [X]; positivity
  have hy : 0≤Y := by dsimp [Y]; positivity
  have hp (w : List ℕ) (hw : w∈P) :
      ‖signedRow S cc N w.prod‖≤X+(if w.prod=N then Y else 0) := by
    by_cases hh : w.prod=N
    · rw [if_pos hh,hh]
      exact hrN.trans (le_add_of_nonneg_left hx)
    · rw [if_neg hh,add_zero]
      have hi := P5Z.ExactOriginalSmoothDyadicPartition.words_spec (Finset.Icc 1 N) 2 w
        (Part3.AllKLambdaChartCorrection.properChartWords_spec (Finset.mem_filter.mp hw).1).1
      exact hr _ (List.prod_pos (fun j hj => (Finset.mem_Icc.mp (hi.2 j hj)).1))
        (word_geometry hb hk hs hgap hw).2 hh
  have hySum : (∑ w∈P,if w.prod=N then Y else 0)=(Dg.card:ℝ)*Y := by
    change _=((P.filter (fun w => w.prod=N)).card:ℝ)*Y
    rw [← Finset.sum_filter]
    simp
  apply (proper_chart_sum_le hb hs hgap K N kappa0 S cc).trans ((Finset.sum_le_sum hp).trans ?_)
  rw [Finset.sum_add_distrib,hySum]
  simp only [Finset.sum_const,nsmul_eq_mul]
  apply (add_le_add (mul_le_mul_of_nonneg_right hcard hx)
    (mul_le_mul_of_nonneg_right hdiagCard hy)).trans
  have h1e : (B*(N:ℝ)^(1-exponent/2)*Real.log (N:ℝ)^3)*X =
      (B*C)*(N:ℝ)^(1-exponent/2+eps)*Real.log (N:ℝ)^3 := by
    conv_rhs => rw [Real.rpow_add hNr]
    dsimp [X]; ring
  have h2e : (F*(N:ℝ)^eps)*Y=(F*D)*(N:ℝ)^(eps+(modulusExponent+eps)) := by
    conv_rhs => rw [Real.rpow_add hNr]
    dsimp [Y]; ring
  rw [h1e,h2e]
  exact (add_le_add hoff (by simpa only [pow_zero,mul_one] using hdiag)).trans_eq (by ring)

/-- The subset is selected only in the outer modulus sum. The medium
and no-medium owners, W, eta, original dyadic labels and all HB rows are
the original ones on both sides. -/
theorem eventually_subset_atlases (K : ℕ) (hK : 2≤K) {b kappa : ℝ}
    (hb : 0<b) (hk : 0<kappa) (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hgap : 2*s≤baseline b kappa-exponent),
      ∀ (kappa0 zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ)
        (level : ℝ) (S : Finset ℕ),S⊆Q omega N →
      let L := pairLicence hb hs hgap N
      let c := coefficient m r n e q a omega k N level
      let cc := fun d => (c d:ℂ)
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖(Part3.primeProductSignedError 2 N N S c (trimmedWeight b kappa s kappa0 N):ℂ)-
        (∑ js∈chartBank N 2,
          (mediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js+
           noMediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js))‖
        ≤delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  obtain ⟨Nr,Hr⟩ := P4BActualUpperRoughPrimeReserveZero.exists_actual_upper_roughPrimeReserve_zero
    (kappa:=kappa) K hK hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
  filter_upwards [eventually_subset_proper A delta hd,eventually_ge_atTop Nr,
    eventually_ge_atTop (2:ℕ)] with N hp hNr hN
  intro s hs hgap kappa0 zeta m r n e q a omega k level S hS
  dsimp only
  intro hrange
  let c := coefficient m r n e q a omega k N level
  let L := pairLicence hb hs hgap N
  let cc := fun d => (c d:ℂ)
  have ha := original_prime_discrepancy_mode_carriers L K N N kappa0 zeta S c
  rw [← P4BArbitraryWidthUpperPairProfile.original_signed_source b kappa s hN S c] at ha
  have hr : ∀ js∈chartBank N 2,roughPrimeReserve L K N N kappa0 S cc js=0 :=
    Hr N hNr s hs (by simpa only [one_mul] using hgap) kappa0 S cc
  rw [Finset.sum_add_distrib,Finset.sum_eq_zero hr,add_zero] at ha
  have ht := P4BOriginalFiniteSignedTrim.difference_eq_trim hb hs hgap hN kappa0 S c
  rw [Complex.ofReal_sub] at ht
  have he : (Part3.primeProductSignedError 2 N N S c (trimmedWeight b kappa s kappa0 N):ℂ)=
      ∑ js∈chartBank N 2,(mediumAtlas L K N N kappa0 (originalMediumLow zeta js)
        (originalMediumHigh zeta js) S cc js + noMediumAtlas L K N N kappa0
        (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js-
        properPowerReserve L K N N kappa0 S cc js) := by linear_combination ha-ht
  rw [Finset.sum_sub_distrib] at he
  rw [he,sub_right_comm,sub_self,zero_sub,norm_neg]
  exact (norm_sum_le _ _).trans (hp b kappa s hb hk hs hgap K kappa0 m r n e q a omega k level S hS hrange)

end
end ImbalancedChen.P4BOriginalRestrictedAtlasProper
