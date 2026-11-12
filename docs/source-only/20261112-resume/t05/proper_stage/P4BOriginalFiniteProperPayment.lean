import ImbalancedChen.P4BOriginalFiniteProperArithmetic
import ImbalancedChen.P4BOriginalFiniteTrimmedCount

/-! Original section 2 proper prime powers in the signed final rectangle.
Both AP and coprime mean are evaluated at the same complete product. -/
namespace ImbalancedChen.P4BOriginalFiniteProperPayment
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
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (properPowerReserve)
open P5Z.OriginalPrimeAtlasReserveBranches
  (mediumAtlas noMediumAtlas originalMediumLow originalMediumHigh)

/-- The sum over all original chart labels of the absolute proper-power
corrections is paid to arbitrary logarithmic accuracy. Its one threshold
precedes every legal test width, policy, beta attachment and aligned
rectangle. The fixed cutoff K is also allowed to vary in this estimate. -/
theorem eventually_actual_proper (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (b kappa s : ℝ) (hb : 0<b),0<kappa →
      ∀ (hs : 0<s) (hgap : 2*s≤baseline b kappa-exponent),
      ∀ (K : ℕ) (kappa0 : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (level : ℝ),
      let S := Q omega N
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
  filter_upwards [eventually_active_count,Hoff,Hdiag] with N hcount hoff hdiag
  intro b kappa s hb hk hs hgap K kappa0 m r n e q a omega k level
  dsimp only
  intro hrange
  let S := Q omega N
  let c := coefficient m r n e q a omega k N level
  let cc : ℕ → ℂ := fun d => (c d:ℂ)
  let L := pairLicence hb hs hgap N
  let P := active L N
  let T := P.filter (fun ps => ps.prod=N)
  let U := P.filter (fun ps => ps.prod≠N)
  have h1 : 1≤N := le_trans (by norm_num : 1≤2) hcount.1
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hqpos (d) (hdq : d∈S) : 0<d :=
    Nat.pos_of_ne_zero (P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hdq).ne_zero
  have hc (d) : |c d|≤1 := P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ _
  obtain ⟨hrow,hrowN⟩ := rows N h1 S c hqpos hc hrange
  have hTsub : T⊆fullCollisionWords N 2 N := by
    intro ps hp
    obtain ⟨hps,heq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hps).1,heq⟩
  have hT : (T.card:ℝ)≤F*(N:ℝ)^eps := by
    have hcard : T.card≤N.divisors.card^2 := (Finset.card_le_card hTsub).trans
      (fullCollisionWords_card_le N 2 N (by omega))
    exact (Nat.cast_le.mpr hcard).trans (tau N 2 h1 le_rfl)
  have hU : (U.card:ℝ)≤B*(N:ℝ)^(1-exponent/2)*Real.log (N:ℝ)^3 :=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ P))).trans
      (hcount.2 b kappa s hb hk hs hgap)
  have hdiagCost : (∑ ps∈T,‖signedRow S cc N ps.prod‖)≤
      (delta/2)*(N:ℝ)/Real.log (N:ℝ)^A := by
    calc
      _ ≤ ∑ _ps∈T,D*(N:ℝ)^(modulusExponent+eps) := by
        apply Finset.sum_le_sum
        intro ps hps
        rw [(Finset.mem_filter.mp hps).2]
        exact hrowN
      _ = (T.card:ℝ)*(D*(N:ℝ)^(modulusExponent+eps)) := by simp
      _ ≤ (F*(N:ℝ)^eps)*(D*(N:ℝ)^(modulusExponent+eps)) :=
        mul_le_mul_of_nonneg_right hT (by positivity)
      _ = (F*D)*(N:ℝ)^(eps+(modulusExponent+eps)) := by
        conv_rhs => rw [Real.rpow_add hNr]
        ring
      _ ≤ _ := by simpa only [pow_zero,mul_one] using hdiag
  have hoffCost : (∑ ps∈U,‖signedRow S cc N ps.prod‖)≤
      (delta/2)*(N:ℝ)/Real.log (N:ℝ)^A := by
    calc
      _ ≤ ∑ _ps∈U,C*(N:ℝ)^eps := by
        apply Finset.sum_le_sum
        intro ps hps
        obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hps
        have hi := P5Z.ExactOriginalSmoothDyadicPartition.words_spec (Finset.Icc 1 N) 2 ps
          (Part3.AllKLambdaChartCorrection.properChartWords_spec (Finset.mem_filter.mp hp).1).1
        exact hrow ps.prod (List.prod_pos (fun j hj => (Finset.mem_Icc.mp (hi.2 j hj)).1))
          (word_geometry hb hk hs hgap hp).2 hn
      _ = (U.card:ℝ)*(C*(N:ℝ)^eps) := by simp
      _ ≤ (B*(N:ℝ)^(1-exponent/2)*Real.log (N:ℝ)^3)*(C*(N:ℝ)^eps) :=
        mul_le_mul_of_nonneg_right hU (by positivity)
      _ = (B*C)*(N:ℝ)^(1-exponent/2+eps)*Real.log (N:ℝ)^3 := by
        conv_rhs => rw [Real.rpow_add hNr]
        ring
      _ ≤ _ := hoff
  have hpart := Finset.sum_filter_add_sum_filter_not P (fun ps => ps.prod=N)
    (fun ps => ‖signedRow S cc N ps.prod‖)
  apply (proper_chart_sum_le hb hs hgap K N kappa0 S cc).trans
  rw [← hpart]
  exact (add_le_add hdiagCost hoffCost).trans_eq (by ring)

/-- Only the original medium and no-medium signed HB sums are left in
the retained discrepancy. The comparison is in complex norm and can
therefore be used on its real part with the unchanged physical mass. -/
theorem eventually_trimmed_two_atlases (K : ℕ) (hK : 2≤K) {b kappa : ℝ}
    (hb : 0<b) (hk : 0<kappa) (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hgap : 2*s≤baseline b kappa-exponent),
      ∀ (kappa0 zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (level : ℝ),
      let L := pairLicence hb hs hgap N
      let S := Q omega N
      let c := coefficient m r n e q a omega k N level
      let cc := fun d => (c d:ℂ)
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖(Part3.primeProductSignedError 2 N N S c (trimmedWeight b kappa s kappa0 N):ℂ)-
        (∑ js∈chartBank N 2,
          (mediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js+
           noMediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js))‖
        ≤delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  filter_upwards [P4BOriginalFiniteTrimmedCount.eventually_trimmed_exact_atlas
    (kappa:=kappa) K hK hb,eventually_actual_proper A delta hd] with N ha hp
  intro s hs hgap kappa0 zeta m r n e q a omega k level
  dsimp only
  intro hrange
  have h := ha s hs hgap kappa0 zeta m r n e q a omega k level
  dsimp only at h
  rw [Finset.sum_sub_distrib] at h
  have hproper := hp b kappa s hb hk hs hgap K kappa0 m r n e q a omega k level hrange
  rw [h,sub_right_comm,sub_self,zero_sub,norm_neg]
  exact (norm_sum_le _ _).trans hproper

end
end ImbalancedChen.P4BOriginalFiniteProperPayment
