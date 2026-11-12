import ImbalancedChen.P4BOriginalRankTwoChartDictionary

/-! The contribution of one dyadic two-prime label on the remaining
physical rough rank two. Both original HB owners are restored together. -/
namespace ImbalancedChen.P4BOriginalRankTwoChartPayment
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOuterRampRoughness (baseline)
open P4BOriginalRankTwoChartScales
open P4BOriginalRankTwoConductorWindows (rectangle modulusCap eventually_rectangles)
open P4BOriginalRankTwoChartDictionary (eventually_original_rectangles)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteSignedTrim (pairLicence)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOriginalTwoAtlasSmallPayment (remaining)
open P4AFiniteFallbackLowRankRho (activeLow activeLow_power activeLow_squarefree activeLow_target_coprime)
open P5Z.ActualLabelledPrimeSmoothCharts (primeTuples)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.OriginalPrimeAtlasReserveBranches

abbrev tau (m : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ) :=
  P4AOriginalOrderedThirdActualCoefficient.alignedWidth (P4AOriginalFiniteFallbackCount.jointIndex
    (P4AFallbackCanonicalBanks.bank m) (P4AOriginalNewFifthUnion.data e q a).m) k

def carrier (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (ell : ℝ) : Finset ℕ :=
  remaining omega N ∩ activeLow m r n e q a omega N (tau m e q a k) ell

/-- No discrepancy estimate, row norm, spectral input or separated
profile is assumed. The full 599/1000 support bound used by the existing
proper-power supplier is a conclusion of the same physical fine schedule. -/
theorem eventually_rank_two_original_chart (K : ℕ) (hK : 2≤K) {b kappa kappa0 : ℝ}
    (hb : 0<b) (hb1 : b<1) (hk : 0<kappa) (hk0 : 0<kappa0)
    (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ s : ℝ,∀ hs : 0<s,∀ hg : 2*s≤baseline b kappa-19/96,
      ∀ (zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      ell<1/1000 →
      let S := carrier m r n e q a omega k N ell
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      let cc := fun d => (c d:ℂ)
      let L := pairLicence hb hs hg N
      let js := labels N
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖mediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js+
        noMediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js‖
        ≤delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  have hfee : 0<delta/3 := by linarith
  obtain ⟨Nr,Hr⟩ := P4BActualUpperRoughPrimeReserveZero.exists_actual_upper_roughPrimeReserve_zero
    (kappa:=kappa) K hK hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
  filter_upwards [eventually_ge_atTop (2^12:ℕ),eventually_ge_atTop Nr,
    eventually_original_rectangles hb hb1 hk hk0,eventually_rectangles A (delta/3) hfee,
    P4BOriginalRestrictedAtlasProper.eventually_subset_proper A (delta/3) hfee]
      with N hN hNr HX HR Hproper
  intro s hs hg zeta m r n e q a omega k ell hell
  dsimp only
  intro hrange
  let js := labels N
  let S := carrier m r n e q a omega k N ell
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let cc := fun d => (c d:ℂ)
  let L := pairLicence hb hs hg N
  have hbank : js∈chartBank N 2 := (scales hN).1
  have hS : S⊆Q omega N := fun d hd' => (Finset.mem_filter.mp (Finset.mem_inter.mp hd').1).1
  have hd' (d : ℕ) (h : d∈S) :
      0<d ∧ d≤modulusCap N ∧ N.Coprime d ∧ |c d|≤1 := by
    have hh := (Finset.mem_inter.mp h).2
    exact ⟨Nat.pos_of_ne_zero (activeLow_squarefree _ _ _ _ _ _ _ _ _ _ hh).ne_zero,
      Nat.le_floor (activeLow_power _ _ _ _ _ _ _ _ (by omega) _ _ hell hh).le,
      activeLow_target_coprime _ _ _ _ _ _ _ _ _ _ hh,
      P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d⟩
  have H := original_chart_allGroup_exact L K N N kappa0 S cc js
  have hrough := Hr N hNr s hs (by simpa only [one_mul] using hg) kappa0 S cc js hbank
  rw [hrough,add_zero,allGroup_actual_branch_split L K N N kappa0
    (originalMediumLow zeta js) (originalMediumHigh zeta js)] at H
  have he := HX s hs hg S c
  change (∑ ps∈primeTuples N 2, originalChart L N kappa0 js ps*
    P5Z.IndependentPrimeSourceWordDictionary.wordKernel S cc N ps)=_ at he
  let P := properPowerReserve L K N N kappa0 S cc js
  have hp : ‖P‖≤delta/3*(N:ℝ)/Real.log (N:ℝ)^A :=
    (Finset.single_le_sum (f:=fun j => ‖properPowerReserve L K N N kappa0 S cc j‖)
      (fun j _ => norm_nonneg _) hbank).trans
      (Hproper b kappa s hb hk hs hg K kappa0 m r n e q a omega k ((N:ℝ)^ell) S hS hrange)
  have hid :
      mediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js+
        noMediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js =
        ((∑ d∈S,(c d:ℂ)*rectangle true N d)+(∑ d∈S,(c d:ℂ)*rectangle false N d))+P := by
    dsimp only [P]
    linear_combination he-H
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
    (add_le_add (HR S c hd' true) (HR S c hd' false))) hp).trans_eq (by ring))

end
end ImbalancedChen.P4BOriginalRankTwoChartPayment
