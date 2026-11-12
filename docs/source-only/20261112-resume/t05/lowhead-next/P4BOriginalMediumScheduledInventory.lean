import ImbalancedChen.P4BOriginalMediumRestoringBudget

/-! One pre-target inventory for the actual scheduled first-medium modes.
The complete body has two HB groups, 39 previously paid Fourier/rectangle
logarithms, at most twelve restored HB logarithms and three gamma owners. -/
namespace ImbalancedChen.P4BOriginalMediumScheduledInventory
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (bank)
open P5Z.CompleteProductTailDivisorBudgets (logScale)
open P4BOriginalMediumAtomFamily (Index)
open P4BOriginalMediumSignedFibre (scalar)
open P4BOriginalMediumPhysicalAtomSum (onWord)
open P4BOriginalMediumRestoringBudget (pieces scalar_cost pieces_cost)
open P4BOriginalHighRankComplementBlocks (cap exists_scheduled_split_mass)
open P4BOriginalHighRankMotherMass (totalMass)
open P4BOriginalHighRankScheduledCount (outerWidth eventually_width)
open P4BArbitraryWidthUpperBlockGeometry (countingScale target_le_countingScale)
open P4BOriginalCollisionThirdFactor (restoring master restored_mass)
open P4BOriginalUpperFourierTailPaid (dyadicConstant dyadicConstant_pos)
open P4AHeldTaggedCompilerSupport (J0)
open P4BOuterRampRoughness (baseline)

/-- omega and the physical tag mesh are fixed before N. The target threshold
also precedes the local medium selector, word, complementary block and mode.
It is valid for the actual common m(N)=floor(log N) outer resolution. -/
theorem exists_inventory (omega T : ℝ) (ho : 0<omega) :
    ∃ C : ℝ,0≤C ∧ ∀ {b kap : ℝ},0<b → b≤1 → 0<kap → 19/96<baseline b kap →
    ∀ᶠ N : ℕ in atTop,∀ (order : ℕ) (zeta kap0 : ℝ) (I : Index order zeta kap0),
    I.P.N=N → I.P.omega=omega → I.P.T=T → 0≤I.P.e → I.P.ell≤1 →
    ((bank (cap N)).card:ℝ)*totalMass b kap (outerWidth N) N kap0*scalar I*
      (∑ j∈I.P.words.attach,|restoring I.P I.x I.U I.eta j.val|*(pieces (onWord I j):ℝ))≤
      C*(Real.log (N:ℝ))^54 := by
  obtain ⟨C0,hC0,HM⟩ := exists_scheduled_split_mass
  let B := ((master omega T).card:ℝ)*((J0 omega).factorial:ℝ)^3
  let D := 2*dyadicConstant*((J0 omega:ℝ)+2)
  have hB : 0≤B := by dsimp [B]; positivity
  have hD : 0≤D := by dsimp [D]; positivity [dyadicConstant_pos]
  refine ⟨C0*4^12*(B*D^3),by positivity,?_⟩
  intro b kap hb hb1 hk hg
  filter_upwards [HM hb hb1 hk hg,eventually_width 1 (by norm_num),eventually_one_le_nat_log] with N hM hw hl
  intro order zeta kap0 I hN hw' hT he hell
  let L := Real.log (N:ℝ)
  have hLp : 0≤L := by dsimp [L]; linarith
  have hNP : 1<I.P.N := by rw [hN]; have h := hw.1; omega
  have hOP : 0<I.P.omega := by simpa only [hw'] using ho
  have hs : scalar I≤(4*L)^12 := by
    apply (scalar_cost I).2.trans
    apply pow_le_pow_left₀ (by
      have hX := P5Z.CompleteProductTailDivisorBudgets.logScale_one_le
        (P4BArbitraryWidthUpperBlockGeometry.countingScale_one_le I.N_pos)
      linarith)
    rw [hN]
    linarith only [hw.2.2.2.2]
  have hLN : logScale (I.P.N:ℝ)≤2*L := by
    rw [hN]
    apply le_trans _ hw.2.2.2.2
    unfold logScale
    apply add_le_add_left
    exact Real.log_le_log (by have := hw.1; positivity)
      (mul_le_mul_of_nonneg_left (target_le_countingScale N) (by norm_num))
  have hwgt : (∑ j∈I.P.words.attach,|restoring I.P I.x I.U I.eta j.val|*(pieces (onWord I j):ℝ))≤
      B*(D*L)^3 := by
    calc
      _≤∑ j∈I.P.words.attach,|restoring I.P I.x I.U I.eta j.val|*((D*L)^3) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply (pieces_cost (onWord I j) hNP he hOP hell).trans
        change (dyadicConstant*((J0 I.P.omega:ℝ)+2)*logScale (I.P.N:ℝ))^3≤_
        rw [hw']
        have hpos : 0≤dyadicConstant*((J0 omega:ℝ)+2) := by positivity [dyadicConstant_pos]
        apply pow_le_pow_left₀ (mul_nonneg hpos (by
          have := P5Z.CompleteProductTailDivisorBudgets.logScale_one_le
            (by exact_mod_cast hNP.le : (1:ℝ)≤I.P.N)
          linarith))
        dsimp only [D]
        nlinarith only [mul_le_mul_of_nonneg_left hLN hpos]
      _≤_ := by
        rw [←Finset.sum_mul,Finset.sum_attach]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (mul_nonneg hD hLp) 3)
        simpa only [B,hw',hT] using restored_mass I.P hNP he hOP I.x I.U I.eta
  have H := mul_le_mul (mul_le_mul (hM kap0) hs (scalar_cost I).1.le
    (mul_nonneg hC0 (pow_nonneg hLp 39))) hwgt
    (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))
    (mul_nonneg (mul_nonneg hC0 (pow_nonneg hLp 39)) (pow_nonneg (by positivity : 0≤4*L) 12))
  apply H.trans_eq
  change (C0*L^39*(4*L)^12)*(B*(D*L)^3)=(C0*4^12*(B*D^3))*L^54
  ring

end
end ImbalancedChen.P4BOriginalMediumScheduledInventory
