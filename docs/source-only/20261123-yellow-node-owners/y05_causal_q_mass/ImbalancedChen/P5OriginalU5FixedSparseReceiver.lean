import ImbalancedChen.P5OriginalU5MarkedMass
import ImbalancedChen.P2GammaU5PlateauRelative

/-! A prescribed sparse, positive U5 marked family. The larger marked
prime lies in (N^(3/25),64 N^(3/25)] for every N. Its window and its
owner are specified before N and before the signed discrepancy. -/
namespace ImbalancedChen.P5OriginalU5FixedSparseReceiver

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalU5CausalFinite (pairSupport)
open P5OriginalU5PlateauPrimeBV (Policy integerRho fullModulus)
open P5OriginalU5MarkedMass
open P2GammaU5PlateauGeometry P2GammaRootFiberRelative
open P2GammaSelectedPhysicalTheta P2GammaRankScaledUpperSource
open P2GammaActualUpperLowRankReduction
open P2OriginalU5SmallPartnerRootPayment (rootQ)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)

def thinRectangle (N : ℕ) : Finset (ℕ × ℕ) :=
  (powerBand N (1/10) (11/100)).product (multiplicativeBand N ((N : ℝ)^(3/25 : ℝ)))

def keepUnit (N : ℕ) (e : ℝ) (P : Policy) (t : ℕ × ℕ) : Prop :=
  t ∈ thinRectangle N ∧ integerRho N e P (fullModulus t 1) ≠ 0

def selected (N : ℕ) (e : ℝ) (P : Policy) : Finset (ℕ × ℕ) :=
  rootFiber N (plateauQ N) (keepUnit N e P)

def sparseFloor : ℝ := Real.log (11/10 : ℝ)/512

theorem sparseFloor_pos : 0 < sparseFloor :=
  div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem eventually_thin_subset :
    ∀ᶠ N : ℕ in atTop, thinRectangle N ⊆ rectangle N := by
  have hg : Tendsto (fun N : ℕ => (N : ℝ)^(1/100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hg.eventually (eventually_gt_atTop (64 : ℝ)), eventually_ge_atTop (2 : ℕ)]
    with N h64 hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hwidth : 64*(N : ℝ)^(3/25 : ℝ) < (N : ℝ)^(13/100 : ℝ) := by
    calc
      _ < (N : ℝ)^(1/100 : ℝ)*(N : ℝ)^(3/25 : ℝ) :=
        mul_lt_mul_of_pos_right h64 (Real.rpow_pos_of_pos hn _)
      _ = _ := by rw [← Real.rpow_add hn]; norm_num
  rintro ⟨p,q⟩ ht
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp ht
  have hsmall := mem_powerBand.mp hp
  obtain ⟨hqwin,hqN⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqp,hqlo,hqhi⟩ := (P5PrimeFixedWidthMass.mem_window (Real.rpow_nonneg hn.le _)).mp hqwin
  apply (mem_rectangle N (p,q)).mpr
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  fin_cases i
  · simpa only [boxLo, boxHi, Matrix.cons_val_zero] using hsmall
  · exact ⟨hqp, hqN, hqlo.le, hqhi.trans_lt hwidth⟩

theorem selected_exact {N : ℕ} (hN : 2 ≤ N) (hsub : thinRectangle N ⊆ rectangle N)
    (e : ℝ) (P : Policy) :
    selected N e P = activeUnits N e P (thinRectangle N) := by
  rw [selected, rootFiber_eq_original_level_filter hN]
  ext t
  constructor
  · intro ht
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp ht).2.1
  · intro ht
    have hkeep := Finset.mem_filter.mp ht
    have hr := hsub hkeep.1
    exact Finset.mem_filter.mpr ⟨rectangle_subset_pairSupport hN hr,
      hkeep, rectangle_rootQ hN hr⟩

theorem eventually_selected_mass :
    ∀ᶠ N : ℕ in atTop, ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy,
      sparseFloor/Real.log (N : ℝ) ≤ reciprocalMass (selected N e P) (unitWeight N e P) := by
  have hsmall := eventually_powerBand_mass (by norm_num : (0 : ℝ)<1/10)
    (by norm_num : (1/10 : ℝ)<11/100)
  have hbig := eventually_multiplicativeBand_mass (3/25) (by norm_num) (by norm_num)
  filter_upwards [hsmall, hbig, eventually_thin_subset, eventually_ge_atTop (2 : ℕ)]
    with N hp hq hsub hN
  intro e he he8 P
  rw [selected_exact hN hsub e P, thinRectangle,
    active_product_mass hN he he8 P _ _ (hsub.trans (rectangle_subset_pairSupport hN))]
  norm_num only [show (11/100 : ℝ)/(1/10)=11/10 by norm_num] at hp
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hpos := Real.log_pos (by norm_num : (1 : ℝ)<11/10)
  calc
    _ = (Real.log (11/10 : ℝ)/4)*(1/(128*Real.log (N : ℝ))) := by
      unfold sparseFloor
      field_simp [hlog.ne'] <;> ring
    _ ≤ _ := mul_le_mul hp hq (by positivity) (le_trans (by positivity) hp)

/-- All constants, including the positive logarithmic mass floor, and the
two prime windows precede N. For every smaller-prime policy and original
native bank the two sides below use one identical physical upper rho. -/
theorem eventually_native_sparse_rank_three (A : ℕ) (kappa : ℝ) (hk : 0 < kappa)
    (hk' : kappa ≤ 1/100) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (R : PairRange) (mesh : ℕ) (bank : CandidateBank mesh)
      (b : ℚ), 0 ≤ b → b ≤ 1/1000 → ∀ e : ℝ, 0 < e → e < 1/8 →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1/1000 → ∀ (e' h : ℝ) (m cap : ℕ),
      let P := selectedPolicy R bank b false N
      let S := selected N e P
      let sigma := unitWeight N e P
      let retain := actualExtendedThirdCompactUpperPolicy e' h m N false
      let moduli := physicalUpperModuli N plateauLevel eps retain cap
      (∀ t ∈ S, let slots := [(t.2,true),(t.1,true)]
        rootQ N t = plateauQ N ∧
        P2OriginalSelectedPairNativeData.rootSeed false b N t = plateauLevel-2*(b : ℝ) ∧
        (b = 0 → (N : ℝ)^(P2OriginalSelectedPairNativeData.rootSeed false b N t) = rootQ N t) ∧
        P t = P5OriginalU5NativeRootCover.policyAt R bank b plateauLevel N t ∧
        P2OriginalSelectedIntegerPrefixSquares.IntegerSquareGates N (plateauLevel-2*(b : ℝ))
          1 (slots.map Prod.fst) ∧
        P2OriginalSelectedIntegerPrefixSquares.IntegerSquareGates N (plateauLevel-2*(b : ℝ))
          (P2OriginalSelectedIntegerPrefixSquares.selectedPrimes slots).prod
          (P2OriginalSelectedIntegerPrefixSquares.remainingPrimes slots) ∧
        integerRho N e P (fullModulus t 1) = 1) ∧
      sparseFloor/Real.log (N : ℝ) ≤ reciprocalMass S sigma ∧
      (2*MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct*(N : ℝ)/(Real.log (N : ℝ))^2)*
        (sparseFloor/Real.log (N : ℝ)) ≤ selectedTheta N (plateauQ N) S sigma ∧
      0 < selectedTheta N (plateauQ N) S sigma ∧
      |selectedGamma N moduli (fullUpperRho N plateauLevel eps retain cap) S sigma -
        selectedGamma N moduli (rankRemainder N plateauLevel eps retain cap 3) S sigma -
        selectedEmpty N moduli (rankUpperRho N plateauLevel eps retain cap 3)
          ((N : ℝ)^(1-kappa)) S sigma| ≤
          eta*selectedTheta N (plateauQ N) S sigma/(Real.log (N : ℝ))^A := by
  have hk1 : kappa < 1 := by linarith
  have hrel := eventually_actualCompact_rootFiber_relative A 1 sparseFloor sparseFloor_pos
    kappa hk hk1 eta heta
  filter_upwards [hrel, eventually_selected_mass, eventually_ge_atTop (4 : ℕ)] with N hr hm hN
  intro R mesh bank b hb hb' e he he8 eps heps0 heps e' h m cap
  dsimp only
  let P := selectedPolicy R bank b false N
  let S := selected N e P
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1<N by omega)
  have hs (t : ℕ × ℕ) (ht : t ∈ S) := rootFiber_data ht
  have hw (t : ℕ × ℕ) (ht : t ∈ S) : unitWeight N e P t = 1 := by
    simp only [unitWeight, (P5OriginalU5UnitMark.original_integer_unit
      (by omega : 2 ≤ N) he he8 P (hs t ht).1).2, Int.cast_one]
  have hmass := hm e he he8 P
  have hpositive : 0 < reciprocalMass S (unitWeight N e P) :=
    (div_pos sparseFloor_pos (Real.log_pos hn)).trans_le hmass
  have hnon (t : ℕ × ℕ) (ht : t ∈ S) : 0 ≤ unitWeight N e P t := by rw [hw t ht]; norm_num
  have htheta := selectedTheta_lower hN (plateauQ N) S (unitWeight N e P)
    (fun t ht => (hs t ht).1) hnon (fun t ht => (hs t ht).2.2.2)
  have hu := MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct_pos
  have hlog := Real.log_pos hn
  refine ⟨?_, hmass, (mul_le_mul_of_nonneg_left hmass (by positivity)).trans htheta,
    (mul_pos (by positivity) hpositive).trans_le htheta, ?_⟩
  · intro t ht
    have hd := hs t ht
    have hv : P2OriginalSelectedPairNativeData.rootLevel false N t = plateauLevel := by
      apply le_antisymm
      · exact (Real.rpow_le_rpow_left_iff hn).mp hd.2.2.1.le
      · exact (Real.rpow_le_rpow_left_iff hn).mp hd.2.2.1.symm.le
    have hm' : t ∈ P5OriginalU5NativeRootCover.marks N plateauLevel :=
      Finset.mem_filter.mpr ⟨hd.1,hv⟩
    have hseed : P2OriginalSelectedPairNativeData.rootSeed false b N t =
        plateauLevel-2*(b : ℝ) := by rw [P2OriginalSelectedPairNativeData.rootSeed,hv]
    have hg := P5OriginalU5NativeRootCover.actual_root_gates (by omega : 2 ≤ N) hm' hb hb'
    refine ⟨hd.2.2.1, hseed, ?_, P5OriginalU5NativeRootCover.native_policy_at R bank b hm',
      hg.2.1, hg.2.2,
      (P5OriginalU5UnitMark.original_integer_unit (by omega) he he8 P hd.1).2⟩
    intro hz
    simpa only [hseed, hz, Rat.cast_zero, mul_zero, sub_zero, plateauQ] using hd.2.2.1.symm
  · have hnu : 0 ≤ plateauLevel := by rw [plateauLevel_exact]; norm_num
    have h37 : plateauLevel ≤ (37/50 : ℝ) := by rw [plateauLevel_exact]; norm_num
    apply hr 3 plateauLevel eps hnu (rank_three_gap hnu h37 heps hk')
      e' h m cap (plateauQ N) 1 zero_lt_one (keepUnit N e P) (unitWeight N e P)
    · intro t ht
      rw [hw t ht]
      norm_num
    · exact Or.inr (by simpa only [mul_one, pow_one] using hmass)

end
end ImbalancedChen.P5OriginalU5FixedSparseReceiver
