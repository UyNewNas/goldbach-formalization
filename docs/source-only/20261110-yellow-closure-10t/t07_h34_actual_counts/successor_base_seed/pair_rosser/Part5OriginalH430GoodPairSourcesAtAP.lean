import ImbalancedChen.Part5OriginalH430BankAfterPairRosser

/-! Direct ordinary comparison of every actual Gamma5--8 good count with its
two-dimensional original integral. This form can also be used at seed depth
zero without selecting a bank alternative. -/
namespace ImbalancedChen.Part5OriginalH430GoodPairSourcesAtAP
noncomputable section
open Set Finset
open P5OriginalActionMassBound P5OriginalFeedbackDomains P2OriginalBankChildPrimeMass
open P2OriginalHalfOpenProfileCarrier P2OriginalPositiveSameQMassLift
open P2OriginalProfileThetaNormalization P2OriginalW2CountTupleReindex
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430ImmutableBankProfiles (precedingH)
open Part5OriginalH430OrdinaryPairWalls (actual_half_iff_open)
open Part5OriginalH430OrdinaryPairCounts (true_pair_split ordinaryIntegral)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430PairOrdinaryCountPayment (laneExcess laneAP oldHMass window all_good_pair_count_means)
open scoped Classical BigOperators

theorem oldHMass_eq_profile (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 4) (g : Fin 430) :
    oldHMass N Q L d j k g=pairThetaOldProfile N Q L d (originalW2At j) k (precedingH g) := by
  unfold oldHMass window pairThetaOldProfile
  rw [sum_filter]

theorem actual_good_pair_to_original_integral {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (r : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N r →
      ∀ (l : LevelIndex N n r t p dep) (j : Fin 36) (k : Fin 4),
      let Q := rootQ N n r t p; let d := wordProduct l; let L := wordLevel l
      sourceGoodOccurrence N Q (actualState N) d (originalW2At j) k+laneExcess N Q L d j k ≤
        laneAP N Q L d j k + thetaAtom N Q d*ordinaryIntegral j k + ε*thetaAtom N Q d := by
  have hF : frozenResidualFloor≤1 := by
    unfold frozenResidualFloor
    have h : (1:ℝ)≤101^440 := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h])
  obtain ⟨Ta,h4,ha⟩ := all_good_pair_count_means (half_pos he)
  obtain ⟨Tb,hb⟩ := all36_positive_sameQ_pair_lift frozenResidualFloor_pos hF (half_pos he)
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven n r t p dep ht ht' hn hp l j k
  have hNa := (le_max_left Ta Tb).trans hN
  have hN1 : 1<N := by have := h4.trans hNa; omega
  let Q := rootQ N n r t p; let d := wordProduct l; let L := wordLevel l
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hLp := frozenResidualFloor_pos.trans_le hL.1
  have h := (ha N hNa hEven n r t p dep ht ht' hn hp l j k 0).2
  rw [oldHMass_eq_profile] at h
  have hsum := hb N ((le_max_right Ta Tb).trans hN) Q {d} (fun _ => (1:ℝ)) (fun _ => L)
    (fun _ => j) (fun _ => k) (by simpa using hd) (by simp) (by simpa using hL) (by simpa using hQ)
  simp only [Theta_eq_sum_atoms,sum_singleton,one_mul] at hsum
  have hu := (abs_le.mp hsum).2
  change sourceGoodOccurrence N Q (actualState N) d (originalW2At j) k+laneExcess N Q L d j k ≤
    laneAP N Q L d j k + thetaAtom N Q d*ordinaryIntegral j k + ε*thetaAtom N Q d
  rw [true_pair_split hN1 hd hLp hQ (actualState N) j k 0]
  unfold ordinaryIntegral
  linarith only [h,hu]

end
end ImbalancedChen.Part5OriginalH430GoodPairSourcesAtAP
