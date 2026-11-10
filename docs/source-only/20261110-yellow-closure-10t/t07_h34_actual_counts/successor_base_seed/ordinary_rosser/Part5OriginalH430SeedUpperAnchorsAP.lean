import ImbalancedChen.Part5OriginalH430SameQCanonicalMains
import ImbalancedChen.Part5OriginalH430SeedFourMarkedRounds
import ImbalancedChen.Part5OriginalH430OrdinarySingletonKernel

/-! Both unchanged-prefix Gamma1 terms have the genuine original positive
Rosser polynomial at their own cutoff. Only the signed arithmetic remainder
survives in their joint same-Q seed bound. -/
namespace ImbalancedChen.Part5OriginalH430SeedUpperAnchorsAP
noncomputable section
open Set Finset Real Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (Phi cutoff Theta)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2ActualMarkedCountState (rootLevel root_level_geometry)
open P2SameQPhysicalRosserSeed (cutoff_log_coordinate)
open P2SeedOmegaLiteralFibre (s0 phi1)
open P2SeedOmegaLiteralFunctional (correction)
open P5CanonicalUpperCancellation (upperA)
open P2OriginalPositiveSameQMassLift
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430SignedSeedCount (signedAnchors signedSingles signedPositive)
open Part5OriginalH430SeedFourMarkedRounds (originalRound four_physical_round_count_debts)
open Part5OriginalH430SameQCanonicalMains (model physical_main_sides)
open Part5OriginalH430OrdinarySingletonKernel (anchor_correction)
open Part5OriginalH430OriginalRootQBound (original_root_Q_le_target)
open P2OriginalW2CentreThetaPayment (groupedSigma)
open scoped Classical BigOperators

def upperAP (N : ℕ) (Q : ℝ) (d : ℕ) (s : ℝ) : ℝ :=
  ordinaryRosserRemainder true N d (P2ActualMarkedCountState.rootLevel Q d) (cutoff Q d s)

def anchorAP (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) : ℝ :=
  ∑ d∈D,σ d*(4*upperAP N Q d s0+upperAP N Q d phi1)

theorem scaled_cutoff {N d : ℕ} {η Q s : ℝ} (hN : 1<N) (hη : 0<η)
    (hr : (N:ℝ)^η≤Q/(d:ℝ)) (hs : 1≤s) (hs10 : s≤10) :
    (N:ℝ)^(η/10)≤cutoff Q d s := by
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hrec := one_div_le_one_div_of_le (show 0<s by linarith) hs10
  calc
    _ ≤ (N:ℝ)^(η*(1/s)) := rpow_le_rpow_of_exponent_le hNr.le (by nlinarith only [mul_le_mul_of_nonneg_left hrec hη.le])
    _ = ((N:ℝ)^η)^(1/s) := rpow_mul (Nat.cast_nonneg N) _ _
    _ ≤ _ := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg N) _) hr (one_div_nonneg.mpr (by linarith))

/-- This measures aggregate error with its actual sign and coefficients
rather than taking absolute values for each individual old prefix. -/
theorem signed_anchors_to_AP {η ε : ℝ} (hη : 0<η) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ),
      (∀ d∈D,0<d ∧ d≤N ∧ (N:ℝ)^η≤Q/(d:ℝ)) → (∀ d∈D,0≤σ d) →
      signedAnchors N Q D σ≤anchorAP N Q D σ+ε*Theta N Q D σ := by
  obtain ⟨T,h4,h⟩ := physical_main_sides (div_pos hη (by norm_num : (0:ℝ)<10))
    (div_pos he (by norm_num : (0:ℝ)<5))
  refine ⟨T,h4,?_⟩
  intro N hN hEven Q D σ hg hσ
  have hN1 : 1<N := by omega
  have hNr : (1:ℝ)<N := by exact_mod_cast hN1
  have point (d : ℕ) (hd : d∈D) (s : ℝ) (h3 : 3≤s) (h5 : s≤5) :
      (sourceSieveCount N d (d*N) (cutoff Q d s):ℝ) -
        (1+correction s)*thetaAtom N Q d ≤ upperAP N Q d s+ε/5*thetaAtom N Q d := by
    obtain ⟨hd,hdN,hr⟩ := hg d hd
    have hR := (one_lt_rpow hNr hη).trans_le hr
    have hz := scaled_cutoff hN1 hη hr (by linarith) (by linarith : s≤10)
    have hm := (h N hN hEven Q (cutoff Q d s) s d hd hdN hR hz
      (cutoff_log_coordinate hR (by linarith)) (by linarith) (by linarith)).1
    have hlev := root_level_geometry hR (show 1≤s by linarith)
    have hu := ordinaryRosser_upper_finite (N:=N) (d:=d) hlev.1 hlev.2
    change (sourceSieveCount N d (d*N) (cutoff Q d s):ℝ)≤model true N Q d (cutoff Q d s)+upperAP N Q d s at hu
    rw [anchor_correction h3 h5] at hm
    linarith only [hm,hu]
  have su : Phi N Q D σ s0-(1+correction s0)*Theta N Q D σ ≤
      (∑ d∈D,σ d*upperAP N Q d s0)+(ε/5)*Theta N Q D σ := by
    unfold Phi
    rw [Theta_eq_sum_atoms,mul_sum,mul_sum,←sum_sub_distrib,←sum_add_distrib]
    apply sum_le_sum
    intro d hd
    nlinarith only [mul_le_mul_of_nonneg_left
      (point d hd s0 (by norm_num [s0]) (by norm_num [s0])) (hσ d hd)]
  have pu : Phi N Q D σ phi1-(1+correction phi1)*Theta N Q D σ ≤
      (∑ d∈D,σ d*upperAP N Q d phi1)+(ε/5)*Theta N Q D σ := by
    unfold Phi
    rw [Theta_eq_sum_atoms,mul_sum,mul_sum,←sum_sub_distrib,←sum_add_distrib]
    apply sum_le_sum
    intro d hd
    nlinarith only [mul_le_mul_of_nonneg_left
      (point d hd phi1 (by norm_num [phi1]) (by norm_num [phi1])) (hσ d hd)]
  have heq : anchorAP N Q D σ = 4*(∑ d∈D,σ d*upperAP N Q d s0)+(∑ d∈D,σ d*upperAP N Q d phi1) := by
    unfold anchorAP; rw [mul_sum,←sum_add_distrib]; apply sum_congr rfl; intro _ _; ring
  rw [signedAnchors,heq]
  linarith only [su,pu]

theorem seed_anchor_payment {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ B : Finset (LevelIndex N n k t p dep),
        let Q := rootQ N n k t p; let D := B.image wordProduct; let σ := groupedSigma B wordProduct levelMark
        signedAnchors N Q D σ≤anchorAP N Q D σ+ε*markedTheta B := by
  obtain ⟨T,h4,hT⟩ := signed_anchors_to_AP frozenResidualFloor_pos he
  refine ⟨T,h4,?_⟩
  intro N hN hEven n k t p dep ht ht' hn hp B
  have h2 : 2≤N := by omega
  have hcap := original_root_Q_le_target N n k t p h2 ht ht' hp
  have h := hT N hN hEven (rootQ N n k t p) (B.image wordProduct) (groupedSigma B wordProduct levelMark)
  rw [←real_word_theta B]
  apply h
  · intro d hd
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hd
    obtain ⟨hd,hL,hQ,hcut,_⟩ := scale_and_alpha h2 ht ht' hn hp l
    have hR := sameQ_residual_gt_one (by omega) hd (frozenResidualFloor_pos.trans_le hL.1) hQ
    have hlt : (wordProduct l:ℝ)<rootQ N n k t p := by
      simpa only [one_mul] using (lt_div_iff₀ (Nat.cast_pos.mpr hd : (0:ℝ)<wordProduct l)).mp hR
    exact ⟨hd,by exact_mod_cast (hlt.trans_le hcap).le,hcut⟩
  · intro d hd
    exact sum_nonneg (fun l _ => (mark_pos (levelOccurrence l)).le)

end
end ImbalancedChen.Part5OriginalH430SeedUpperAnchorsAP
