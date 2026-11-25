import ImbalancedChen.Part5OriginalH430SeedConvertedMass
import ImbalancedChen.Part5OriginalH430StrictSeedCeiling
import ImbalancedChen.P2OriginalW2CentreThetaPayment
import ImbalancedChen.Part5OriginalH430HistoryScaleCore

/-! Supply the residual scale, true alpha and positive marked normalization
from the generated U3/U4 path positions, including generation zero. -/
namespace ImbalancedChen.Part5OriginalH430SeedHistoryMass
noncomputable section
open Set Real Finset
open P5OriginalActionMassBound P2EnhancedLowerPrimeChildCarriers
open P2EnhancedSwitchedTrueNormalization (trueAlpha prefixExponent)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2OriginalW2CentreThetaPayment (groupedSigma weighted_fiber_sum)
open P2SeedOmegaLiteralFibre (K)
open P2Selected430CausalOccurrenceExporter (iterate)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430SeedConvertedMass Part5OriginalH430StrictSeedCeiling
open scoped Classical BigOperators

def markedTheta {N n p dep : ℕ} {k : Root} {t : ℝ}
    (S : Finset (LevelIndex N n k t p dep)) : ℝ :=
  ∑ l ∈ S, levelMark l*thetaAtom N (rootQ N n k t p) (wordProduct l)

def markedConverted {N n p dep : ℕ} {k : Root} {t : ℝ}
    (S : Finset (LevelIndex N n k t p dep)) : ℝ :=
  converted N (rootQ N n k t p) (S.image wordProduct) (groupedSigma S wordProduct levelMark)

theorem real_word_theta {N n p dep : ℕ} {k : Root} {t : ℝ}
    (S : Finset (LevelIndex N n k t p dep)) :
    Theta N (rootQ N n k t p) (S.image wordProduct) (groupedSigma S wordProduct levelMark) =
      markedTheta S := by
  rw [Theta_eq_sum_atoms]
  exact weighted_fiber_sum S wordProduct levelMark _

theorem converted_centre_on_histories {J : ℝ} (hJ : J<P2SeedOmegaLiteralFunctional.actualJ2omega) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ S : Finset (LevelIndex N n k t p dep),
        J*markedTheta S ≤ (ordinaryPart*markedTheta S-(K/4)*markedConverted S)/5 := by
  obtain ⟨T,hT,h⟩ := base_after_converted frozenResidualFloor_pos hJ
  refine ⟨T,hT,?_⟩
  intro N hN n k t p dep ht ht' hn hp S
  have hw := scale_and_alpha (by omega : 2≤N) ht ht' hn hp (dep:=dep)
  let D := S.image wordProduct
  have hB (d : ℕ) (hd : d∈D) : 0<d ∧
      (N:ℝ)^frozenResidualFloor ≤ rootQ N n k t p/d ∧ 2≤trueAlpha N (rootQ N n k t p) d := by
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hd
    exact ⟨(hw l).1,(hw l).2.2.2⟩
  have hσ (d : ℕ) (_ : d∈D) : 0≤groupedSigma S wordProduct levelMark d :=
    sum_nonneg (fun l _ => (mark_pos (levelOccurrence l)).le)
  have hh := h N hN (rootQ N n k t p) D (groupedSigma S wordProduct levelMark)
    (fun d hd => (hB d hd).1) hσ (fun d hd => (hB d hd).2.1) (fun d hd => (hB d hd).2.2)
  simpa only [D,real_word_theta,markedConverted] using hh

theorem converted_on_histories :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ S : Finset (LevelIndex N n k t p dep),
        (1/50:ℝ)*markedTheta S ≤ (ordinaryPart*markedTheta S-(K/4)*markedConverted S)/5 := by
  apply converted_centre_on_histories
  exact (show (1/50:ℝ)<20249/1000000 by norm_num).trans
    P2SeedOmegaOriginalNumerical.actualJ2omega_gt_safe_base

def seedPositions (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ) :
    Finset (LevelIndex N n k t p 0) :=
  univ.filter fun l => 0 < requestValue (iterate 0) (levelOccurrence l).current

/-- Both ingredients are simultaneous for every actual positive leaf at
either original root. This is the ordinary real centre less the converted
integer charge; no sifted-prime count estimate is presumed here. -/
theorem positive_seed_positions :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      let S := seedPositions N n k t p
      (1/50:ℝ)*markedTheta S ≤ (ordinaryPart*markedTheta S-(K/4)*markedConverted S)/5 ∧
      ∀ l∈S, P2EnhancedLowerPhysicalNode.residual (levelOccurrence l).current.node.physical /
        (11/5:ℝ) < (levelOccurrence l).current.node.physical.ceiling := by
  obtain ⟨T,hT,h⟩ := converted_on_histories
  refine ⟨T,hT,?_⟩
  intro N hN n k t p ht ht' hn hp
  refine ⟨h N hN n k t p 0 ht ht' hn hp _,?_⟩
  intro l hl
  exact actual_positive_seed_strict_ceiling (by omega) ht ht' hn hp
    (levelOccurrence_source l).1 (mem_filter.mp hl).2

end
end ImbalancedChen.Part5OriginalH430SeedHistoryMass
