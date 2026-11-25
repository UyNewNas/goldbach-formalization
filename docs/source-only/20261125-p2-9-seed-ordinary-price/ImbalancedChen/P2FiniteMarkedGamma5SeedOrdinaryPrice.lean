import ImbalancedChen.P2FiniteMarkedGamma5NativeSeedSum
import ImbalancedChen.P2FiniteMarkedGamma5ActualProfileMassComparison

namespace ImbalancedChen.P2FiniteMarkedGamma5SeedOrdinaryPrice
noncomputable section
open Filter Finset Real
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SeedHistoryMass
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2FiniteMarkedGamma5RealSelectedPrefix (selected)
open P2FiniteMarkedGamma5NativeSeedSum
open P2FiniteMarkedGamma5ActualRadialAggregate
open P2FiniteMarkedGamma5ActualProfileMassComparison
open P2FiniteMarkedGamma5RadialRoughMass (norm)
open P2EnhancedBadGamma5ArithmeticGeometry (ordinaryBad)
open P2EnhancedBadGamma5CostTheta (actual_bad_inclusive_upper badRawCost)
open P2EnhancedSwitchedTrueNormalization (thetaConversion rawMainAtom rawMainAtom_to_thetaAtom)
open P2EnhancedUnitSourceMass (thetaConversion_nonneg)
open P2EnhancedNonunitWordMass (rawScale)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open scoped Classical Topology BigOperators

/-- One carrier and one set of fixed positive coefficients for the full
profile, the unconverted sharp source, and its marked Theta conversion. -/
def seedMass (N n : ℕ) (k : Root) (t : ℝ) (F : ℕ → List ℕ → ℝ) : ℝ :=
  ∑ i : Index 430, ∑ x ∈ primeTuples N k i,
    if (fun j => physicalPrime N (x j).val) ∈ selected n k t i.val.1 i.val.2 then
      fixedWeight i * F (x (.inl ())).val (coordinateOld n k t ⟨i,x⟩) else 0

private theorem literal_eq {N n : ℕ} {k : Root} {t : ℝ}
    (hN : 2≤N) (ht : 0≤t) (ht' : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (F : ℕ → List ℕ → ℝ) :
    seedMass N n k t F =
      ∑ p ∈ originalBand N k, ∑ l ∈ seedPositions N n k t p,
        levelMark l*F p (levelOccurrence l).current.old :=
  (seed_marked_sum_eq_selected_coordinates N n k t hN ht ht' hn F).symm

def completeProfile (N n : ℕ) (t h : ℝ) (p : ℕ) (w : List ℕ) : ℝ :=
  ∑ s : Split, if admissibleSplit s then
    boundedProfileSlice N s.1.val s.2.val (log (rootQ N n .U4 t p)) h w else 0

private def seedOnly (N n : ℕ) (t : ℝ) (dep : Fin 431) (p : ℕ) :
    Finset (LevelIndex N n .U4 t p dep.val) :=
  if he : dep.val=0 then he.symm ▸ seedPositions N n .U4 t p else ∅

private theorem collapse (N n : ℕ) (t : ℝ) (F : ℕ → List ℕ → ℝ) :
    (∑ dep : Fin 431, ∑ p ∈ originalBand N .U4,
      ∑ l ∈ seedOnly N n t dep p, levelMark l*F p (levelOccurrence l).current.old) =
      ∑ p ∈ originalBand N .U4, ∑ l ∈ seedPositions N n .U4 t p,
        levelMark l*F p (levelOccurrence l).current.old := by
  rw [Finset.sum_eq_single (0 : Fin 431)]
  · simp [seedOnly]
  · intro dep _ hd
    have hv : dep.val≠0 := fun he => hd (Fin.ext he)
    simp [seedOnly,hv]
  · simp

/-- No loss of the coefficient one in the original ordinary comparison.
The profile still has its full product cap 2*N on the prime enumerator. -/
theorem profile_le_ordinary (n : ℕ) (hn : 1/((n:ℝ)+1)≤11/384)
    {epsilon : ℝ} (he : 0<epsilon) :
    ∃ h : ℝ, 0<h ∧ h≤1/8 ∧ ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0≤t → t≤1/12 →
      norm N * seedMass N n .U4 t (completeProfile N n t h) ≤
        norm N * seedMass N n .U4 t (fun p w => ordinaryBad N (rootQ N n .U4 t p) w.prod) +
          epsilon := by
  obtain ⟨h,hh,h8,H⟩ := actual_selected_profile_le_original_plus_epsilon n hn he
  refine ⟨h,hh,h8,?_⟩
  filter_upwards [H,eventually_ge_atTop (2 : ℕ)] with N hN h2
  intro t ht ht'
  have hp := hN t ht ht' (seedOnly N n t)
  change norm N * (∑ dep : Fin 431, ∑ p ∈ originalBand N .U4,
    ∑ l ∈ seedOnly N n t dep p, levelMark l *
        completeProfile N n t h p (levelOccurrence l).current.old) ≤
      norm N * (∑ dep : Fin 431, ∑ p ∈ originalBand N .U4,
        ∑ l ∈ seedOnly N n t dep p, levelMark l *
          ordinaryBad N (rootQ N n .U4 t p) (levelOccurrence l).current.old.prod) + epsilon at hp
  simp only [literal_eq h2 ht ht' hn]
  rw [collapse N n t (completeProfile N n t h),
    collapse N n t (fun p w => ordinaryBad N (rootQ N n .U4 t p) w.prod)] at hp
  exact hp

/-- Both prices retain the same p, Q and every actual seed mark. The
first is unconverted. The second converts at each original d before
summation. Empty seed families need no special positivity assumption. -/
theorem raw_and_converted_upper {epsilon : ℝ} (he : 0<epsilon) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (n : ℕ) (k : Root) (t : ℝ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 →
      let Q := rootQ N n k t
      seedMass N n k t (fun p w => ordinaryBad N (Q p) w.prod) ≤
        (badRawCost+epsilon)*seedMass N n k t (fun p w => rawScale N (Q p) w.prod) ∧
      seedMass N n k t (fun p w => thetaConversion N w.prod*ordinaryBad N (Q p) w.prod) ≤
        (badRawCost+epsilon)*(∑ p ∈ originalBand N k, markedTheta (seedPositions N n k t p)) := by
  obtain ⟨T,h4,H⟩ := actual_bad_inclusive_upper frozenResidualFloor_pos he
  refine ⟨T,h4,?_⟩
  intro N hN n k t ht ht' hn
  dsimp only
  have hN4 := h4.trans hN
  have hN2 : 2≤N := by omega
  have price (p : ℕ) (hp : p ∈ originalBand N k)
      (l : LevelIndex N n k t p 0) :
      let d := wordProduct l
      let Q := rootQ N n k t p
      ordinaryBad N Q d ≤ rawScale N Q d*(badRawCost+epsilon) ∧
      thetaConversion N d*ordinaryBad N Q d ≤ thetaAtom N Q d*(badRawCost+epsilon) := by
    dsimp only
    have h := scale_and_alpha hN2 ht ht' hn hp l
    have hscale := h.2.2.2.1
    have hraw := H N hN _ _ h.1 hscale h.2.2.2.2
    have hR := (one_lt_rpow (by exact_mod_cast (show 1<N by omega)) frozenResidualFloor_pos).trans_le hscale
    have hw := thetaConversion_nonneg hN4 h.1 hR
    refine ⟨hraw,?_⟩
    calc
      _ ≤ thetaConversion N (wordProduct l) *
        rawMainAtom N (rootQ N n k t p) (wordProduct l) (fun _ => badRawCost+epsilon) := by
          simpa only [rawMainAtom,rawScale] using mul_le_mul_of_nonneg_left hraw hw
      _ = _ := rawMainAtom_to_thetaAtom (by omega) h.1 _ hR _
  simp only [literal_eq hN2 ht ht' hn]
  constructor
  · simp only [mul_sum]
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro l _
    have hm := mul_le_mul_of_nonneg_left (price p hp l).1 (mark_pos (levelOccurrence l)).le
    simpa only [mul_left_comm,mul_comm,mul_assoc] using hm
  · simp only [markedTheta,mul_sum]
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro l _
    have hm := mul_le_mul_of_nonneg_left (price p hp l).2 (mark_pos (levelOccurrence l)).le
    simpa only [mul_left_comm,mul_comm,mul_assoc] using hm

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedOrdinaryPrice
