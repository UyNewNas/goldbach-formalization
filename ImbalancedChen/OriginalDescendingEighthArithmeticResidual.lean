import ImbalancedChen.P1ActualUpperClosedParameterUniformity
import ImbalancedChen.P4ASlot17DescendingChargedFrontier
import ImbalancedChen.P4AOriginalEighthParentPhysicalLedger

/-!
SOURCE ONLY / UNCOMPILED. A uniform arithmetic residual supplier for the
original mask129 descending eighth action. The old exponent is its actual
inherited sixth exponent, not the conservative oldRaw envelope. The two
literal upper Rosser densities retain the full prefix-product quotient.
No prime-measure limit, cell integral or desired family bound is assumed.
This treats the unpresieved residual; the physical positive-w beta width
and its absolute-mass ledger are not discarded.
-/

namespace ImbalancedChen.OriginalDescendingEighthArithmeticResidual

noncomputable section
open scoped Classical BigOperators
open P2OriginalDescendingEighthLogSemantics

private def window (a b : ℝ) : Set (ℝ × ℝ) :=
  (Set.Icc a (3 * b) ×ˢ Set.Icc a b) ∩ {q | q.1 ≤ 3 * q.2}

/-- The initial-range compact supplier applies to the literal quotient
level, with one threshold before all products, last primes and exponents. -/
private theorem exists_initial_quotient_error (a b : ℝ) (ha : 0 < a)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y lambda beta u : ℝ, 0 < P → 0 < y →
        actualRosserQuotientParameters (N : ℝ) P y lambda = (beta, u) →
        a ≤ u → u ≤ b → u ≤ beta → beta ≤ 3 * u →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          |actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ lambda / P) *
            Real.log (N : ℝ) / singularSeries N - 4 / beta| < eta := by
  have hcompact : IsCompact (window a b) :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_fst (continuous_const.mul continuous_snd))
  have hlegal : ∀ q ∈ window a b, 0 < q.2 ∧ 0 < q.1 ∧ q.1 ≤ 3 * q.2 := by
    intro q hq
    exact ⟨ha.trans_le hq.1.2.1, ha.trans_le hq.1.1.1, hq.2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_cube_compact_normalized_threshold
      (window a b) hcompact hlegal eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y lambda beta u hP hy hparams hau hub hubeta hbeta cap hcap
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hlevel, hcut⟩ :=
    actualRosserQuotientParameters_exact (N : ℝ) P y lambda hNr hP hy
  rw [hparams] at hlevel hcut
  have hmem : (beta, u) ∈ window a b :=
    ⟨⟨⟨hau.trans hubeta, hbeta.trans (by linarith)⟩, ⟨hau, hub⟩⟩, hbeta⟩
  have h := hbound N hN hEven (beta, u) hmem cap (by simpa only [hcut] using hcap)
  simpa only [hlevel, hcut] using h

/-- Both old and new original descending residuals have their actual
arithmetic values uniformly approximated by the rational initial profiles.
The same N0 works before lambda6, histories, enumeration caps and cells.
The original strict history and terminal inequalities supply 1<s<3.
There is no independent fixed beta identification or density premise. -/
theorem exists_original_descending_residual_difference_error
    (a b : ℝ) (ha : 0 < a) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (lambda6 : List ℕ → ℝ) (pre : List ℕ), pre.length = 8 →
        (∀ p ∈ pre, 0 < p) → (0 : ℝ) < pre.prod → (0 : ℝ) < pre.headD 0 →
        let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
        let current := P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre
        a ≤ t 7 → t 7 ≤ b →
        P4ASlot17DescendingChargedFrontierSourceOnly.DescendingRows t current →
        ∀ cap : ℕ, (pre.headD 0 : ℝ) ≤ (cap : ℝ) →
          |(actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
                ((N : ℝ) ^ current / (pre.prod : ℝ)) -
              actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
                ((N : ℝ) ^ newCap t / (pre.prod : ℝ))) *
              Real.log (N : ℝ) / singularSeries N -
            (4 / (current - total t) - 4 / (newCap t - total t))| < eta := by
  obtain ⟨N0, hN0, hbound⟩ := exists_initial_quotient_error a b ha (eta / 2) (half_pos heta)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven lambda6 pre hlen hpos hP hy
  dsimp only
  intro hau hub hrow cap hcap
  let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
  let current := P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hdict := P2OriginalAscendingEighthCapDictionary.rank_eight_log_dictionary
    (N : ℝ) hNr pre hlen hpos
  have hsum : total t = Real.log (pre.prod : ℝ) / Real.log (N : ℝ) := hdict.1
  have hlast : t 7 = Real.log (pre.headD 0 : ℝ) / Real.log (N : ℝ) := hdict.2
  have hparams (lambda : ℝ) :
      actualRosserQuotientParameters (N : ℝ) (pre.prod : ℝ)
        (pre.headD 0 : ℝ) lambda = (lambda - total t, t 7) := by
    simp only [actualRosserQuotientParameters, hsum, hlast]
  have hchain := residual_interval_chain t current (ha.trans_le hau)
    hrow.lastOrder hrow.seventhHistory hrow.parentUpper hrow.improvement hrow.terminal
  have hold := hbound N hN hEven (pre.prod : ℝ) (pre.headD 0 : ℝ) current
    (current - total t) (t 7) hP hy (hparams current) hau hub hchain.1.le
    (by linarith [hchain.2.1, hchain.2.2.1, hchain.2.2.2]) cap hcap
  have hnew := hbound N hN hEven (pre.prod : ℝ) (pre.headD 0 : ℝ) (newCap t)
    (newCap t - total t) (t 7) hP hy (hparams (newCap t)) hau hub
    (by linarith [hchain.1, hchain.2.1, hchain.2.2.1]) hchain.2.2.2.le cap hcap
  have habs := abs_sub_le (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      ((N : ℝ) ^ current / (pre.prod : ℝ)) * Real.log (N : ℝ) / singularSeries N -
        4 / (current - total t)) 0
    (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      ((N : ℝ) ^ newCap t / (pre.prod : ℝ)) * Real.log (N : ℝ) / singularSeries N -
        4 / (newCap t - total t))
  simp only [sub_zero, zero_sub, abs_neg] at habs
  have hlt := habs.trans_lt (add_lt_add hold hnew)
  have heq :
      (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
          ((N : ℝ) ^ current / (pre.prod : ℝ)) * Real.log (N : ℝ) / singularSeries N -
            4 / (current - total t)) -
        (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
          ((N : ℝ) ^ newCap t / (pre.prod : ℝ)) * Real.log (N : ℝ) / singularSeries N -
            4 / (newCap t - total t)) =
      (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
          ((N : ℝ) ^ current / (pre.prod : ℝ)) -
        actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
          ((N : ℝ) ^ newCap t / (pre.prod : ℝ))) *
          Real.log (N : ℝ) / singularSeries N -
        (4 / (current - total t) - 4 / (newCap t - total t)) := by ring
  rw [heq] at hlt
  convert hlt using 1 <;> ring

/-- The actual old-minus-new arithmetic residual dominates the original
conservative descending kernel, up to the displayed reciprocal-coordinate
error. The frozen positive eighth wall is used literally. The threshold
precedes every inherited sixth cap, actual history and covering cap.
This is a residual estimate, not yet the integral of the whole frontier. -/
theorem exists_original_descending_arithmetic_kernel_lower
    (b eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (lambda6 : List ℕ → ℝ) (pre : List ℕ), pre.length = 8 →
        (∀ p ∈ pre, 0 < p) → (0 : ℝ) < pre.prod → (0 : ℝ) < pre.headD 0 →
        let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
        let current := P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre
        (53 / 13824 : ℝ) ≤ t 7 → t 7 ≤ b →
        P4ASlot17DescendingChargedFrontierSourceOnly.DescendingRows t current →
        ∀ cap : ℕ, (pre.headD 0 : ℝ) ≤ (cap : ℝ) →
          physicalKernel t ≤
            ((actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
                  ((N : ℝ) ^ current / (pre.prod : ℝ)) -
                actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
                  ((N : ℝ) ^ newCap t / (pre.prod : ℝ))) *
                Real.log (N : ℝ) / singularSeries N + eta) * ∏ i, 1 / t i := by
  obtain ⟨N0, hN0, herror⟩ :=
    exists_original_descending_residual_difference_error
      (53 / 13824 : ℝ) b (by norm_num) eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven lambda6 pre hlen hpos hP hy
  dsimp only
  intro hau hub hrow cap hcap
  let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
  let current := P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre
  have herr := herror N hN hEven lambda6 pre hlen hpos hP hy hau hub hrow cap hcap
  have hchain := residual_interval_chain t current (hrow.coordinates 7)
    hrow.lastOrder hrow.seventhHistory hrow.parentUpper hrow.improvement hrow.terminal
  have hkernel := P4ASlot17DescendingChargedFrontierSourceOnly.physicalKernel_le_inheritedSaving hrow
  rw [actualResidualProfile_eq_initial current t (hrow.coordinates 7) hchain.1
      (by linarith [hchain.2.1, hchain.2.2.1, hchain.2.2.2]),
    actualResidualProfile_eq_initial (newCap t) t (hrow.coordinates 7)
      (by linarith [hchain.1, hchain.2.1, hchain.2.2.1]) hchain.2.2.2.le] at hkernel
  apply hkernel.trans
  apply mul_le_mul_of_nonneg_right
  · have hlo := (abs_lt.mp herr).1
    linarith only [hlo]
  · exact Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hrow.coordinates i)).le)

/-- On the literal inherited sixth parent's depth-eight frontier the
incoming mass, sign, history length and covering cutoff are supplied by
membership. Thus this is an arithmetic lower supplier for an actual
old-minus-new summand of the descending charge. No frontier summand or
prime product is replaced by an independent small-prime beta factor. -/
theorem exists_original_descending_frontier_kernel_lower
    (b eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool)
        (cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ),
        state ∈ firstExitDepthFrontier 8
          (P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base)
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) →
        let pre := state.selectedPrefix
        let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
        let current := P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre
        (53 / 13824 : ℝ) ≤ t 7 → t 7 ≤ b →
        P4ASlot17DescendingChargedFrontierSourceOnly.DescendingRows t current →
        state.mass * physicalKernel t ≤
          ((actualFrozenFrontierDensityTerm false N cap
              (P4ASlot17DescendingChargedFrontierSourceOnly.oldLevel (N : ℝ) lambda6) pre -
            actualFrozenFrontierDensityTerm false N cap
              (P4ASlot17DescendingChargedFrontierSourceOnly.raisedLevel (N : ℝ) lambda6) pre) *
              Real.log (N : ℝ) / singularSeries N + eta * state.mass) * ∏ i, 1 / t i := by
  obtain ⟨N0, hN0, hbound⟩ := exists_original_descending_arithmetic_kernel_lower b eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven lambda6 base cap z state hs
  dsimp only
  intro hau hub hrow
  let parent := P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base
  have hgeom := actualPrimeFrontier_geometry 8 (by omega) parent N cap z state hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) state hs
  have hprime : ∀ p ∈ state.selectedPrefix, Nat.Prime p := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))
  have hheadmem : state.selectedPrefix.headD 0 ∈ state.selectedPrefix := by
    rw [← primeHistoryTuple_last hgeom.1]
    exact primeHistoryTuple_mem hgeom.1 _
  have hy : (0 : ℝ) < state.selectedPrefix.headD 0 := by
    exact_mod_cast (hprime _ hheadmem).pos
  have hcap : (state.selectedPrefix.headD 0 : ℝ) ≤ (cap : ℝ) := by
    exact_mod_cast (mem_roughPrimeUniverse.mp
      (hsub.subset (List.mem_reverse.mpr hheadmem))).1.le
  have hmass := hgeom.2.2.2.2.2.2
  have hmass0 : 0 ≤ state.mass := by
    rw [hmass]
    apply List.prod_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    apply div_nonneg zero_le_one
    apply sub_nonneg.mpr
    exact_mod_cast (hprime p hp).one_le
  have hkernel := hbound N hN hEven lambda6 state.selectedPrefix hgeom.1
    (fun p hp => (hprime p hp).pos) hgeom.2.2.1 hy hau hub hrow cap hcap
  have hweighted := mul_le_mul_of_nonneg_left hkernel hmass0
  have hdiff := P2OriginalAscendingEighthCapDictionary.actual_rank_eight_difference N cap
    (P4ASlot17DescendingChargedFrontierSourceOnly.oldLevel (N : ℝ) lambda6)
    (P4ASlot17DescendingChargedFrontierSourceOnly.raisedLevel (N : ℝ) lambda6)
    state.selectedPrefix hgeom.1
  rw [hdiff]
  unfold P2OriginalAscendingEighthCapDictionary.actualEighthResidualDifference
  rw [← hmass]
  simp only [P4ASlot17DescendingChargedFrontierSourceOnly.oldLevel,
    P4ASlot17DescendingChargedFrontierSourceOnly.raisedLevel,
    P4ASlot17DescendingChargedFrontierSourceOnly.raisedExponent]
  dsimp only
  rw [if_pos hrow]
  convert hweighted using 1 <;> ring

end
end ImbalancedChen.OriginalDescendingEighthArithmeticResidual
