import ImbalancedChen.P1ActualUpperClosedParameterUniformity
import ImbalancedChen.P4AOriginalEighthParentPhysicalLedger
import ImbalancedChen.P4AActualEighthInheritedHistoryGuard

/-!
SOURCE ONLY / UNCOMPILED. Native arithmetic residual supplier for the
original ascending mask138 action, with M=A(t2+t4+t8)-10^-6 and conservative
R=A(t1+t4). The old level remains the actual inherited sixth exponent.
The actual frontier supplies H7<current; no history-bound assumption or
identification of current with R is made. The original PhysicalRows allow
closed residual endpoint three and retain their positive eighth cutoff.
The common threshold precedes policies, prefixes, states and caps.

This is an unpresieved arithmetic summand estimate. The thirteen-cell
ownership, actual adopted third/sixth provenance, positive-w beta-width
error and prime integral remain separate obligations.
-/

namespace ImbalancedChen.OriginalAscendingNineteenArithmeticResidual
noncomputable section
open scoped Classical BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly

private def window (a b : ℝ) : Set (ℝ × ℝ) :=
  (Set.Icc a (3 * b) ×ˢ Set.Icc a b) ∩ {q | q.1 ≤ 3 * q.2}

private theorem initial_quotient_error (a b : ℝ) (ha : 0 < a)
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

/-- The actual two-sided arithmetic error, at the inherited parent and
the original ascending cap. Rank7 admissibility is discharged from the
literal sixth-parent frontier, independently of all selected-cell data. -/
theorem exists_original_ascending_frontier_residual_error
    (b eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool)
        (cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ),
        state ∈ firstExitDepthFrontier 8
          (P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base)
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) →
        let pre := state.selectedPrefix
        let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
        let current := P4ASlot19ChargedFrontierSourceOnly.inheritedSixth lambda6 pre
        PhysicalRows t → current ≤ comparisonCap t → t 7 ≤ b →
          |(actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
                ((N : ℝ) ^ current / (pre.prod : ℝ)) -
              actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
                ((N : ℝ) ^ newCap t / (pre.prod : ℝ))) *
              Real.log (N : ℝ) / singularSeries N -
            (4 / (current - total t) - 4 / (newCap t - total t))| < eta := by
  obtain ⟨N0, hN0, hbound⟩ := initial_quotient_error
    (53 / 13824 : ℝ) b (by norm_num) (eta / 2) (half_pos heta)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven lambda6 base cap z state hs
  dsimp only
  intro hrow hCap hub
  let pre := state.selectedPrefix
  let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
  let current := P4ASlot19ChargedFrontierSourceOnly.inheritedSixth lambda6 pre
  let parent := P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hgeom := actualPrimeFrontier_geometry 8 (by omega) parent N cap z state hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) state hs
  have hprime : ∀ p ∈ pre, Nat.Prime p := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))
  have hpos : ∀ p ∈ pre, 0 < p := fun p hp => (hprime p hp).pos
  have hheadmem : pre.headD 0 ∈ pre := by
    rw [← primeHistoryTuple_last hgeom.1]
    exact primeHistoryTuple_mem hgeom.1 _
  have hy : (0 : ℝ) < pre.headD 0 := by exact_mod_cast (hprime _ hheadmem).pos
  have hcap : (pre.headD 0 : ℝ) ≤ (cap : ℝ) := by
    exact_mod_cast (mem_roughPrimeUniverse.mp
      (hsub.subset (List.mem_reverse.mpr hheadmem))).1.le
  have hHistory : history7 t < current := by
    have hh := P4AActualEighthInheritedHistoryGuard.actual_log_history7_lt_current
      base lambda6 N cap hNr 0 z (fun p : ℕ => 1 / ((p : ℝ) - 1)) state hs
    exact hh
  have hlastOrder : t 7 ≤ t 6 := hrow.ordered (by decide : (6 : Fin 8) ≤ 7)
  have hlo : t 7 < current - total t := by
    linarith [history7_residual t]
  have hnewlo : t 7 < newCap t - total t := by
    linarith [hrow.improvement]
  have hdict := P2OriginalAscendingEighthCapDictionary.rank_eight_log_dictionary
    (N : ℝ) hNr pre hgeom.1 hpos
  have hsum : total t = Real.log (pre.prod : ℝ) / Real.log (N : ℝ) := hdict.1
  have hlast : t 7 = Real.log (pre.headD 0 : ℝ) / Real.log (N : ℝ) := hdict.2
  have hparams (lambda : ℝ) :
      actualRosserQuotientParameters (N : ℝ) (pre.prod : ℝ)
        (pre.headD 0 : ℝ) lambda = (lambda - total t, t 7) := by
    simp only [actualRosserQuotientParameters, hsum, hlast]
  have hold := hbound N hN hEven (pre.prod : ℝ) (pre.headD 0 : ℝ) current
    (current - total t) (t 7) hgeom.2.2.1 hy (hparams current) hrow.eighthCutoff hub hlo.le
    (by linarith [hrow.improvement, hrow.newResidualUpper]) cap hcap
  have hnew := hbound N hN hEven (pre.prod : ℝ) (pre.headD 0 : ℝ) (newCap t)
    (newCap t - total t) (t 7) hgeom.2.2.1 hy (hparams (newCap t))
    hrow.eighthCutoff hub hnewlo.le hrow.newResidualUpper cap hcap
  have herr := abs_sub_le
    (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      ((N : ℝ) ^ current / (pre.prod : ℝ)) * Real.log (N : ℝ) / singularSeries N -
        4 / (current - total t)) 0
    (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      ((N : ℝ) ^ newCap t / (pre.prod : ℝ)) * Real.log (N : ℝ) / singularSeries N -
        4 / (newCap t - total t))
  simp only [sub_zero, zero_sub, abs_neg] at herr
  have hlt := herr.trans_lt (add_lt_add hold hnew)
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

private theorem parentDensity_eq_profile (current : ℝ) (t : Point) :
    parentDensity current t =
      (4 / (current - total t) - 4 / (newCap t - total t)) * ∏ i, 1 / t i := by
  simp only [parentDensity, one_div, Finset.prod_inv_distrib, div_eq_mul_inv]
  ring

/-- Literal old-minus-new ascending frontier charge dominates its original
conservative rational density up to eta times the exact incoming mass.
The retained H7 bound is obtained from membership, not from a comparison R. -/
theorem exists_original_ascending_frontier_density_lower
    (b eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool)
        (cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ),
        state ∈ firstExitDepthFrontier 8
          (P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base)
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) →
        let pre := state.selectedPrefix
        let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
        let current := P4ASlot19ChargedFrontierSourceOnly.inheritedSixth lambda6 pre
        PhysicalRows t → current ≤ comparisonCap t → t 7 ≤ b →
        state.mass * conservativeDensity t ≤
          ((actualFrozenFrontierDensityTerm false N cap
              (P4ASlot19ChargedFrontierSourceOnly.oldLevel (N : ℝ) lambda6) pre -
            actualFrozenFrontierDensityTerm false N cap
              (P4ASlot19ChargedFrontierSourceOnly.raisedLevel (N : ℝ) lambda6) pre) *
              Real.log (N : ℝ) / singularSeries N + eta * state.mass) * ∏ i, 1 / t i := by
  obtain ⟨N0, hN0, herror⟩ := exists_original_ascending_frontier_residual_error b eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven lambda6 base cap z state hs
  dsimp only
  intro hrow hCap hub
  let pre := state.selectedPrefix
  let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
  let current := P4ASlot19ChargedFrontierSourceOnly.inheritedSixth lambda6 pre
  let parent := P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base
  have herr := herror N hN hEven lambda6 base cap z state hs hrow hCap hub
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hHistory : history7 t < current :=
    P4AActualEighthInheritedHistoryGuard.actual_log_history7_lt_current
      base lambda6 N cap hNr 0 z (fun p : ℕ => 1 / ((p : ℝ) - 1)) state hs
  have hgeom := actualPrimeFrontier_geometry 8 (by omega) parent N cap z state hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) state hs
  have hprime : ∀ p ∈ pre, Nat.Prime p := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))
  have hmass := hgeom.2.2.2.2.2.2
  have hmass0 : 0 ≤ state.mass := by
    rw [hmass]
    apply List.prod_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact div_nonneg zero_le_one (sub_nonneg.mpr (by exact_mod_cast (hprime p hp).one_le))
  have hkernel := conservativeDensity_le_parentDensity hrow hHistory hCap
  rw [parentDensity_eq_profile] at hkernel
  have hprofile :
      4 / (current - total t) - 4 / (newCap t - total t) ≤
        (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
            ((N : ℝ) ^ current / (pre.prod : ℝ)) -
          actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
            ((N : ℝ) ^ newCap t / (pre.prod : ℝ))) *
          Real.log (N : ℝ) / singularSeries N + eta := by
    have hlo := (abs_lt.mp herr).1
    linarith only [hlo]
  have hweights : 0 ≤ ∏ i, 1 / t i :=
    Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (coordinate_pos hrow i)).le)
  have hrowLower := hkernel.trans (mul_le_mul_of_nonneg_right hprofile hweights)
  have hweighted := mul_le_mul_of_nonneg_left hrowLower hmass0
  have hdiff := P2OriginalAscendingEighthCapDictionary.actual_rank_eight_difference N cap
    (P4ASlot19ChargedFrontierSourceOnly.oldLevel (N : ℝ) lambda6)
    (P4ASlot19ChargedFrontierSourceOnly.raisedLevel (N : ℝ) lambda6) pre hgeom.1
  rw [hdiff]
  unfold P2OriginalAscendingEighthCapDictionary.actualEighthResidualDifference
  rw [← hmass]
  simp only [P4ASlot19ChargedFrontierSourceOnly.oldLevel,
    P4ASlot19ChargedFrontierSourceOnly.raisedLevel,
    P4ASlot19ChargedFrontierSourceOnly.raisedExponent]
  dsimp only
  rw [if_pos (show P4ASlot19ChargedFrontierSourceOnly.actionGuard t current from ⟨hrow, hCap⟩)]
  convert hweighted using 1 <;> ring

end
end ImbalancedChen.OriginalAscendingNineteenArithmeticResidual
