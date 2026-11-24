import ImbalancedChen.P2OriginalFourteenSignedParentLedger
import ImbalancedChen.P4AActualEighthInheritedHistoryGuard
import ImbalancedChen.P1ActualUpperClosedParameterUniformity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One arithmetic threshold for all fourteen saving16 cells and all actual
inherited sixth caps. This strengthens the old point-dependent threshold:
N0 is chosen before the policy, cap, state, point, and cell label. The H7
lower guard is derived from actual frontier membership. The resulting
ordinary profile is the original coefficient-four saving; its prime
Riemann sum and historical 2^96 endpoint remain separate obligations.
-/
namespace ImbalancedChen.P2OriginalFourteenUniformResidual
noncomputable section
open scoped Classical BigOperators
open P2OriginalAscendingEighthCapDictionary VariableEnvelope
open P4AOriginalEighthParentPhysicalLedger

private def window : Set (ℝ × ℝ) :=
  (Set.Icc (53 / 13824) (3 * mu) ×ˢ Set.Icc (53 / 13824) mu) ∩
    {q | q.1 ≤ 3 * q.2}

private theorem window_error (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y lambda beta u : ℝ, 0 < P → 0 < y →
      actualRosserQuotientParameters (N : ℝ) P y lambda = (beta, u) →
      53 / 13824 ≤ u → u ≤ mu → u ≤ beta → beta ≤ 3 * u →
      ∀ cap : ℕ, y ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ lambda / P) *
          Real.log (N : ℝ) / singularSeries N - 4 / beta| < epsilon := by
  have hcompact : IsCompact window :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_fst (continuous_const.mul continuous_snd))
  have hlegal : ∀ q ∈ window, 0 < q.2 ∧ 0 < q.1 ∧ q.1 ≤ 3 * q.2 := by
    intro q hq
    exact ⟨lt_of_lt_of_le (by norm_num) hq.1.2.1,
      lt_of_lt_of_le (by norm_num) hq.1.1.1, hq.2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_cube_compact_normalized_threshold
      window hcompact hlegal epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y lambda beta u hP hy hparams hau hub hubeta hbeta cap hcap
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hlevel, hcut⟩ :=
    actualRosserQuotientParameters_exact (N : ℝ) P y lambda hNr hP hy
  rw [hparams] at hlevel hcut
  have hmem : (beta, u) ∈ window :=
    ⟨⟨⟨hau.trans hubeta, hbeta.trans (by linarith)⟩, ⟨hau, hub⟩⟩, hbeta⟩
  have h := hbound N hN hEven (beta, u) hmem cap (by simpa only [hcut] using hcap)
  simpa only [hlevel, hcut] using h

/-- Uniform original comparison gain for every physical saving16 point.
The only analytical input is the established actual ordinary density
limit on one fixed compact residual window. -/
theorem exists_uniform_comparison_gain (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (planes : Finset (Fin 6) → Bool) (t : Point) (current P y : ℝ),
      CellGuard planes t → CurrentParentGuard t current → 0 < P → 0 < y →
      Real.log P / Real.log (N : ℝ) = S t →
      Real.log y / Real.log (N : ℝ) = t 7 →
      ∀ cap : ℕ, y ≤ (cap : ℝ) →
        sourceGain (R t) (M t) t - epsilon <
          (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current / P) -
            actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P)) *
              Real.log (N : ℝ) / singularSeries N := by
  obtain ⟨N0, hN0, hbound⟩ := window_error (epsilon / 2) (half_pos hepsilon)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven planes t current P y hcell hcurrent hP hy hlogP hlogy cap hcap
  have hp := residual_parameter_range hcell current hcurrent
  have hub : t 7 ≤ mu :=
    (hcell.order (by decide : (0 : Fin 8) < 7)).le.trans hcell.largest.le
  have hparams (lambda : ℝ) :
      actualRosserQuotientParameters (N : ℝ) P y lambda = (lambda - S t, t 7) := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
  have hold := hbound N hN hEven P y current (current - S t) (t 7)
    hP hy (hparams current) hcell.compact_cutoff.le hub hp.2.1.le hp.2.2.1 cap hcap
  have hnew := hbound N hN hEven P y (M t) (M t - S t) (t 7)
    hP hy (hparams (M t)) hcell.compact_cutoff.le hub hp.2.2.2.1.le hp.2.2.2.2 cap hcap
  have hcomparison := comparison_gain_le_current hcell current hcurrent
  rw [sourceGain_eq_difference current (M t) t
    (hp.1.trans hp.2.1) (hp.1.trans hp.2.2.2.1)] at hcomparison
  have holdLower := (abs_lt.mp hold).1
  have hnewUpper := (abs_lt.mp hnew).2
  have hdistribute :
      (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current / P) -
        actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P)) *
          Real.log (N : ℝ) / singularSeries N =
      actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current / P) *
          Real.log (N : ℝ) / singularSeries N -
        actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P) *
          Real.log (N : ℝ) / singularSeries N := by ring
  rw [hdistribute]
  linarith only [hcomparison, holdLower, hnewUpper]

private theorem oddCube6_eq_history7 (t : Point) :
    oddCube t 6 = P2OriginalDescendingEighthLogSemantics.history7 t := by
  norm_num [oddCube, prefixSum, Finset.sum_filter, Fin.sum_univ_succ,
    P2OriginalDescendingEighthLogSemantics.history7]
  <;> ring

/-- Actual saving16 source, with no H7/admissibility premise. The remaining
parent upper comparison is the real inheritance obligation lambda6<=R,
not equality with a historical comparison and not an integrated saving. -/
theorem exists_uniform_actual_fourteen_frontier_gain
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool)
        (patterns : Fin 15 → Finset (Fin 6) → Bool)
        (cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ),
      state ∈ firstExitDepthFrontier 8 (parentPolicy (N : ℝ) lambda6 base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) →
      let pre := state.selectedPrefix
      let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
      let current := inheritedExponent lambda6 pre
      SelectedFamilyGuard patterns t → current ≤ R t →
        sourceGain (R t) (M t) t - epsilon <
          (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
              (currentLevel (N : ℝ) lambda6 pre / (pre.prod : ℝ)) -
            actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
              (familyNextLevel (N : ℝ) lambda6 patterns pre / (pre.prod : ℝ))) *
            Real.log (N : ℝ) / singularSeries N := by
  obtain ⟨N0, hN0, hbound⟩ := exists_uniform_comparison_gain epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven lambda6 base patterns cap z state hs
  dsimp only
  intro hfamily hupper
  let pre := state.selectedPrefix
  let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
  let current := inheritedExponent lambda6 pre
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hgeom := actualPrimeFrontier_geometry 8 (by omega)
    (parentPolicy (N : ℝ) lambda6 base) N cap z state hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8
    (parentPolicy (N : ℝ) lambda6 base) (fun p : ℕ => 1 / ((p : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z) state hs
  have hprime : ∀ p ∈ pre, Nat.Prime p := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))
  have hpos : ∀ p ∈ pre, 0 < p := fun p hp => (hprime p hp).pos
  have hhead : pre.headD 0 ∈ pre := by
    rw [← primeHistoryTuple_last hgeom.1]
    exact primeHistoryTuple_mem hgeom.1 _
  have hy : (0 : ℝ) < pre.headD 0 := by exact_mod_cast (hprime _ hhead).pos
  have hcap : (pre.headD 0 : ℝ) ≤ (cap : ℝ) := by
    exact_mod_cast (mem_roughPrimeUniverse.mp
      (hsub.subset (List.mem_reverse.mpr hhead))).1.le
  have hhistory : oddCube t 6 < current := by
    rw [oddCube6_eq_history7]
    exact P4AActualEighthInheritedHistoryGuard.actual_log_history7_lt_current
      base lambda6 N cap hNr 0 z (fun p : ℕ => 1 / ((p : ℝ) - 1)) state hs
  have hcurrent : CurrentParentGuard t current := ⟨hhistory, hupper⟩
  obtain ⟨i, hi, hcell⟩ := hfamily
  have hlog := rank_eight_log_dictionary (N : ℝ) hNr pre hgeom.1 hpos
  have h := hbound N hN hEven (patterns i) t current (pre.prod : ℝ)
    (pre.headD 0 : ℝ) hcell hcurrent hgeom.2.2.1 hy hlog.1.symm hlog.2.symm cap hcap
  have hguard : SelectedFamilyGuard patterns t ∧ CurrentParentGuard t current :=
    ⟨⟨i, hi, hcell⟩, hcurrent⟩
  simpa only [currentLevel, familyNextLevel, familyNextExponent, if_pos hguard] using h

end
end ImbalancedChen.P2OriginalFourteenUniformResidual
