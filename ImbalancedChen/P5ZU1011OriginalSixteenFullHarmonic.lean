import ImbalancedChen.P5ZU1011OriginalSixteenReassembly
import ImbalancedChen.P5ZU1011OriginalSixteenAffineState
import ImbalancedChen.P5ZU1011OriginalSixteenCommonStatePrimeTest

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The complete-state geometry and direct PNT suppliers are independently
frozen source modules. No compiler or numerical producer was run.

The original nonlinear sixteen-policy cost is partitioned at the same
point by EVERY cap ownership, first-failed eligibility and H248 state.
The actual finite prime sum and the genuine weighted integral are glued
with this complete partition before the finite sum of proved PNT limits.
No hMean/hCellMean, minimum-of-means or moving-mask limit is used.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenFullHarmonic

noncomputable section
open Set MeasureTheory Filter Topology
open Classical
open U11Integral U11Canonical
open scoped BigOperators

abbrev State := U1011OriginalSixteenAffineState.State

def actualMinimum : LogFour → ℝ := U1011OriginalSixteenStateKernel.actualMinimum

def domain : Set LogFour := originalDomain ∅
def box : Set LogFour := logPrimeBox (fun _ : Fin 4 => (417/5000 : ℝ))
  (fun _ => (59/250 : ℝ))
def piece (s : State) : Set LogFour := domain ∩ U1011OriginalSixteenAffineState.commonCell s

theorem domain_subset_box : domain ⊆ box := by
  intro v hv
  obtain ⟨ha,h32,h21,h1,h0lo,h0hi,hm⟩ := hv
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i <;> dsimp <;> constructor <;> linarith

theorem harmonicDensity_eq_prod (v : LogFour) : harmonicDensity v=∏ i, 1/v i := by
  simp only [harmonicDensity,Fin.prod_univ_succ,Finset.prod_empty,mul_one,one_div,mul_inv_rev]
  ring

theorem measurableSet_piece (s : State) : MeasurableSet (piece s) :=
  (measurableSet_originalDomain ∅ measurableSet_empty).inter
    (U1011OriginalSixteenAffineState.measurableSet_commonCell s)

/-- Every original point owns one COMPLETE common state. The cost here
is the actual full-bank minimum itself, never a selected policy average. -/
theorem sum_piece_indicator (v : LogFour) :
    (∑ s : State, (piece s).indicator actualMinimum v) = domain.indicator actualMinimum v := by
  by_cases hd : v ∈ domain
  · let s₀ := U1011OriginalSixteenAffineState.chosenState v
    have hs₀ : v ∈ U1011OriginalSixteenAffineState.commonCell s₀ :=
      U1011OriginalSixteenAffineState.chosenState_mem v
        ((originalDomain_denominators_pos ∅ v hd).1)
    rw [Finset.sum_eq_single s₀]
    · exact (indicator_of_mem ⟨hd,hs₀⟩ _).trans (indicator_of_mem hd _).symm
    · intro s _ hne
      exact indicator_of_notMem (fun hs => hne
        (U1011OriginalSixteenAffineState.commonCell_unique hs.2 hs₀)) _
    · intro hs
      exact (hs (Finset.mem_univ _)).elim
  · rw [indicator_of_notMem hd]
    apply Finset.sum_eq_zero
    intro s _
    exact indicator_of_notMem (fun hs => hd hs.1) _

/-- Harmonic weights are attached AFTER the exact common-state
partition, so each original tuple has one occurrence and one cost. -/
theorem sum_piece_weighted_indicator (v : LogFour) :
    (∑ s : State, (piece s).indicator (fun v => actualMinimum v*harmonicDensity v) v) =
      domain.indicator (fun v => actualMinimum v*harmonicDensity v) v := by
  calc
    _ = ∑ s : State, (piece s).indicator actualMinimum v*harmonicDensity v := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hv : v ∈ piece s <;> simp [hv]
    _ = (∑ s : State, (piece s).indicator actualMinimum v)*harmonicDensity v := by
      rw [Finset.sum_mul]
    _ = domain.indicator actualMinimum v*harmonicDensity v := by
      rw [sum_piece_indicator]
    _ = _ := by
      by_cases hv : v ∈ domain <;> simp [hv]

def primeMean (N : ℕ) : ℝ := actualPrimeBoxTestSum N
  (fun _ : Fin 4 => (417/5000 : ℝ)) (fun _ => (59/250 : ℝ))
  (domain.indicator actualMinimum)
def statePrimeMean (s : State) (N : ℕ) : ℝ := actualPrimeBoxTestSum N
  (fun _ : Fin 4 => (417/5000 : ℝ)) (fun _ => (59/250 : ℝ))
  ((piece s).indicator actualMinimum)

theorem primeMean_eq_state_sum (N : ℕ) : primeMean N=∑ s : State, statePrimeMean s N := by
  unfold primeMean statePrimeMean actualPrimeBoxTestSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [←Finset.mul_sum,sum_piece_indicator]

theorem integrableOn_actual_weighted :
    IntegrableOn (fun v => actualMinimum v*harmonicDensity v) domain volume :=
  U1011OriginalSixteenReassembly.integrableOn_weighted_actualMinimum ∅ measurableSet_empty

theorem integral_eq_complete_state_sum :
    (∫ v in domain, actualMinimum v*harmonicDensity v)=
      ∑ s : State, ∫ v in box ∩ piece s, actualMinimum v*∏ i, 1/v i := by
  have hi (s : State) : IntegrableOn ((piece s).indicator
      (fun v => actualMinimum v*harmonicDensity v)) box volume := by
    apply (integrable_indicator_iff (measurableSet_piece s)).2
    have hsub : box ∩ piece s ⊆ domain := fun v hv => hv.2.1
    have hh := integrableOn_actual_weighted.mono_set hsub
    simpa only [IntegrableOn,Measure.restrict_restrict (measurableSet_piece s),inter_comm] using hh
  calc
    _ = ∫ v in box, domain.indicator (fun v => actualMinimum v*harmonicDensity v) v := by
      rw [setIntegral_indicator (measurableSet_originalDomain ∅ measurableSet_empty)]
      have heq : box ∩ domain=domain := inter_eq_right.mpr domain_subset_box
      rw [heq]
    _ = ∫ v in box, ∑ s : State,
        (piece s).indicator (fun v => actualMinimum v*harmonicDensity v) v := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun v => (sum_piece_weighted_indicator v).symm)
    _ = ∑ s : State, ∫ v in box,
        (piece s).indicator (fun v => actualMinimum v*harmonicDensity v) v := by
      apply integral_finsetSum
      intro s _
      exact hi s
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [setIntegral_indicator (measurableSet_piece s)]
      apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter (measurableSet_piece s))
      intro v _
      rw [harmonicDensity_eq_prod]

/-- Complete ORIGINAL16 unmasked harmonic mean. Each state mean below
is a proved direct PNT supplier with actual nonlinear clipped cost, not a
hypothesis of this theorem. The eligibility and H248 minimum are never
interchanged with averaging. -/
theorem tendsto_actual_original_full_sixteen_mean :
    Tendsto primeMean atTop (𝓝 (∫ v in domain, actualMinimum v*harmonicDensity v)) := by
  rw [integral_eq_complete_state_sum]
  have hstate (s : State) :=
    U1011OriginalSixteenCommonStatePrimeTest.tendsto_original_sixteen_commonCell s
  have ht := tendsto_finsetSum (Finset.univ : Finset State) (fun s _ => hstate s)
  have ht' : Tendsto (fun N : ℕ => ∑ s : State, statePrimeMean s N) atTop
      (𝓝 (∑ s : State, ∫ v in box ∩ piece s, actualMinimum v*∏ i, 1/v i)) := by
    simpa only [statePrimeMean,box,piece,domain,actualMinimum,
      U1011OriginalSixteenAffineState.originalCell] using ht
  have heq : primeMean=(fun N : ℕ => ∑ s : State, statePrimeMean s N) := by
    funext N
    exact primeMean_eq_state_sum N
  rw [heq]
  exact ht'

end
end ImbalancedChen.P5Z.U1011OriginalSixteenFullHarmonic



