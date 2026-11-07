import ImbalancedChen.P5ZU1011OriginalSixteenU10Geometry

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Direct full16 nonlinear H248 harmonic mean on the ORIGINAL U10 low-fourth
band. The five true U10 support rows and all241 actual cap/first-failure/
H248 rows form one246-row common circuit. Existing exact zero-row reduction
supplies each actual state PNT; no separate-policy minimum-of-means occurs.
The actual clipped-state identity is proved on D10 in the preceding source,
rather than passing D10 off as the U11 support. All state integrability,
finite harmonic Fubini and weighted integral gluing are constructed here.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenU10FullHarmonic

noncomputable section
open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalSixteenEligibilityState U1011OriginalSixteenMixedGatePrimeTests

abbrev State := U1011OriginalSixteenAffineState.State
abbrev GateSlot10 := Fin 5 ⊕ U1011OriginalSixteenAffineState.CommonGateSlot

def domain : Set LogFour := U1011OriginalSixteenU10Geometry.domain10
def box : Set LogFour := U1011OriginalSixteenFullHarmonic.box
def actualMinimum : LogFour → ℝ := U1011OriginalSixteenStateKernel.actualMinimum

def piece (s : State) : Set LogFour := domain ∩ U1011OriginalSixteenAffineState.commonCell s

def gates (s : State) : GateSlot10 → MixedGate
  | .inl i => U1011OriginalSixteenU10Geometry.supportGates i
  | .inr k => U1011OriginalSixteenAffineState.commonGates s k

theorem piece_eq_mixed (s : State) : piece s=mixedRegion (gates s) := by
  ext v
  constructor
  · rintro ⟨hd,hs⟩ k
    cases k with
    | inl i =>
        have hh : v ∈ mixedRegion U1011OriginalSixteenU10Geometry.supportGates := by
          rw [←U1011OriginalSixteenU10Geometry.domain10_eq_mixed]
          exact hd
        exact hh i
    | inr k =>
        have hh : v ∈ U1011OriginalSixteenAffineState.commonAffineCell s := by
          rw [←U1011OriginalSixteenAffineState.commonCell_eq_affineCell]
          exact hs
        exact hh k
  · intro h
    constructor
    · rw [domain,U1011OriginalSixteenU10Geometry.domain10_eq_mixed]
      exact fun i => h (.inl i)
    · rw [U1011OriginalSixteenAffineState.commonCell_eq_affineCell]
      exact fun k => h (.inr k)

theorem measurableSet_piece (s : State) : MeasurableSet (piece s) := by
  rw [piece_eq_mixed]
  exact measurableSet_mixedRegion _

theorem actual_eq_kernel {s : State} {v : LogFour} (hv : v ∈ piece s) :
    actualMinimum v=U1011OriginalSixteenStateKernel.frozenMinimum
      (U1011OriginalSixteenAffineState.kernelState s) v :=
  U1011OriginalSixteenU10Geometry.actualMinimum_eq_frozen_D10 _ hv.1
    (U1011OriginalSixteenAffineState.commonCell_subset_kernelState s hv.2)

/-- Direct actual D10 nonlinear state PNT: only the finite STATE is an
argument. Every support, state, zero-row and properness input is discharged. -/
theorem tendsto_actual_state (s : State) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 4 => (417/5000 : ℝ))
      (fun _ => (59/250 : ℝ)) ((piece s).indicator actualMinimum)) atTop
      (𝓝 (∫ v in box ∩ piece s, actualMinimum v*∏ i,1/v i)) := by
  have hc : ContinuousOn (U1011OriginalSixteenStateKernel.frozenMinimum
      (U1011OriginalSixteenAffineState.kernelState s))
      (univ.pi (fun _ : Fin 4 => Icc (417/5000 : ℝ) (59/250 : ℝ))) := by
    apply (U1011OriginalSixteenStateKernel.continuousOn_frozenMinimum _).mono
    intro v hv
    exact ⟨fun j => (hv j (mem_univ j)).1,fun j => (hv j (mem_univ j)).2⟩
  have ht := tendsto_actualPrimeBox_mixedRegion (gates s)
    (U1011OriginalSixteenStateKernel.frozenMinimum (U1011OriginalSixteenAffineState.kernelState s)) hc
  rw [←piece_eq_mixed s] at ht
  have hind : (piece s).indicator actualMinimum=(piece s).indicator
      (U1011OriginalSixteenStateKernel.frozenMinimum (U1011OriginalSixteenAffineState.kernelState s)) := by
    funext v
    by_cases hv : v ∈ piece s
    · simp only [indicator_of_mem hv,actual_eq_kernel hv]
    · simp only [indicator_of_notMem hv]
  have hint : (∫ v in box ∩ piece s,
      U1011OriginalSixteenStateKernel.frozenMinimum (U1011OriginalSixteenAffineState.kernelState s) v*∏ i,1/v i)=
      ∫ v in box ∩ piece s,actualMinimum v*∏ i,1/v i := by
    apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter (measurableSet_piece s))
    intro v hv
    rw [actual_eq_kernel hv.2]
  rw [hind,←hint]
  exact ht

theorem sum_piece_indicator (v : LogFour) :
    (∑ s : State,(piece s).indicator actualMinimum v)=domain.indicator actualMinimum v := by
  by_cases hd : v ∈ domain
  · let s₀:=U1011OriginalSixteenAffineState.chosenState v
    have hs₀ : v ∈ U1011OriginalSixteenAffineState.commonCell s₀ :=
      U1011OriginalSixteenAffineState.chosenState_mem v
        (U1011OriginalSixteenU10Geometry.domain10_smallest_pos hd)
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

theorem sum_piece_weighted_indicator (v : LogFour) :
    (∑ s : State,(piece s).indicator (fun v => actualMinimum v*harmonicDensity v) v)=
      domain.indicator (fun v => actualMinimum v*harmonicDensity v) v := by
  calc
    _ = ∑ s : State,(piece s).indicator actualMinimum v*harmonicDensity v := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hv : v ∈ piece s <;> simp [hv]
    _ = (∑ s : State,(piece s).indicator actualMinimum v)*harmonicDensity v := by rw [Finset.sum_mul]
    _ = domain.indicator actualMinimum v*harmonicDensity v := by rw [sum_piece_indicator]
    _ = _ := by by_cases hv : v ∈ domain <;> simp [hv]

theorem integrable_piece_weighted_indicator (s : State) :
    Integrable ((piece s).indicator (fun v => actualMinimum v*harmonicDensity v)) := by
  have hc := (U1011OriginalSixteenStateKernel.continuousOn_frozenMinimum
    (U1011OriginalSixteenAffineState.kernelState s)).mul continuousOn_harmonicDensity_compactBox
  have hi := (hc.integrableOn_compact isCompact_compactBox).mono_set
    (show piece s ⊆ compactBox from fun v hv => U1011OriginalSixteenU10Geometry.domain10_subset_compactBox hv.1)
  have hg := hi.integrable_indicator (measurableSet_piece s)
  have heq : (piece s).indicator (fun v => actualMinimum v*harmonicDensity v)=
      (piece s).indicator (fun v => U1011OriginalSixteenStateKernel.frozenMinimum
        (U1011OriginalSixteenAffineState.kernelState s) v*harmonicDensity v) := by
    funext v
    by_cases hv : v ∈ piece s
    · simp only [indicator_of_mem hv,actual_eq_kernel hv]
    · simp only [indicator_of_notMem hv]
  rw [heq]
  exact hg

def primeMean10 (N : ℕ) : ℝ := actualPrimeBoxTestSum N (fun _ : Fin 4 => (417/5000 : ℝ))
  (fun _ => (59/250 : ℝ)) (domain.indicator actualMinimum)

def statePrimeMean (s : State) (N : ℕ) : ℝ := actualPrimeBoxTestSum N
  (fun _ : Fin 4 => (417/5000 : ℝ)) (fun _ => (59/250 : ℝ)) ((piece s).indicator actualMinimum)

def integral10 : ℝ := ∫ v in domain,actualMinimum v*harmonicDensity v

theorem primeMean10_eq_state_sum (N : ℕ) : primeMean10 N=∑ s : State,statePrimeMean s N := by
  unfold primeMean10 statePrimeMean actualPrimeBoxTestSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [←Finset.mul_sum,sum_piece_indicator]

theorem integral10_eq_state_sum : integral10=∑ s : State,∫ v in box ∩ piece s,actualMinimum v*∏ i,1/v i := by
  calc
    integral10=∫ v,domain.indicator (fun v => actualMinimum v*harmonicDensity v) v :=
      (integral_indicator U1011OriginalSixteenU10Geometry.measurableSet_domain10).symm
    _ = ∫ v,∑ s : State,(piece s).indicator (fun v => actualMinimum v*harmonicDensity v) v := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun v => (sum_piece_weighted_indicator v).symm)
    _ = ∑ s : State,∫ v,(piece s).indicator (fun v => actualMinimum v*harmonicDensity v) v :=
      integral_finsetSum _ (fun s _ => integrable_piece_weighted_indicator s)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_indicator (measurableSet_piece s)]
      have hsub : piece s ⊆ box := fun v hv => U1011OriginalSixteenU10Geometry.domain10_subset_box hv.1
      have heq : box ∩ piece s=piece s := inter_eq_right.mpr hsub
      rw [heq]
      apply setIntegral_congr_fun (measurableSet_piece s)
      intro v _
      rw [U1011OriginalSixteenFullHarmonic.harmonicDensity_eq_prod]

/-- Original low-band full16 nonlinear harmonic limit, from direct named
state PNTs and exact finite gluing, without any hMean/hCellMean premise. -/
theorem tendsto_primeMean10 : Tendsto primeMean10 atTop (𝓝 integral10) := by
  rw [integral10_eq_state_sum]
  have ht := tendsto_finsetSum (Finset.univ : Finset State) (fun s _ => tendsto_actual_state s)
  have ht' : Tendsto (fun N : ℕ => ∑ s : State,statePrimeMean s N) atTop
      (𝓝 (∑ s : State,∫ v in box ∩ piece s,actualMinimum v*∏ i,1/v i)) := ht
  have heq : primeMean10=(fun N : ℕ => ∑ s : State,statePrimeMean s N) := by
    funext N
    exact primeMean10_eq_state_sum N
  rw [heq]
  exact ht'

/-- The mean belongs to the literal Y10 four-prime source and its true
full-product reciprocal totient, rather than merely a log-box surrogate. -/
theorem tendsto_native10 :
    Tendsto (fun N : ℕ => U1011OriginalSixteenU10Geometry.native10 N actualMinimum) atTop (𝓝 integral10) := by
  have heq : primeMean10 =ᶠ[atTop] (fun N : ℕ => U1011OriginalSixteenU10Geometry.native10 N actualMinimum) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact (U1011OriginalSixteenU10Geometry.native10_eq_actualPrimeBox hN actualMinimum).symm
  exact tendsto_primeMean10.congr' heq

end
end ImbalancedChen.P5Z.U1011OriginalSixteenU10FullHarmonic
