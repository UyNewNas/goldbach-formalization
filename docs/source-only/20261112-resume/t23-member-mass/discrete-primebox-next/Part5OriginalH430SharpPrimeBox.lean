import ImbalancedChen.Part5OriginalH430FixedPrimeScreen
import ImbalancedChen.ActualPrimeBoxTestFunctions
import Mathlib.Topology.MetricSpace.ThickenedIndicator

namespace ImbalancedChen.Part5OriginalH430SharpPrimeBox
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators
open Part5OriginalH430PrimeRegularGerms Part5OriginalH430FixedPrimeScreen
open P2EnhancedLowerFinitePhysicalGraph Part5OriginalH430NativeQueryPaths Part5OriginalH430NativeMovingDensity
open Part5OriginalH430FixedProgramL1 Part5OriginalH430PhysicalRoots Part5OriginalH430FullMemberMeasurable
open Part5OriginalH430FrozenRootMass
open Part5OriginalUpsilon5CausalDictionary (FloorAtom)

abbrev box (r : ℕ) (a : ℝ) := logPrimeBox (fun _ : Fin r => a) (fun _ => 1)
def kernel {r : ℕ} (x : Space r) := ∏ i, 1 / x i
def total (r N : ℕ) (a : ℝ) := actualPrimeBoxMass N (fun _ : Fin r => a) (fun _ => 1)
def atomWeight {r : ℕ} (p : Fin r → ℕ) := ∏ i, 1 / ((p i : ℝ)-1)
def badMass {r : ℕ} (N : ℕ) (a : ℝ) (S : Set (Space r)) :=
  actualPrimeBoxTestSum N (fun _ : Fin r => a) (fun _ => 1) (S.indicator (fun _ => (1:ℝ)))

theorem kernel_bounds {r : ℕ} {a : ℝ} (ha : 0 < a) {x : Space r} (hx : x ∈ box r a) :
    0 ≤ kernel x ∧ kernel x ≤ (1/a)^r := by
  have h (i : Fin r) := (mem_logPrimeBox.mp hx i).1
  constructor
  · exact Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (ha.trans_le (h i))).le)
  · simpa only [kernel,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      Finset.prod_le_prod (s := Finset.univ) (fun i _ => (one_div_pos.mpr (ha.trans_le (h i))).le)
        (fun i _ => one_div_le_one_div_of_le ha (h i))

private def ramp {r} (S : Set (Space r)) (j : ℕ) (x : Space r) : ℝ :=
  thickenedIndicator (δ := (1:ℝ)/(j+1)) (by positivity) S x

private theorem ramp_cont {r} (S : Set (Space r)) (j : ℕ) : Continuous (ramp S j) :=
  NNReal.continuous_coe.comp (thickenedIndicator (δ := (1:ℝ)/(j+1)) (by positivity) S).continuous

private theorem ramp_one {r} (S : Set (Space r)) (j : ℕ) {x} (hx : x ∈ S) : ramp S j x = 1 := by
  simp only [ramp,thickenedIndicator_one _ _ hx,NNReal.coe_one]

private theorem ramp_lim {r} {S : Set (Space r)} (hS : Stable (fun x => x ∈ S)) :
    ∀ᵐ x, Tendsto (fun j => ramp S j x) atTop (𝓝 (S.indicator (fun _ => (1:ℝ)) x)) := by
  have h := thickenedIndicator_tendsto_indicator_closure
    (δseq := fun j : ℕ => (1:ℝ)/(j+1)) (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat S
  filter_upwards [hS] with x hx
  have he : x ∈ closure S ↔ x ∈ S := by
    refine ⟨fun hc => ?_,subset_closure⟩
    by_contra hn
    exact (mem_closure_iff_frequently.mp hc) (hx.mono (fun _ hy h => hn (hy.mp h)))
  have ht := NNReal.continuous_coe.continuousAt.tendsto.comp (tendsto_pi_nhds.mp h x)
  by_cases hs : x ∈ S
  · simpa only [ramp,indicator_of_mem (he.mpr hs),indicator_of_mem hs,NNReal.coe_one] using ht
  · simpa only [ramp,indicator_of_notMem (fun hc => hs (he.mp hc)),indicator_of_notMem hs,NNReal.coe_zero] using ht

/-- Discontinuous ORIGINAL Boolean indicators, with true nonnegative
prime tuple weights. The majorant is explicitly constructed on the
actual positive cube and its limiting mass is paid in ordinary volume. -/
theorem eventual_sharp_bound {r : ℕ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {S : Set (Space r)} (hm : MeasurableSet S) (hs : Stable (fun x => x ∈ S))
    (hf : volume S < ⊤) {eps : ℝ} (he : 0 < eps) :
    ∀ᶠ N in atTop, badMass N a S < (1/a)^r * volume.real S + eps := by
  let B := box r a
  have hB : MeasurableSet B := measurableSet_logPrimeBox _ _
  let g := S.indicator (fun _ => (1:ℝ))
  let I := ∫ x in B, g x * kernel x
  have hlim : Tendsto (fun j => ∫ x in B, ramp S j x * kernel x) atTop (𝓝 I) := by
    apply tendsto_integral_of_dominated_convergence kernel
    · intro j
      exact ((ramp_cont S j).measurable.mul (Finset.measurable_prod _ (fun _ _ =>
        measurable_const.div (measurable_pi_apply _)))).aestronglyMeasurable
    · exact integrableOn_logPrimeBox_one_div _ _ (fun _ => ha)
    · intro j
      filter_upwards [ae_restrict_mem hB] with x hx
      have hb := (kernel_bounds ha hx).1
      have hu : ramp S j x ≤ 1 := by
        exact_mod_cast thickenedIndicator_le_one (δ := (1:ℝ)/(j+1)) (by positivity) S x
      have h0 : 0 ≤ ramp S j x := NNReal.coe_nonneg _
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h0 hb)]
      exact (mul_le_mul_of_nonneg_right hu hb).trans_eq (one_mul _)
    · filter_upwards [ae_restrict_of_ae (ramp_lim hs)] with x hx
      exact hx.mul_const _
  have hI : I ≤ (1/a)^r * volume.real S := by
    have hInt : I = ∫ x in B ∩ S, kernel x := by
      rw [show I = ∫ x in B, S.indicator kernel x from by
        apply setIntegral_congr_fun hB
        intro x _
        by_cases hx : x ∈ S <;> simp [g,hx],setIntegral_indicator hm]
    have hb : volume (B ∩ S) < ⊤ := lt_of_le_of_lt (measure_mono inter_subset_right) hf
    rw [hInt]
    have hh := norm_setIntegral_le_of_norm_le_const (f := kernel) hb (fun x hx => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (kernel_bounds ha hx.1).1] using (kernel_bounds ha hx.1).2)
    have hvol : volume.real (B ∩ S) ≤ volume.real S := ENNReal.toReal_mono hf.ne (measure_mono inter_subset_right)
    exact (le_abs_self _).trans (hh.trans (mul_le_mul_of_nonneg_left hvol (pow_nonneg (by positivity) _)))
  obtain ⟨j,hj⟩ := (hlim.eventually (eventually_lt_nhds (show I < I+eps/2 by linarith))).exists
  have hp := tendsto_actualPrimeBoxTestSum_cube ha ha1 (ramp S j) (ramp_cont S j).continuousOn
  filter_upwards [hp.eventually (eventually_lt_nhds (show
    (∫ x in B, ramp S j x * kernel x) < (1/a)^r * volume.real S + eps by linarith))] with N hN
  apply lt_of_le_of_lt _ hN
  unfold badMass actualPrimeBoxTestSum
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (actualPrimeBoxWeight_nonneg hp)
  by_cases hx : actualPrimeTupleLog N p ∈ S
  · simp only [indicator_of_mem hx,ramp_one S j hx,le_refl]
  · simp only [indicator_of_notMem hx]
    exact NNReal.coe_nonneg _

def screen {r mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool) (atom : FloorAtom) (n : ℕ) :
    Set (Space r) := view e ⁻¹' (region k (shapes code) ∩ fixedDifference k code lower atom n)

theorem view_preserves {r : ℕ} {ι : Type*} [Fintype ι] (e : Fin r ≃ ι) :
    MeasurePreserving (view e) := by
  have he : view e = (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e : Space r → (ι → ℝ)) := by
    funext x i
    obtain ⟨j,rfl⟩ := e.surjective i
    simp only [view,e.symm_apply_apply,MeasurableEquiv.piCongrLeft_apply_apply]
  rw [he]
  exact volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e

theorem screen_regular {r mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool) (atom : FloorAtom) (n : ℕ) :
    MeasurableSet (screen k code e lower atom n) ∧
    Stable (fun x => x ∈ screen k code e lower atom n) ∧
    volume (screen k code e lower atom n) =
      volume (region k (shapes code) ∩ fixedDifference k code lower atom n) := by
  have hmI := fixedSet_measurable k code lower atom none
  have hmS := fixedSet_measurable k code lower atom (some n)
  have hmD : MeasurableSet (fixedDifference k code lower atom n) := (hmI.diff hmS).union (hmS.diff hmI)
  have hmB : MeasurableSet (region k (shapes code)) := measurableSet_Icc.inter
    ((rootBand_measurable k).preimage (measurable_pi_apply (.inl ())))
  refine ⟨(hmB.inter hmD).preimage (view_preserves e).measurable,?_,
    (view_preserves e).measure_preimage (hmB.inter hmD).nullMeasurableSet⟩
  have hcoord (i : NativeSlot (shapes code)) :=
    ((pw_const 0).le (pw_coord (e.symm i))).and ((pw_coord (e.symm i)).le (pw_const 1))
  have cube : Stable (fun x => view e x ∈ Icc (fun _ => (0:ℝ)) (fun _ => (1:ℝ))) := by
    filter_upwards [Filter.eventually_all.mpr hcoord] with x hx
    filter_upwards [Filter.eventually_all.mpr hx] with y hy
    change ((∀ i, 0 ≤ y (e.symm i)) ∧ (∀ i, y (e.symm i) ≤ 1)) ↔
      ((∀ i, 0 ≤ x (e.symm i)) ∧ (∀ i, x (e.symm i) ≤ 1))
    constructor <;> rintro ⟨hl,hu⟩
    · exact ⟨fun i => ((hy i).mp ⟨hl i,hu i⟩).1,fun i => ((hy i).mp ⟨hl i,hu i⟩).2⟩
    · exact ⟨fun i => ((hy i).mpr ⟨hl i,hu i⟩).1,fun i => ((hy i).mpr ⟨hl i,hu i⟩).2⟩
  exact (cube.and (rootBand_stable k code e)).and (difference_stable k code e lower atom n)

/-- Original fixed Program first, original frozen precision next, then
an arithmetic threshold at that precision. This is a sum over coprime
actual prime tuples, with the original strict/closed Member tests. -/
theorem fixed_screen_primebox {r mesh d : ℕ} (hd : d ≤ 440) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool) (atom : FloorAtom) {a eps : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (he : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop, badMass N a (screen k code e lower atom n) < eps := by
  let C := (1/a)^r
  have hC : 0 < C := pow_pos (one_div_pos.mpr ha) _
  obtain ⟨T,hT⟩ := all_fixed_program_threshold mesh (div_pos (half_pos he) hC)
  filter_upwards [eventually_ge_atTop T] with n hn
  have hs := screen_regular k code e lower atom n
  have hv := (hT n hn d hd code k lower atom).2
  have heq := congrArg ENNReal.toReal hs.2.2
  change volume.real (screen k code e lower atom n) = _ at heq
  have hB : volume (region k (shapes code)) < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  have hf : volume (screen k code e lower atom n) < ⊤ := hs.2.2.trans_lt
    (lt_of_le_of_lt (measure_mono inter_subset_left) hB)
  filter_upwards [eventual_sharp_bound ha ha1 hs.1 hs.2.1 hf (half_pos he)] with N hN
  have hsmall := (lt_div_iff₀ hC).mp hv
  change badMass N a _ < C * volume.real _ + eps/2 at hN
  rw [heq,mul_comm C] at hN
  linarith only [hN,hsmall]

end
end ImbalancedChen.Part5OriginalH430SharpPrimeBox
