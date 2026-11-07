import ImbalancedChen.P1HistoricalFourthResidualIntegral
import ImbalancedChen.ActualRosserInitialResidualSaving
import ImbalancedChen.P1FourthNearOneKernel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Vanishing continuous strips at the fourth PLUS legality wall

The strip is on the same historical fourth joint cell.  Its volume is
bounded by delta times a three-dimensional box volume, using the literal
coefficient one of t0 in the legality form.  For delta <= 2a the genuine
upper profile is exactly 4/(lambda - sum t), hence bounded on t4 >= a.
No actual finite-density domination near residual one is assumed here.
-/

namespace ImbalancedChen
noncomputable section
open MeasureTheory Filter Topology Set
open scoped Classical BigOperators ENNReal

def fourthPlusWallGapP1 (lambda : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  lambda - (∑ i, t i) - t (Fin.last 3)

def fourthPlusNearWallBoxP1 (a b lambda delta : ℝ) : Set (Fin 4 → ℝ) :=
  logPrimeBox (fun _ => a) (fun _ => b) ∩
    {t | 0 < fourthPlusWallGapP1 lambda t ∧ fourthPlusWallGapP1 lambda t < delta}

theorem measurableSet_fourthPlusNearWallBoxP1 (a b lambda delta : ℝ) :
    MeasurableSet (fourthPlusNearWallBoxP1 a b lambda delta) := by
  have hc : Continuous (fourthPlusWallGapP1 lambda) := by
    unfold fourthPlusWallGapP1
    fun_prop
  exact (measurableSet_logPrimeBox _ _).inter
    ((isOpen_lt continuous_const hc).measurableSet.inter
      (isOpen_lt hc continuous_const).measurableSet)

private def fourthStripFiberP1 (a b lambda delta : ℝ) : Set (ℝ × (Fin 3 → ℝ)) :=
  {q | q.2 ∈ Set.univ.pi (fun _ => Set.Icc a b) ∧
    lambda - q.2 0 - q.2 1 - 2 * q.2 2 - delta ≤ q.1 ∧
    q.1 ≤ lambda - q.2 0 - q.2 1 - 2 * q.2 2}

private theorem measurableSet_fourthStripFiberP1 (a b lambda delta : ℝ) :
    MeasurableSet (fourthStripFiberP1 a b lambda delta) := by
  have hcube : MeasurableSet (Set.univ.pi (fun _ : Fin 3 => Set.Icc a b)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  exact (hcube.preimage measurable_snd).inter
    ((isClosed_le (by fun_prop) continuous_fst).measurableSet.inter
      (isClosed_le continuous_fst (by fun_prop)).measurableSet)

private theorem fourthStripFiber_volumeP1 (a b lambda delta : ℝ) :
    volume (fourthStripFiberP1 a b lambda delta) =
      ENNReal.ofReal delta * (ENNReal.ofReal (b - a)) ^ 3 := by
  let C : Set (Fin 3 → ℝ) := Set.univ.pi (fun _ => Set.Icc a b)
  have hC : MeasurableSet C := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hvolC : volume C = (ENNReal.ofReal (b - a)) ^ 3 := by
    rw [C, volume_pi_pi, Fin.prod_univ_three]
    simp only [Real.volume_Icc]
    ring
  have hfiber (y : Fin 3 → ℝ) :
      volume ((fun x : ℝ => (x, y)) ⁻¹' fourthStripFiberP1 a b lambda delta) =
        C.indicator (fun _ => ENNReal.ofReal delta) y := by
    by_cases hy : y ∈ C
    · have heq : ((fun x : ℝ => (x, y)) ⁻¹' fourthStripFiberP1 a b lambda delta) =
          Set.Icc (lambda - y 0 - y 1 - 2 * y 2 - delta)
            (lambda - y 0 - y 1 - 2 * y 2) := by
        ext x
        simp only [Set.mem_preimage, fourthStripFiberP1, Set.mem_setOf_eq,
          Set.mem_Icc]
        exact and_iff_right hy
      rw [heq, Set.indicator_of_mem hy, Real.volume_Icc]
      congr 1
      ring
    · have heq : ((fun x : ℝ => (x, y)) ⁻¹' fourthStripFiberP1 a b lambda delta) = ∅ := by
        ext x
        simp only [Set.mem_preimage, fourthStripFiberP1, Set.mem_setOf_eq, Set.mem_empty_iff_false]
        exact ⟨fun h => hy h.1, False.elim⟩
      rw [heq, measure_empty, Set.indicator_of_notMem hy]
  change (volume.prod volume) (fourthStripFiberP1 a b lambda delta) = _
  rw [Measure.prod_apply_symm (measurableSet_fourthStripFiberP1 a b lambda delta)]
  simp_rw [hfiber]
  rw [lintegral_indicator hC]
  simp only [lintegral_const, Measure.restrict_apply_univ, hvolC]

/-- Quantitative volume estimate, before restricting to the joint cell.
The first coordinate has coefficient one, so no dimension-dependent
coarea constant is hidden in the bound. -/
theorem fourthPlusNearWallBox_volume_leP1 (a b lambda delta : ℝ)
    (hab : a ≤ b) (hdelta : 0 ≤ delta) :
    volume (fourthPlusNearWallBoxP1 a b lambda delta) ≤
      ENNReal.ofReal (delta * (b - a) ^ 3) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) (0 : Fin 4)
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) (0 : Fin 4)
  have hsub : fourthPlusNearWallBoxP1 a b lambda delta ⊆
      e ⁻¹' fourthStripFiberP1 a b lambda delta := by
    intro t ht
    have hsum : (∑ i, t i) + t (Fin.last 3) = t 0 + t 1 + t 2 + 2 * t 3 := by
      simp [Fin.sum_univ_succ] <;> ring
    have hg0 := ht.2.1
    have hgd := ht.2.2
    unfold fourthPlusWallGapP1 at hg0 hgd
    rw [show lambda - (∑ i, t i) - t (Fin.last 3) =
      lambda - ((∑ i, t i) + t (Fin.last 3)) by ring, hsum] at hg0 hgd
    change e t ∈ fourthStripFiberP1 a b lambda delta
    refine ⟨?_, ?_, ?_⟩
    · intro i _hi
      change a ≤ t i.succ ∧ t i.succ ≤ b
      exact ⟨(mem_logPrimeBox.mp ht.1 i.succ).1, (mem_logPrimeBox.mp ht.1 i.succ).2.le⟩
    · change lambda - t 1 - t 2 - 2 * t 3 - delta ≤ t 0
      linarith
    · change t 0 ≤ lambda - t 1 - t 2 - 2 * t 3
      linarith
  calc
    volume (fourthPlusNearWallBoxP1 a b lambda delta) ≤
        volume (e ⁻¹' fourthStripFiberP1 a b lambda delta) := measure_mono hsub
    _ = volume (fourthStripFiberP1 a b lambda delta) := by
      rw [← Measure.map_apply e.measurable (measurableSet_fourthStripFiberP1 a b lambda delta)]
      exact congrArg (fun mu => mu (fourthStripFiberP1 a b lambda delta)) hmp.map_eq
    _ = ENNReal.ofReal delta * (ENNReal.ofReal (b - a)) ^ 3 := fourthStripFiber_volumeP1 _ _ _ _
    _ = ENNReal.ofReal (delta * (b - a) ^ 3) := by
      rw [ENNReal.ofReal_mul hdelta, ENNReal.ofReal_pow (sub_nonneg.mpr hab)]

/-- Near residual one the literal upper profile has the exact rational
formula supplied by uniqueness of the actual Rosser density limits. -/
theorem fourthPlusProfile_nearWall_eqP1 {a b lambda delta : ℝ}
    (ha : 0 < a) (hdelta : delta ≤ 2 * a)
    {t : Fin 4 → ℝ} (ht : t ∈ fourthPlusNearWallBoxP1 a b lambda delta) :
    fourthPlusProfileP1 lambda t = 4 / (lambda - ∑ i, t i) := by
  have hu : 0 < t (Fin.last 3) := ha.trans_le (mem_logPrimeBox.mp ht.1 _).1
  have hau : a ≤ t (Fin.last 3) := (mem_logPrimeBox.mp ht.1 _).1
  have hg0 := ht.2.1
  have hgd := ht.2.2
  unfold fourthPlusWallGapP1 at hg0 hgd
  exact normalized_suzukiUpperFactor_initial _ _ hu (by linarith) (by linarith)

/-- The independently supplied closed upper kernel also bounds the raw
profile on every strict legal strip, with no restriction on its width. -/
theorem fourthPlusNearWall_profile_abs_le_closedP1 {a b lambda delta : ℝ}
    (ha : 0 < a) {t : Fin 4 → ℝ}
    (ht : t ∈ fourthPlusNearWallBoxP1 a b lambda delta) :
    |fourthPlusProfileP1 lambda t| ≤ 4 / a := by
  have hu : 0 < t (Fin.last 3) := ha.trans_le (mem_logPrimeBox.mp ht.1 _).1
  have hgap := ht.2.1
  unfold fourthPlusWallGapP1 at hgap
  have hs : 1 < P1FourthNearOneKernel.residual lambda t := by
    apply (one_lt_div hu).mpr
    linarith
  have hlegal : t ∈ P1FourthNearOneKernel.legal a lambda :=
    ⟨(mem_logPrimeBox.mp ht.1 _).1, by linarith⟩
  have heq : P1FourthNearOneKernel.density lambda t = fourthPlusProfileP1 lambda t :=
    P1FourthNearOneKernel.density_eq_actual lambda t hs
  rw [← heq]
  exact P1FourthNearOneKernel.abs_density_le ha hlegal

def fourthNearWallKernelBoundP1 (a : ℝ) : ℝ := (4 / a) * (1 / a) ^ 4

theorem fourthNearWallKernelBound_nonnegP1 {a : ℝ} (ha : 0 < a) :
    0 ≤ fourthNearWallKernelBoundP1 a := by
  unfold fourthNearWallKernelBoundP1
  positivity

theorem fourthPlusNearWall_kernel_abs_leP1 {a b lambda delta : ℝ}
    (ha : 0 < a) (hdelta : delta ≤ 2 * a)
    {t : Fin 4 → ℝ} (ht : t ∈ fourthPlusNearWallBoxP1 a b lambda delta) :
    |fourthPlusProfileP1 lambda t * ∏ i, 1 / t i| ≤ fourthNearWallKernelBoundP1 a := by
  have hti (i : Fin 4) : 0 < t i := ha.trans_le (mem_logPrimeBox.mp ht.1 i).1
  have hbeta : a ≤ lambda - ∑ i, t i := by
    have hgap := ht.2.1
    unfold fourthPlusWallGapP1 at hgap
    linarith [(mem_logPrimeBox.mp ht.1 (Fin.last 3)).1]
  have hbeta0 : 0 < lambda - ∑ i, t i := ha.trans_le hbeta
  have hratio : 4 / (lambda - ∑ i, t i) ≤ 4 / a := by
    exact div_le_div_of_nonneg_left (by norm_num) ha hbeta
  have hprod : (∏ i, 1 / t i) ≤ (1 / a) ^ 4 := by
    calc
      _ ≤ ∏ _i : Fin 4, 1 / a := Finset.prod_le_prod
        (fun i _ => (one_div_pos.mpr (hti i)).le)
        (fun i _ => one_div_le_one_div_of_le ha (mem_logPrimeBox.mp ht.1 i).1)
      _ = _ := by simp
  rw [fourthPlusProfile_nearWall_eqP1 ha hdelta ht,
    abs_of_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hti i)).le)))]
  exact mul_le_mul hratio hprod
    (Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hti i)).le)) (by positivity)

/-- The real integral is genuinely integrable, using equality to a
continuous clipped rational profile on this exact strip. -/
theorem integrableOn_fourthPlusNearWall_kernelP1 {a b lambda delta : ℝ}
    (ha : 0 < a) (hdelta : delta ≤ 2 * a) :
    IntegrableOn (fun t : Fin 4 → ℝ => fourthPlusProfileP1 lambda t * ∏ i, 1 / t i)
      (fourthPlusNearWallBoxP1 a b lambda delta) := by
  let f : (Fin 4 → ℝ) → ℝ := fun t => 4 / max a (lambda - ∑ i, t i)
  have hf : Continuous f := by
    apply continuous_const.div (by dsimp; fun_prop)
    intro t
    exact (ha.trans_le (le_max_left _ _)).ne'
  have hi := (integrableOn_logPrimeBox_test_cube ha f hf.continuousOn).mono_set
    (show fourthPlusNearWallBoxP1 a b lambda delta ⊆
      logPrimeBox (fun _ : Fin 4 => a) (fun _ => b) from fun _ ht => ht.1)
  apply hi.congr_fun ?_ (measurableSet_fourthPlusNearWallBoxP1 a b lambda delta)
  intro t ht
  have hbeta : a ≤ lambda - ∑ i, t i := by
    have hgap := ht.2.1
    unfold fourthPlusWallGapP1 at hgap
    linarith [(mem_logPrimeBox.mp ht.1 (Fin.last 3)).1]
  rw [fourthPlusProfile_nearWall_eqP1 ha hdelta ht]
  simp only [f, max_eq_right hbeta]

namespace HistoricalPrefixCapData

def fourthJointNearWallStripP1 (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : Set (Fin 4 → ℝ) :=
  (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
    primeAffineGateRegion p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)) ∩
      {t | 0 < fourthPlusWallGapP1 (D.old4 j : ℝ) t ∧
        fourthPlusWallGapP1 (D.old4 j : ℝ) t < delta}

theorem measurableSet_fourthJointNearWallStripP1 (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    MeasurableSet (D.fourthJointNearWallStripP1 j delta) := by
  have hc : Continuous (fourthPlusWallGapP1 (D.old4 j : ℝ)) := by
    unfold fourthPlusWallGapP1
    fun_prop
  exact ((measurableSet_logPrimeMeshCell _ _ _ _).inter
    (measurableSet_primeAffineGateRegion _ _)).inter
      ((isOpen_lt continuous_const hc).measurableSet.inter
        (isOpen_lt hc continuous_const).measurableSet)

theorem fourthJointNearWallStrip_subset_boxP1 (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    D.fourthJointNearWallStripP1 j delta ⊆
      fourthPlusNearWallBoxP1 (D.a : ℝ) (D.b : ℝ) (D.old4 j : ℝ) delta := by
  intro t ht
  exact ⟨logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht.1.1, ht.2⟩

theorem fourthJointNearWallStrip_volume_leP1 (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) (hdelta : 0 ≤ delta) :
    volume (D.fourthJointNearWallStripP1 j delta) ≤
      ENNReal.ofReal (delta * ((D.b : ℝ) - D.a) ^ 3) := by
  exact (measure_mono (D.fourthJointNearWallStrip_subset_boxP1 hab j delta)).trans
    (fourthPlusNearWallBox_volume_leP1 _ _ _ _ (by exact_mod_cast hab.le) hdelta)

theorem integrableOn_fourthJointNearWall_kernelP1 (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    (delta : ℝ) (hdelta : delta ≤ 2 * (D.a : ℝ)) :
    IntegrableOn (fun t => fourthPlusProfileP1 (D.old4 j : ℝ) t * ∏ i, 1 / t i)
      (D.fourthJointNearWallStripP1 j delta) := by
  exact (integrableOn_fourthPlusNearWall_kernelP1 (by exact_mod_cast ha) hdelta).mono_set
    (D.fourthJointNearWallStrip_subset_boxP1 hab j delta)

theorem fourthJointNearWall_integral_abs_leP1 (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 2 * (D.a : ℝ)) :
    |∫ t in D.fourthJointNearWallStripP1 j delta,
      fourthPlusProfileP1 (D.old4 j : ℝ) t * ∏ i, 1 / t i| ≤
      fourthNearWallKernelBoundP1 (D.a : ℝ) * (delta * ((D.b : ℝ) - D.a) ^ 3) := by
  have hvol := D.fourthJointNearWallStrip_volume_leP1 hab j delta hdelta0
  have hfinite : volume (D.fourthJointNearWallStripP1 j delta) < ∞ :=
    hvol.trans_lt ENNReal.ofReal_lt_top
  have hreal : volume.real (D.fourthJointNearWallStripP1 j delta) ≤
      delta * ((D.b : ℝ) - D.a) ^ 3 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    simpa only [Measure.real, ENNReal.toReal_ofReal
      (mul_nonneg hdelta0 (pow_nonneg (by exact_mod_cast sub_nonneg.mpr hab.le) 3))] using hh
  have hn := norm_setIntegral_le_of_norm_le_const hfinite
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact fourthPlusNearWall_kernel_abs_leP1 (by exact_mod_cast ha) hdelta
        (D.fourthJointNearWallStrip_subset_boxP1 hab j delta ht))
  rw [Real.norm_eq_abs] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left hreal
    (fourthNearWallKernelBound_nonnegP1 (by exact_mod_cast ha)))

/-- Explicit delta-to-zero entry point on the original historical joint
cell; it is a proved continuous integral payment, not an arithmetic mean. -/
theorem fourthJointNearWall_integral_uniform_smallP1 (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ ∀ delta : ℝ, 0 ≤ delta → delta ≤ delta₀ →
      ∀ j : Fin 4 → Fin (D.m + 1),
        |∫ t in D.fourthJointNearWallStripP1 j delta,
          fourthPlusProfileP1 (D.old4 j : ℝ) t * ∏ i, 1 / t i| < epsilon := by
  let C := fourthNearWallKernelBoundP1 (D.a : ℝ) * ((D.b : ℝ) - D.a) ^ 3
  have hC : 0 ≤ C := mul_nonneg
    (fourthNearWallKernelBound_nonnegP1 (by exact_mod_cast ha))
    (pow_nonneg (by exact_mod_cast sub_nonneg.mpr hab.le) 3)
  let delta₀ := min (D.a : ℝ) (epsilon / (C + 1))
  have hd0 : 0 < delta₀ := lt_min (by exact_mod_cast ha) (div_pos hepsilon (by positivity))
  refine ⟨delta₀, hd0, ?_⟩
  intro delta hd hsmall j
  have hda : delta ≤ (D.a : ℝ) := hsmall.trans (min_le_left _ _)
  have hde : delta ≤ epsilon / (C + 1) := hsmall.trans (min_le_right _ _)
  have hpaid := D.fourthJointNearWall_integral_abs_leP1 ha hab j delta hd
    (by have ha0 : (0 : ℝ) < D.a := by exact_mod_cast ha; linarith)
  have hmul : delta * (C + 1) ≤ epsilon := (le_div_iff₀ (by positivity)).mp hde
  have hstrict : C * delta < epsilon := by
    by_cases hz : delta = 0
    · simp only [hz, mul_zero]
      exact hepsilon
    · have hpos : 0 < delta := lt_of_le_of_ne hd (Ne.symm hz)
      nlinarith
  calc
    _ ≤ fourthNearWallKernelBoundP1 (D.a : ℝ) *
        (delta * ((D.b : ℝ) - D.a) ^ 3) := hpaid
    _ = C * delta := by dsimp [C]; ring
    _ < epsilon := hstrict

theorem tendsto_fourthJointNearWall_integralP1 {ι : Type*} (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    (l : Filter ι) (delta : ι → ℝ) (hlim : Tendsto delta l (𝓝 0))
    (hdelta : ∀ᶠ i in l, 0 ≤ delta i) :
    Tendsto (fun i => ∫ t in D.fourthJointNearWallStripP1 j (delta i),
      fourthPlusProfileP1 (D.old4 j : ℝ) t * ∏ q, 1 / t q) l (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  obtain ⟨delta₀, hd0, hsmall⟩ := D.fourthJointNearWall_integral_uniform_smallP1
    ha hab epsilon hepsilon
  have hev : ∀ᶠ i in l, delta i < delta₀ := hlim.eventually (gt_mem_nhds hd0)
  filter_upwards [hdelta, hev] with i hi hdi
  simpa only [Real.dist_eq, sub_zero] using hsmall (delta i) hi hdi.le j

end HistoricalPrefixCapData
end
end ImbalancedChen
