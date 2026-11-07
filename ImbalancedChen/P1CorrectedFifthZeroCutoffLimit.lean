import ImbalancedChen.P1CorrectedFifthUniformSmallRemainder
import Mathlib.Topology.MetricSpace.Cauchy

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The genuine actual corrected arithmetic tail constructs a Cauchy family of
the actual-parent positive-cut integrals. Completeness constructs their
zero-cut value, and the same source tail proves convergence of the COMPLETE
original-T3 normalized corrected charge for every covering cap function.
Canonical lower monotonicity plus the finite h45 check proves nonnegativity;
no desired limiting value, target mean or integral bound is an input.

This module first constructs the zero-cut value. Its identification with a
separately defined untruncated Lebesgue integral is an independent exhaustion
step. No generic-D parent or coarse-old5 remainder is substituted here.
-/

namespace ImbalancedChen.P1CorrectedFifthZeroCutoffLimit

noncomputable section
open Filter Topology Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary P1CorrectedFifthStoredH45Check
open P1CorrectedFifthSmallLastGeometry P1CorrectedFifthUniformSmallRemainder
open P1CorrectedFifthGlobalSourceAssembly P1OriginalFifthMovingScaleLimit

private theorem evenTargets_nonempty : NeBot evenTargets := by
  have hd : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have he : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop
      (Filter.principal {N : ℕ | 0 < N ∧ Even N}) := by
    apply tendsto_principal.2
    exact Eventually.of_forall (fun n => ⟨by omega, ⟨n + 1, by omega⟩⟩)
  exact (tendsto_inf.2 ⟨hd, he⟩).neBot

section Corrected
variable (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
  (e : ℚ) (chi omega : ℝ) (homega : 0 < omega)
  (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
  (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
  (hcheck : storedH45Check D J e rows = true)

theorem corrected_selectedIntegral_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ selectedIntegral D J e chi omega rows licensed a := by
  apply Finset.sum_nonneg
  intro j hj
  change 0 ≤ ∫ t in correctedOriginalCell e chi omega a D.m j,
    correctedCellKernel (originalVariableFourthProfile e chi omega D.m j rows licensed)
      (D.cap5 j : ℝ) t
  apply setIntegral_nonneg (P1OriginalFifthIntegral.truncatedCell_measurable e chi D.m omega a j)
  intro t ht
  apply correctedCellKernel_nonneg
  · intro i
    exact ha.trans_le (mem_logPrimeBox.mp ht.1 i).1
  · exact originalVariableFourthProfile_le_storedCap
      D J e chi omega rows licensed howned hcheck j hj t ht.2.1

/-- The arithmetic source cancels between two complete corrected charges.
Its independently proved tails bound the two actual positive-cut integrals. -/
theorem exists_corrected_cutoff_difference_le :
    ∃ L : ℝ, 0 < L ∧ ∀ a b : ℝ,
      0 < a → a < min (19 / 96 : ℝ) (omega / 6) →
      0 < b → b < min (19 / 96 : ℝ) (omega / 6) →
      |selectedIntegral D J e chi omega rows licensed a -
        selectedIntegral D J e chi omega rows licensed b| ≤ L * (a + b) := by
  obtain ⟨L, hL, htail⟩ := exists_eventually_corrected_smallRemainder_abs_le_linear
    D J e chi omega homega rows licensed howned hcheck
  refine ⟨L, hL, ?_⟩
  intro a b ha hamax hb hbmax
  letI : NeBot evenTargets := evenTargets_nonempty
  let cap : ℕ → ℕ := fun N => Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ))
  have hcap : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ) :=
    Eventually.of_forall (fun N => Nat.le_ceil _)
  have hlim := (tendsto_normalizedCharge_sub_smallRemainder D J e chi omega rows licensed
    a ha (hamax.trans_le (min_le_left _ _)) howned cap hcap).sub
      (tendsto_normalizedCharge_sub_smallRemainder D J e chi omega rows licensed
        b hb (hbmax.trans_le (min_le_left _ _)) howned cap hcap)
  have hpair : ∀ᶠ N : ℕ in evenTargets,
      |(normalizedCharge D J e chi omega rows licensed N (cap N) -
          smallRemainder D J e chi omega rows licensed a N (cap N)) -
        (normalizedCharge D J e chi omega rows licensed N (cap N) -
          smallRemainder D J e chi omega rows licensed b N (cap N))| ≤ L * (a + b) := by
    filter_upwards [htail a ha hamax.le cap hcap, htail b hb hbmax.le cap hcap]
      with N hA hB
    have heq : (normalizedCharge D J e chi omega rows licensed N (cap N) -
        smallRemainder D J e chi omega rows licensed a N (cap N)) -
        (normalizedCharge D J e chi omega rows licensed N (cap N) -
          smallRemainder D J e chi omega rows licensed b N (cap N)) =
      smallRemainder D J e chi omega rows licensed b N (cap N) -
        smallRemainder D J e chi omega rows licensed a N (cap N) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  exact le_of_tendsto hlim.abs hpair

/-- Completeness constructs the zero-cut value from the actual corrected
integrals themselves. No target limit or untruncated integral is supplied. -/
theorem exists_corrected_selectedIntegral_zero_cutoff_limit :
    ∃ V : ℝ, Tendsto (fun a : ℝ => selectedIntegral D J e chi omega rows licensed a)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 V) := by
  obtain ⟨L, hL, hbound⟩ := exists_corrected_cutoff_difference_le
    D J e chi omega homega rows licensed howned hcheck
  let I : ℝ → ℝ := selectedIntegral D J e chi omega rows licensed
  apply cauchy_map_iff_exists_tendsto.1
  apply Metric.cauchy_iff.2
  refine ⟨inferInstance, ?_⟩
  intro epsilon hepsilon
  let delta := min (min (19 / 96 : ℝ) (omega / 6)) (epsilon / (2 * L))
  have hdelta : 0 < delta := lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  refine ⟨I '' Ioo 0 delta, ?_, ?_⟩
  · apply Filter.mem_map.2
    filter_upwards [self_mem_nhdsWithin,
      (Iio_mem_nhds hdelta).filter_mono nhdsWithin_le_nhds] with a ha hadelta
    exact ⟨a, ⟨ha, hadelta⟩, rfl⟩
  · intro x hx y hy
    obtain ⟨a, ⟨ha, hadelta⟩, rfl⟩ := hx
    obtain ⟨b, ⟨hb, hbdelta⟩, rfl⟩ := hy
    have haMax : a < min (19 / 96 : ℝ) (omega / 6) := hadelta.trans_le (min_le_left _ _)
    have hbMax : b < min (19 / 96 : ℝ) (omega / 6) := hbdelta.trans_le (min_le_left _ _)
    have had : a < epsilon / (2 * L) := hadelta.trans_le (min_le_right _ _)
    have hbd : b < epsilon / (2 * L) := hbdelta.trans_le (min_le_right _ _)
    have hA := (lt_div_iff₀ (show 0 < 2 * L by positivity)).mp had
    have hB := (lt_div_iff₀ (show 0 < 2 * L by positivity)).mp hbd
    have hp : L * (a + b) < epsilon := by nlinarith
    rw [Real.dist_eq]
    exact (hbound a b ha haMax hb hbMax).trans_lt hp

/-- Full actual corrected normalized charge and positive-cut integrals
converge to the SAME constructed nonnegative value. Only original finite
ownership/h45 and genuine enumeration coverage occur as primitive inputs. -/
theorem exists_corrected_full_charge_and_zero_cutoff_limit :
    ∃ V : ℝ, 0 ≤ V ∧
      Tendsto (fun a : ℝ => selectedIntegral D J e chi omega rows licensed a)
        (𝓝[Ioi 0] (0 : ℝ)) (𝓝 V) ∧
      ∀ cap : ℕ → ℕ,
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      Tendsto (fun N : ℕ => normalizedCharge D J e chi omega rows licensed N (cap N))
        evenTargets (𝓝 V) := by
  obtain ⟨V, hI⟩ := exists_corrected_selectedIntegral_zero_cutoff_limit
    D J e chi omega homega rows licensed howned hcheck
  obtain ⟨L, hL, htail⟩ := exists_eventually_corrected_smallRemainder_abs_le_linear
    D J e chi omega homega rows licensed howned hcheck
  have hV : 0 ≤ V := le_of_tendsto hI (by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact corrected_selectedIntegral_nonneg D J e chi omega rows licensed howned hcheck a ha)
  refine ⟨V, hV, hI, ?_⟩
  intro cap hcap
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  have hthird : 0 < epsilon / 3 := by positivity
  have hcut : 0 < min (min (19 / 96 : ℝ) (omega / 6)) (epsilon / (3 * L)) :=
    lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  obtain ⟨a, ha, hsmall, hnear⟩ :=
    (self_mem_nhdsWithin.and
      (((Iio_mem_nhds hcut).filter_mono nhdsWithin_le_nhds).and
        (Metric.tendsto_nhds.1 hI (epsilon / 3) hthird))).exists
  have ha0 : 0 < a := ha
  have hamax : a < min (19 / 96 : ℝ) (omega / 6) := hsmall.trans_le (min_le_left _ _)
  have hLa : L * a < epsilon / 3 := by
    have hh := (lt_div_iff₀ (show 0 < 3 * L by positivity)).mp
      (hsmall.trans_le (min_le_right _ _))
    nlinarith
  have hpos := tendsto_normalizedCharge_sub_smallRemainder D J e chi omega rows licensed
    a ha0 (hamax.trans_le (min_le_left _ _)) howned cap hcap
  have hclose := Metric.tendsto_nhds.1 hpos (epsilon / 3) hthird
  filter_upwards [htail a ha0 hamax.le cap hcap, hclose] with N hrem hposN
  rw [Real.dist_eq] at hnear hposN ⊢
  have htri : |normalizedCharge D J e chi omega rows licensed N (cap N) - V| ≤
      |normalizedCharge D J e chi omega rows licensed N (cap N) -
        smallRemainder D J e chi omega rows licensed a N (cap N) -
        selectedIntegral D J e chi omega rows licensed a| +
      |smallRemainder D J e chi omega rows licensed a N (cap N)| +
      |selectedIntegral D J e chi omega rows licensed a - V| := by
    calc
      _ = |((normalizedCharge D J e chi omega rows licensed N (cap N) -
          smallRemainder D J e chi omega rows licensed a N (cap N)) -
          selectedIntegral D J e chi omega rows licensed a) +
          smallRemainder D J e chi omega rows licensed a N (cap N) +
          (selectedIntegral D J e chi omega rows licensed a - V)| := by congr 1; ring
      _ ≤ _ := (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
  change |normalizedCharge D J e chi omega rows licensed N (cap N) -
      smallRemainder D J e chi omega rows licensed a N (cap N) -
      selectedIntegral D J e chi omega rows licensed a| < epsilon / 3 at hposN
  linarith

/-- The complete original retained-polynomial difference starts at the
empty history with mass one. The finite stored checker, rather than an
assumed density inequality, identifies this with the corrected charge. -/
def normalizedRetainedDifference (N cap : ℕ) : ℝ :=
  (originalFourthRetained e chi D.m omega N cap ((N : ℝ) ^ (19 / 96 : ℝ)) rows licensed -
    firstExitRetainedPolynomial
      (P1VariableFifthOriginalBaseQ3Bridge.correctedStoredPolicy5
        D J e chi omega (N : ℝ) rows licensed)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) *
      Real.log (N : ℝ) / singularSeries N

theorem exists_corrected_policy_and_zero_cutoff_limit :
    ∃ V : ℝ, 0 ≤ V ∧
      Tendsto (fun a : ℝ => selectedIntegral D J e chi omega rows licensed a)
        (𝓝[Ioi 0] (0 : ℝ)) (𝓝 V) ∧
      ∀ cap : ℕ → ℕ,
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      Tendsto (fun N : ℕ => normalizedRetainedDifference D J e chi omega rows licensed N (cap N))
        evenTargets (𝓝 V) := by
  obtain ⟨V, hV, hI, hmean⟩ := exists_corrected_full_charge_and_zero_cutoff_limit
    D J e chi omega homega rows licensed howned hcheck
  refine ⟨V, hV, hI, ?_⟩
  intro cap hcap
  apply (hmean cap hcap).congr'
  filter_upwards [(eventually_gt_atTop (1 : ℕ)).filter_mono
    (show evenTargets ≤ atTop from inf_le_left)] with N hN
  rw [normalizedRetainedDifference,
    corrected_fourth_to_fifth_finite_density_identity D J e chi omega rows licensed
      howned hcheck N (cap N) hN ((N : ℝ) ^ (19 / 96 : ℝ))]
  rfl

end Corrected
end
end ImbalancedChen.P1CorrectedFifthZeroCutoffLimit
