import ImbalancedChen.P5ZU1011SameRhoNativePrimeBoxDensity

/-!
# Actual native normalized density error tends to zero uniformly in E

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Fix mesh and positive rational eta BEFORE N. The finite-cell density
error is bounded by its true reciprocal-prime box mass, whose limit is
already proved. One common threshold pays the TOTAL error for every
outer mask, including moving masks. This is a vanishing error statement,
not an integral model for arbitrary moving masks.
-/

namespace ImbalancedChen.P5Z.U1011SameRhoDensityErrorZero

noncomputable section

open Set Classical Filter Topology
open scoped BigOperators
open U11Integral U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenJointNearCapCompiler
open U1011OriginalSixteenJointNearCapModulusConvolution
open U1011SameRhoNativePrimeBoxDensity

def densityError (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ t ∈ ordinaryTuples n N E,
    |ownerDensity n N eta (coordinates N t) * Real.log (N : ℝ) / singularSeries N -
      ownerLimit n eta (coordinates N t)| / (Nat.totient (fullPrefix t) : ℝ)

def normalizedPhysicalDensity (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  physicalDensitySum (modulusSupport n N eta E) (sigma n N eta E) *
    Real.log (N : ℝ) / singularSeries N

def ordinaryNativeMass (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  JointNearCapPrimeReserve.jointMass N E (ordinaryKeep n N) (ownerLimit n eta)

theorem densityError_nonneg (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) :
    0 ≤ densityError n N eta E :=
  Finset.sum_nonneg (fun t _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

/-- Same actual full-phi mean, with no row-count factor or new coefficient. -/
theorem abs_normalizedPhysicalDensity_sub_ordinaryNativeMass_le {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    |normalizedPhysicalDensity n N eta E - ordinaryNativeMass n N eta E| ≤
      densityError n N eta E := by
  have hsum (f : LogFour → ℝ) :
      JointNearCapPrimeReserve.jointMass N E (ordinaryKeep n N) f =
        ∑ t ∈ ordinaryTuples n N E, f (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ) := by
    simp only [JointNearCapPrimeReserve.jointMass, ordinaryKeep, ordinaryTuples,
      U1011OriginalSixteenJointNativeCompiler.ordinaryTuples, Finset.sum_filter]
  have heq : normalizedPhysicalDensity n N eta E - ordinaryNativeMass n N eta E =
      ∑ t ∈ ordinaryTuples n N E,
        (ownerDensity n N eta (coordinates N t) * Real.log (N : ℝ) / singularSeries N -
          ownerLimit n eta (coordinates N t)) / (Nat.totient (fullPrefix t) : ℝ) := by
    rw [normalizedPhysicalDensity, physicalDensity_eq_actual_native_harmonic hN heta E,
      ordinaryNativeMass, hsum, hsum, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [heq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold densityError
  apply Finset.sum_le_sum
  intro t ht
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _)]

/-- Mesh and eta are fixed, then ONE N threshold works for every E. -/
theorem eventually_all_outer_masks_densityError_lt (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ E : ℕ × ℕ → Prop, densityError n N eta E < epsilon := by
  let L : ℝ := ∏ i : Fin 4, Real.log ((59 / 250 : ℝ) / (417 / 5000 : ℝ))
  let M : ℝ := |L| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hLM : L < M := by dsimp [M]; linarith only [le_abs_self L]
  have hmass : ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxMass N (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) < M :=
    (tendsto_actualPrimeBoxMass (fun _ : Fin 4 => (417 / 5000 : ℝ))
      (fun _ => (59 / 250 : ℝ)) (fun _ => by norm_num) (fun _ => by norm_num)).eventually
        (gt_mem_nhds hLM)
  have htol : 0 < epsilon / (2 * M) := div_pos hepsilon (mul_pos (by norm_num) hM)
  filter_upwards [eventually_actual_primebox_density_error n eta heta (epsilon / (2 * M)) htol,
    hmass.filter_mono inf_le_left] with N herr hmassN
  intro E
  have hh := (herr E).trans (mul_le_mul_of_nonneg_left hmassN.le htol.le)
  change densityError n N eta E ≤ _ at hh
  have hcancel : epsilon / (2 * M) * M = epsilon / 2 := by field_simp [hM.ne'] <;> ring
  rw [hcancel] at hh
  exact hh.trans_lt (by linarith only [hepsilon])

/-- Arbitrary moving E has only an ERROR limit here; no integral limit
for its actual retained mass is inferred. -/
theorem tendsto_densityError_moving_mask (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    (E : ℕ → ℕ × ℕ → Prop) :
    Tendsto (fun N : ℕ => densityError n N eta (E N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [eventually_all_outer_masks_densityError_lt n eta heta epsilon hepsilon] with N hN
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (densityError_nonneg n N eta (E N))] using hN (E N)

theorem tendsto_normalizedPhysicalDensity_sub_ordinaryNativeMass (n : ℕ) (eta : ℚ)
    (heta : 0 < eta) (E : ℕ → ℕ × ℕ → Prop) :
    Tendsto (fun N : ℕ => normalizedPhysicalDensity n N eta (E N) - ordinaryNativeMass n N eta (E N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [eventually_all_outer_masks_densityError_lt n eta heta epsilon hepsilon,
    (eventually_gt_atTop (1 : ℕ)).filter_mono inf_le_left] with N hpaid hN
  simpa only [Real.dist_eq, sub_zero] using
    (abs_normalizedPhysicalDensity_sub_ordinaryNativeMass_le hN heta (E N)).trans_lt (hpaid (E N))

end

end ImbalancedChen.P5Z.U1011SameRhoDensityErrorZero
