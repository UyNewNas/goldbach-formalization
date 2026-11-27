import ImbalancedChen.ActualRosserResidualDensity
import ImbalancedChen.ActualThirdPrefixTailIntegralCore
import ImbalancedChen.P2OriginalSelectedPairNativeData
import ImbalancedChen.P2OriginalU5PlateauRectangle

/-! A positive lower bound for the ordinary residual density at the starting
cap of the original U5 marked pair. The physical level includes its two
buffers and both marked primes. Summing the uniform row estimate uses a
fixed interior rectangle of the original selector. -/

namespace ImbalancedChen.P3OriginalU5OrdinaryRootDensity

noncomputable section

open Filter Topology
open scoped BigOperators
open MathlibNt.SieveTheory
open P2LowerCapPlanIntegerRetention (coordinate coordinate_power)
open P2OriginalSelectedPairNativeData (rootSeed)
open P5OriginalU5CausalFinite (coordinates pairSupport cutoff originalResidual)
open Part5OriginalUpsilon5CausalDictionary (a)

/-- The ordinary term of the lower U5 tree, before a rough prime is selected. -/
def ordinaryRootDensity (b : ℚ) (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  actualSmallRosserMinusDensity N (Nat.ceil (cutoff N)) (cutoff N)
    ((N : ℝ) ^ rootSeed false b N t / ((t.1 : ℝ) * t.2))

private theorem root_parameters {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {b : ℚ} (hb : 0 ≤ b) (hb' : b ≤ 1/1000) :
    let s := (originalResidual N t - 2 * (b : ℝ)) / a
    3 ≤ s ∧ s ≤ 5 ∧
      (N : ℝ) ^ (s * a) = (N : ℝ) ^ rootSeed false b N t / ((t.1 : ℝ) * t.2) := by
  have ha : 0 < a := by norm_num [a]
  have hb₀ : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hb₁ : (b : ℝ) ≤ 1/1000 := by
    have hc : (b : ℝ) ≤ ((1/1000 : ℚ) : ℝ) := Rat.cast_le.mpr hb'
    norm_num at hc ⊢
    exact hc
  have hx := P5OriginalU5CausalFinite.coordinates_mem_triangle hN ht
  obtain ⟨hu, hut, hh⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp hx
  obtain ⟨hl, hr⟩ := Part5OriginalUpsilon5CausalDictionary.residual_bounds hu hut.le hh.le
  change (34 / 125 : ℝ) ≤ originalResidual N t at hl
  change originalResidual N t ≤ (2083 / 5000 : ℝ) at hr
  obtain ⟨hpair, _, _, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpair
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hp' := coordinate_power hNr (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have hq' := coordinate_power hNr (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  have he : originalResidual N t - 2 * (b : ℝ) =
      rootSeed false b N t - (coordinate N t.1 + coordinate N t.2) := by
    let V := Part5OriginalUpsilon5CausalDictionary.level (coordinate N t.1) (coordinate N t.2)
    change (V - coordinate N t.1 - coordinate N t.2) - 2 * (b : ℝ) =
      (V - 2 * (b : ℝ)) - (coordinate N t.1 + coordinate N t.2)
    ring
  dsimp only
  refine ⟨(le_div_iff₀ ha).mpr ?_, (div_le_iff₀ ha).mpr ?_, ?_⟩
  · dsimp only [a]
    linarith only [hl, hb₁]
  · dsimp only [a]
    linarith only [hr, hb₀]
  · rw [div_mul_cancel₀ _ ha.ne', he, Real.rpow_sub (zero_lt_one.trans hNr),
      Real.rpow_add (zero_lt_one.trans hNr), hp', hq']

/-- One positive constant and one threshold work across the original ordered
pairs and every buffer from zero through the manuscript working buffer. -/
theorem exists_ordinary_root_row_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
      ∀ t ∈ pairSupport N, ∀ b : ℚ, 0 ≤ b → b ≤ 1/1000 →
        c * singularSeries N / Real.log (N : ℝ) ≤ ordinaryRootDensity b N t := by
  have ha : 0 < a := by norm_num [a]
  let A := 2 * Real.exp (-Real.eulerMascheroniConstant) / a
  have hA : 0 < A := div_pos (mul_pos (by norm_num) (Real.exp_pos _)) ha
  have hf : 0 < suzukiContinuousLowerFactor 3 := by
    rw [suzukiContinuousLowerFactor_firstInterval_eq 3 (by norm_num) (by norm_num)]
    have hl : 0 < Real.log ((3 : ℝ) - 1) := Real.log_pos (by norm_num)
    positivity
  let c := A * suzukiContinuousLowerFactor 3 / 2
  have hc : 0 < c := div_pos (mul_pos hA hf) (by norm_num)
  let S : Set (ℝ × ℝ) := Set.Icc a a ×ˢ Set.Icc (3 : ℝ) 5
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hparam (p : ℝ × ℝ) (hp : p ∈ S) : 0 < p.1 ∧ 2 ≤ p.2 :=
    ⟨ha.trans_le hp.1.1, (by norm_num : (2 : ℝ) ≤ 3).trans hp.2.1⟩
  obtain ⟨N0, hN0, hclose⟩ :=
    exists_actualSmallRosserMinusDensity_compact_normalized_threshold S hS hparam c hc
  refine ⟨c, hc, N0, hN0, ?_⟩
  intro N hN hEven t ht b hb hb'
  let s := (originalResidual N t - 2 * (b : ℝ)) / a
  obtain ⟨hs₁, hs₂, hlevel⟩ := root_parameters (hN0.trans hN) ht hb hb'
  have hp : (a,s) ∈ S := ⟨⟨le_rfl, le_rfl⟩, hs₁, hs₂⟩
  have h := hclose N hN hEven (a,s) hp (Nat.ceil (cutoff N)) (Nat.le_ceil _)
  change |actualSmallRosserMinusDensity N (Nat.ceil (cutoff N)) (cutoff N)
      ((N : ℝ) ^ (s * a)) * Real.log (N : ℝ) / singularSeries N -
      A * suzukiContinuousLowerFactor s| < c at h
  rw [hlevel] at h
  have hmono : suzukiContinuousLowerFactor 3 ≤ suzukiContinuousLowerFactor s :=
    thirdTail_lowerFactor_monotone (by norm_num : (2 : ℝ) ≤ 3)
      ((by norm_num : (2 : ℝ) ≤ 3).trans hs₁) hs₁
  have hv := mul_le_mul_of_nonneg_left hmono hA.le
  have hlo := (abs_lt.mp h).1
  change -c < ordinaryRootDensity b N t * Real.log (N : ℝ) / singularSeries N -
      A * suzukiContinuousLowerFactor s at hlo
  have hc' : 2 * c = A * suzukiContinuousLowerFactor 3 := by dsimp only [c]; ring
  have hh : c ≤ ordinaryRootDensity b N t * Real.log (N : ℝ) / singularSeries N := by
    linarith only [hlo, hv, hc']
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact (div_le_iff₀ (Real.log_pos hNr)).mpr ((le_div_iff₀ (singularSeries_pos N)).mp hh)

open P2GammaU5PlateauGeometry (rectangle boxLo boxHi rectangle_subset_pairSupport)

private theorem rectangle_reciprocal_mass {N : ℕ} (hN : 2 ≤ N) :
    (∑ t ∈ rectangle N, 1 / (Nat.totient (t.1 * t.2) : ℝ)) =
      actualPrimeBoxMass N boxLo boxHi := by
  classical
  rw [rectangle, Finset.sum_image]
  · unfold actualPrimeBoxMass
    apply Finset.sum_congr rfl
    intro p hp
    have ht : (p 0, p 1) ∈ rectangle N := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨_, _, hlt, _⟩ := Finset.mem_filter.mp (rectangle_subset_pairSupport hN ht)
    have hpr := mem_actualPrimeBoxTuples_iff.mp hp
    change 1 / (Nat.totient (p 0 * p 1) : ℝ) = _
    rw [chen_prime_pair_totient_cast (hpr 0).1 (hpr 1).1 hlt.ne]
    simp only [Fin.prod_univ_two, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  · intro p _ q _ he
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

/-- The product of the two logarithmic prime masses on a fixed subrectangle
gives a positive eventual lower bound for the original ordered-pair carrier. -/
theorem exists_pairSupport_harmonic_lower :
    ∃ h : ℝ, 0 < h ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0,
      h ≤ ∑ t ∈ pairSupport N, 1 / (Nat.totient (t.1 * t.2) : ℝ) := by
  have hlo (i : Fin 2) : 0 < boxLo i := by fin_cases i <;> norm_num [boxLo]
  have hlt (i : Fin 2) : boxLo i < boxHi i := by fin_cases i <;> norm_num [boxLo, boxHi]
  let M := ∏ i : Fin 2, Real.log (boxHi i / boxLo i)
  have hM : 0 < M :=
    Finset.prod_pos (fun i _ => Real.log_pos ((one_lt_div (hlo i)).mpr (hlt i)))
  have hev : ∀ᶠ N : ℕ in atTop, M / 2 < actualPrimeBoxMass N boxLo boxHi :=
    (tendsto_actualPrimeBoxMass boxLo boxHi hlo hlt).eventually
      (lt_mem_nhds (show M / 2 < M by linarith only [hM]))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  refine ⟨M / 2, half_pos hM, max N0 2, le_max_right _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  calc
    M / 2 ≤ actualPrimeBoxMass N boxLo boxHi := (hN0 N ((le_max_left _ _).trans hN)).le
    _ = ∑ t ∈ rectangle N, 1 / (Nat.totient (t.1 * t.2) : ℝ) :=
      (rectangle_reciprocal_mass hN2).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (rectangle_subset_pairSupport hN2)
      (fun _ _ _ => by positivity)

/-- The ordinary starting term has positive mass after summing over every
original U5 label, with the full external pair totient in each denominator. -/
theorem exists_ordinary_root_pair_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
      ∀ b : ℚ, 0 ≤ b → b ≤ 1/1000 →
        c * singularSeries N / Real.log (N : ℝ) ≤
          ∑ t ∈ pairSupport N, ordinaryRootDensity b N t / (Nat.totient (t.1 * t.2) : ℝ) := by
  obtain ⟨c, hc, N1, hN1, hrow⟩ := exists_ordinary_root_row_lower
  obtain ⟨h, hh, N2, _, hmass⟩ := exists_pairSupport_harmonic_lower
  refine ⟨c * h, mul_pos hc hh, max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN hEven b hb hb'
  have h₁ : N1 ≤ N := (le_max_left _ _).trans hN
  have h₂ : N2 ≤ N := (le_max_right _ _).trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let scale := c * singularSeries N / Real.log (N : ℝ)
  have hscale : 0 ≤ scale := (div_pos (mul_pos hc (singularSeries_pos N)) (Real.log_pos hNr)).le
  calc
    c * h * singularSeries N / Real.log (N : ℝ) = scale * h := by dsimp only [scale]; ring
    _ ≤ scale * (∑ t ∈ pairSupport N, 1 / (Nat.totient (t.1 * t.2) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass N h₂) hscale
    _ = ∑ t ∈ pairSupport N, scale / (Nat.totient (t.1 * t.2) : ℝ) := by
      simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun t ht =>
      div_le_div_of_nonneg_right (hrow N h₁ hEven t ht b hb hb') (Nat.cast_nonneg _))

end

end ImbalancedChen.P3OriginalU5OrdinaryRootDensity
