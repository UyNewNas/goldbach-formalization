import ImbalancedChen.P1OriginalSingletonSmoothLicence
import ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy
import ImbalancedChen.P1OriginalSingletonProperPower

/-!
The proper-power correction in the original singleton Atlas, with all
original chart weights and pre-HB roughness thresholds retained.

The finite chart sum is put inside one real weight. Its amplitude is at
most one because the original psi partition is nonnegative and sums to
one, while each original rough projector takes values zero and one.
The extra complete-product eta in originalChart is kept, even when its
parameter agrees with the lower smoothing parameter of fullSmoothWeight.

The only arithmetic estimate is the existing Part3 proper-power theorem.
The finite dictionary below includes every integer proper-power input,
one Lambda/log factor, the original signed coefficient, and its exact
coprime mean. No bound for an unknown signed error is an input.
-/

namespace ImbalancedChen.P1OriginalSingletonAtlasProperPower

noncomputable section

open Classical Finset Filter
open scoped BigOperators Topology
open Part3
open Part3.FiniteLambdaOverLogDictionary (lambdaOverLog)
open Part3.AllKLambdaChartCorrection (lambdaWord roughWord properChartWords
  properChartWords_spec supportedWord primeOnly)
open Part3.OriginalProperPowerActualChart (integerWords)
open P5Z.ActualEtaPsiOccurrenceBudget (eta chi eta_bounds)
open P5Z.ActualSingletonPrimeTestFamily (chi_bounds chi_one chi_zero)
open P5Z.ExactOriginalSmoothDyadicPartition
  (R R_pos bump psi cutoffIndex words words_spec words_mem words_sum_cons
    chartBank tupleProfile beforeHBCutoff bump_bounds scalar_partition)
open P5Z.ActualLabelledPrimeSmoothCharts (chartTerm trimmedWeight)
open P5Z.LicensedOriginalIntegerProfile (listExtension)
open P5Z.IndependentPrimeSourceWordDictionary
  (sourceWord sourceWord_injective wordKernel residueKernel_real)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (originalChart properPowerReserve)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence smoothNatural smooth_range)

/-- The real value of the literal original rough projector. -/
def roughIndicator (z : ℝ) (n : ℕ) : ℝ :=
  if ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ) then 1 else 0

private theorem roughIndicator_cast (z : ℝ) (n : ℕ) :
    (roughIndicator z n : ℂ) = roughOneSlot z n := by
  unfold roughIndicator roughOneSlot
  split_ifs <;> rfl

private theorem roughIndicator_bounds (z : ℝ) (n : ℕ) :
    0 ≤ roughIndicator z n ∧ roughIndicator z n ≤ 1 := by
  unfold roughIndicator
  split_ifs <;> norm_num

/-- Each summand retains the roughness threshold of its own original chart. -/
def chartRoughMultiplier (K cap n : ℕ) : ℝ :=
  ∑ j ∈ range (cutoffIndex cap + 1),
    bump chi ((n : ℝ) / R j) * roughIndicator (beforeHBCutoff K [j]) n

private theorem chi_antitone : Antitone chi := by
  intro x y hxy
  exact sub_le_sub_left
    (Real.smoothTransition.monotone (sub_le_sub_right hxy 1)) 1

private theorem actual_bump_bounds (j n : ℕ) :
    0 ≤ bump chi ((n : ℝ) / R j) ∧ bump chi ((n : ℝ) / R j) ≤ 1 :=
  bump_bounds chi chi_antitone chi_bounds (div_nonneg (Nat.cast_nonneg _) (R_pos _).le)

private theorem chartRoughMultiplier_zero (K cap : ℕ) :
    chartRoughMultiplier K cap 0 = 0 := by
  simp [chartRoughMultiplier, bump]

private theorem chartRoughMultiplier_bounds (K cap n : ℕ)
    (hn : 1 ≤ n) (hcap : n ≤ cap) :
    0 ≤ chartRoughMultiplier K cap n ∧ chartRoughMultiplier K cap n ≤ 1 := by
  have hpartition :
      (∑ j ∈ range (cutoffIndex cap + 1), bump chi ((n : ℝ) / R j)) = 1 := by
    apply Complex.ofReal_injective
    have hp : cap ≤ 2 ^ cutoffIndex cap := Nat.le_of_lt Nat.lt_log2_self
    simpa only [psi, Complex.ofReal_sum, Complex.ofReal_one] using
      scalar_partition chi (fun _ h => chi_one h) (fun _ h => chi_zero h)
        hn (hcap.trans hp)
  constructor
  · exact sum_nonneg (fun j _ => mul_nonneg (actual_bump_bounds j n).1
      (roughIndicator_bounds _ _).1)
  · calc
      chartRoughMultiplier K cap n ≤
          ∑ j ∈ range (cutoffIndex cap + 1), bump chi ((n : ℝ) / R j) := by
        apply sum_le_sum
        intro j _
        exact mul_le_of_le_one_right (actual_bump_bounds j n).1
          (roughIndicator_bounds _ _).2
      _ = 1 := hpartition

/-- The actual scalar source, including the additional original Atlas eta.
The Lambda/log factor belongs to labelledProperPowerResidual, not this weight. -/
def atlasNaturalWeight (kap kap0 : ℝ) (B K N n : ℕ) : ℝ :=
  smoothNatural kap B N n * eta ((n : ℝ) / (N : ℝ) ^ (1 - kap0)) *
    chartRoughMultiplier K (2 * N) n

def atlasWeight (kap kap0 : ℝ) (B K N : ℕ) :
    (Fin 1 → Fin (2 * N + 1)) → ℝ :=
  P5S1SingletonPP.singletonWeight (2 * N) (atlasNaturalWeight kap kap0 B K N)

private theorem atlasNaturalWeight_bounds (kap kap0 : ℝ) (B K N n : ℕ)
    (hn : n ≤ 2 * N) :
    0 ≤ atlasNaturalWeight kap kap0 B K N n ∧
      atlasNaturalWeight kap kap0 B K N n ≤ 1 := by
  by_cases hz : n = 0
  · simp [atlasNaturalWeight, hz, chartRoughMultiplier_zero]
  have hF := smooth_range kap B N n
  have hE := eta_bounds ((n : ℝ) / (N : ℝ) ^ (1 - kap0))
  have hR := chartRoughMultiplier_bounds K (2 * N) n (by omega) hn
  have hFE : smoothNatural kap B N n *
      eta ((n : ℝ) / (N : ℝ) ^ (1 - kap0)) ≤ 1 := by
    exact (mul_le_mul hF.2 hE.2 hE.1 zero_le_one).trans_eq (by norm_num)
  refine ⟨mul_nonneg (mul_nonneg hF.1 hE.1) hR.1, ?_⟩
  exact (mul_le_mul hFE hR.2 hR.1 zero_le_one).trans_eq (by norm_num)

private theorem atlasWeight_abs_le_one (kap kap0 : ℝ) (B K N : ℕ)
    (t : Fin 1 → Fin (2 * N + 1)) : |atlasWeight kap kap0 B K N t| ≤ 1 := by
  obtain ⟨h0, h1⟩ := atlasNaturalWeight_bounds kap kap0 B K N (t 0).val
    (Nat.le_of_lt_succ (t 0).isLt)
  change |atlasNaturalWeight kap kap0 B K N (t 0).val| ≤ 1
  rwa [abs_of_nonneg h0]

private theorem atlasWeight_effective_geometry (kap kap0 : ℝ) (B K : ℕ)
    {N : ℕ} (hN : 2 ≤ N) (t : Fin 1 → Fin (2 * N + 1))
    (ht : atlasWeight kap kap0 B K N t * labelledVonMangoldtWeight t ≠ 0) :
    (∀ i, (N : ℝ) ^ (1 - kap) ≤ ((t i).val : ℝ)) ∧
      (labelledProduct t : ℝ) ≤ 2 * (N : ℝ) := by
  have hW : atlasWeight kap kap0 B K N t ≠ 0 := (mul_ne_zero_iff.mp ht).1
  have hF : smoothNatural kap B N (t 0).val ≠ 0 := by
    intro hz
    apply hW
    simp only [atlasWeight, P5S1SingletonPP.singletonWeight, atlasNaturalWeight,
      hz, zero_mul]
  have hlo : (N : ℝ) ^ (1 - kap) < ((t 0).val : ℝ) := by
    by_contra h
    apply hF
    exact P5Z.ActualSingletonLogCollarFamily.profile_zero_below (1 - kap)
      (P5Z.ActualSingletonLogCollarFamily.logWidth B N) hN
      (fun _ : Fin 1 => ((t 0).val : ℝ)) (le_of_not_gt h)
  constructor
  · intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa only [hi] using hlo.le
  · rw [P5S1SingletonPP.labelledProduct_singleton]
    exact_mod_cast Nat.le_of_lt_succ (t 0).isLt

private theorem asSingleton {ps : List ℕ} (h : ps.length = 1) :
    ∃ n, ps = [n] := by
  cases ps with
  | nil => simp at h
  | cons n ns =>
    have he : ns = [] := List.length_eq_zero.mp (by simpa using h)
    exact ⟨n, by rw [he]⟩

private theorem properPrimePower_pos {n : ℕ} (hn : properPrimePower n) : 0 < n := by
  obtain ⟨p, e, hp, _, rfl⟩ := (properPrimePower_iff_exists n).mp hn
  exact pow_pos hp.pos _

private theorem proper_singleton_mem (cap n : ℕ) :
    [n] ∈ properChartWords cap 1 ↔ n ∈ Icc 1 cap ∧ properPrimePower n := by
  constructor
  · intro h
    obtain ⟨hw, hs, hprime⟩ := mem_filter.mp h
    have hm := (words_spec (Icc 1 cap) 1 [n] hw).2 n (by simp)
    have hnp : ¬n.Prime := by
      intro hp
      apply hprime
      intro m hm
      have he : m = n := by simpa only [List.mem_singleton] using hm
      simpa only [he] using hp
    exact ⟨hm, (hs n (by simp)).resolve_left hnp⟩
  · rintro ⟨hn, hp⟩
    apply mem_filter.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply words_mem (Icc 1 cap) 1 [n] (by simp)
      intro m hm
      have he : m = n := by simpa only [List.mem_singleton] using hm
      simpa only [he] using hn
    · intro m hm
      have he : m = n := by simpa only [List.mem_singleton] using hm
      exact Or.inr (by simpa only [he] using hp)
    · intro hprime
      exact hp.2 (hprime n (by simp))

private def properLabels (cap : ℕ) : Finset (Fin 1 → Fin (cap + 1)) :=
  univ.filter (fun t => ∃ i : Fin 1, properPrimePower (t i).val)

private theorem properLabel_zero {cap : ℕ} {t : Fin 1 → Fin (cap + 1)}
    (ht : t ∈ properLabels cap) : properPrimePower (t 0).val := by
  obtain ⟨i, hi⟩ := (mem_filter.mp ht).2
  have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
  simpa only [hi0] using hi

private theorem sourceWord_singleton (cap : ℕ) (t : Fin 1 → Fin (cap + 1)) :
    sourceWord t = [(t 0).val] := by
  simp [sourceWord, List.ofFn_succ]

private theorem proper_words_image (cap : ℕ) :
    properChartWords cap 1 = (properLabels cap).image sourceWord := by
  ext ps
  constructor
  · intro hps
    have hlen := (words_spec (Icc 1 cap) 1 ps (properChartWords_spec hps).1).1
    obtain ⟨n, rfl⟩ := asSingleton hlen
    obtain ⟨hn, hp⟩ := (proper_singleton_mem cap n).mp hps
    let t : Fin 1 → Fin (cap + 1) := fun _ =>
      ⟨n, Nat.lt_succ_of_le (mem_Icc.mp hn).2⟩
    refine mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, 0, hp⟩, ?_⟩
    simpa only [sourceWord_singleton] using (show [(t 0).val] = [n] from rfl)
  · intro hps
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hps
    rw [sourceWord_singleton, proper_singleton_mem]
    have hp := properLabel_zero ht
    exact ⟨mem_Icc.mpr ⟨properPrimePower_pos hp, Nat.le_of_lt_succ (t 0).isLt⟩, hp⟩

private theorem lambdaOverLog_eq_vonMangoldtOverLog (n : ℕ) :
    lambdaOverLog n = vonMangoldtOverLog n := by
  by_cases hn : n ≤ 1
  · have hc : n = 0 ∨ n = 1 := by omega
    rcases hc with rfl | rfl <;> simp [lambdaOverLog, vonMangoldtOverLog]
  · simp only [lambdaOverLog, if_neg hn, vonMangoldtOverLog]

private theorem wordKernel_eq_finiteProductKernel
    (Q : Finset ℕ) (rho : ℕ → ℂ) (N : ℕ) (ps : List ℕ) :
    wordKernel Q rho N ps = ∑ q ∈ Q, rho q * finiteProductKernel q N ps.prod := by
  unfold wordKernel
  apply sum_congr rfl
  intro q _
  congr 1
  rw [residueKernel_real]
  by_cases hc : Nat.ModEq q ps.prod N <;>
    by_cases hg : ps.prod.Coprime q <;> simp [finiteProductKernel, hc, hg]

/-- A finite integer-word dictionary. It does not use prime-only agreement
of a licence, and the normalized von Mangoldt factor appears exactly once. -/
private theorem weighted_proper_words_eq_residual
    (cap N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) (omega : ℕ → ℝ) :
    (∑ ps ∈ properChartWords cap 1,
      lambdaWord ps * (omega ps.prod : ℂ) * wordKernel Q rho N ps) =
      finiteProductSignedError (Icc 1 cap) Q N rho
        (labelledProperPowerResidual 1 cap (P5S1SingletonPP.singletonWeight cap omega)) := by
  have hB (t : Fin 1 → Fin (cap + 1)) (ht : t ∈ properLabels cap) :
      labelledProduct t ∈ Icc 1 cap := by
    rw [P5S1SingletonPP.labelledProduct_singleton]
    exact mem_Icc.mpr ⟨properPrimePower_pos (properLabel_zero ht),
      Nat.le_of_lt_succ (t 0).isLt⟩
  change _ = finiteProductSignedError (Icc 1 cap) Q N rho
    (finiteProductMass (properLabels cap) labelledProduct
      (fun t => ((P5S1SingletonPP.singletonWeight cap omega t *
        labelledVonMangoldtWeight t : ℝ) : ℂ)))
  rw [finiteProductSignedError_fibres (properLabels cap) labelledProduct
    (fun t => ((P5S1SingletonPP.singletonWeight cap omega t *
      labelledVonMangoldtWeight t : ℝ) : ℂ)) (Icc 1 cap) Q N rho
    (fun t ht _ => hB t ht)]
  rw [proper_words_image, sum_image]
  · simp_rw [wordKernel_eq_finiteProductKernel, Finset.mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro t _
    simp only [sourceWord_singleton, lambdaWord, List.prod_cons, List.prod_nil, mul_one,
      P5S1SingletonPP.singletonWeight, labelledVonMangoldtWeight, Fin.prod_univ_one,
      P5S1SingletonPP.labelledProduct_singleton, lambdaOverLog_eq_vonMangoldtOverLog,
      Complex.ofReal_mul]
    ring
  · intro t _ u _ htu
    exact sourceWord_injective 1 cap htu

/-- This equality holds on every natural input, including all proper powers. -/
private theorem actual_listExtension_singleton (kap : ℝ) (B N n : ℕ) :
    listExtension (actualLicence kap B N) [n] = smoothNatural kap B N n := by
  rfl

private theorem original_reserve_sum_eq_weighted_words
    (kap kap0 : ℝ) (B K N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    (∑ js ∈ chartBank (2 * N) 1,
      properPowerReserve (actualLicence kap B N) K (2 * N) N kap0 Q rho js) =
      ∑ ps ∈ properChartWords (2 * N) 1,
        lambdaWord ps * (atlasNaturalWeight kap kap0 B K N ps.prod : ℂ) *
          wordKernel Q rho N ps := by
  unfold properPowerReserve
  rw [sum_comm]
  apply sum_congr rfl
  intro ps hps
  have hlen := (words_spec (Icc 1 (2 * N)) 1 ps (properChartWords_spec hps).1).1
  obtain ⟨n, rfl⟩ := asSingleton hlen
  unfold chartBank
  rw [words_sum_cons]
  simp only [words, sum_singleton, originalChart, chartTerm, trimmedWeight,
    tupleProfile, psi, lambdaWord, roughWord, List.prod_cons, List.prod_nil, mul_one,
    actual_listExtension_singleton, ← roughIndicator_cast]
  unfold atlasNaturalWeight chartRoughMultiplier
  push_cast
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  ring

/-- Exact identification of the entire original chart-dependent proper-power
correction with one P3 residual. Every original eta, psi and rough cutoff is
retained inside atlasWeight; the physical kernel and rho are unchanged. -/
theorem original_singleton_properPowerReserve_sum_eq_labelledResidual
    (kap kap0 : ℝ) (B K N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    (∑ js ∈ chartBank (2 * N) 1,
      properPowerReserve (actualLicence kap B N) K (2 * N) N kap0 Q rho js) =
      finiteProductSignedError (Icc 1 (2 * N)) Q N rho
        (labelledProperPowerResidual 1 (2 * N) (atlasWeight kap kap0 B K N)) := by
  rw [original_reserve_sum_eq_weighted_words]
  exact weighted_proper_words_eq_residual (2 * N) N Q rho
    (atlasNaturalWeight kap kap0 B K N)

/-- P3 pays the original Atlas correction uniformly before choosing the
collar order, pre-HB cutoff rank, extra trim, physical Q or signed rho. -/
theorem eventually_original_singleton_atlas_properPower_logAccuracy
    (kap : ℝ) (hkap : kap < 1) (A eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ (B K : ℕ) (kap0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ),
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) →
      (∀ q ∈ Q, |rho q| ≤ 1) →
      ‖∑ js ∈ chartBank (2 * N) 1,
        properPowerReserve (actualLicence kap B N) K (2 * N) N kap0 Q
          (fun q => (rho q : ℂ)) js‖ ≤
        eps * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  have h := ProperPowerChartSum.eventually_labelledProperPowerResidual_logAccuracy
    1 0 0 (M := 1) (C := 2) (c := 1) (K := 1) (Cρ := 1)
    (a := 1 - kap) (θ := 599 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) A eps heps
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with N hmain hN
  intro B K kap0 Q rho hQ hrho
  rw [original_singleton_properPowerReserve_sum_eq_labelledResidual]
  apply hmain (2 * N) (Icc 1 (2 * N)) Q (fun q => (rho q : ℂ))
    (atlasWeight kap kap0 B K N) chi
  · intro b hb
    refine mem_Icc.mpr ⟨(mem_Icc.mp hb).1, (mem_Icc.mp hb).2.trans ?_⟩
    exact_mod_cast Nat.le_ceil ((2 : ℝ) * (N : ℝ))
  · intro q hq
    exact ⟨(hQ q hq).1, by simpa only [one_mul] using (hQ q hq).2.le⟩
  · intro q hq
    simpa only [Complex.norm_real, Real.norm_eq_abs, pow_zero, mul_one] using hrho q hq
  · intro s hs
    exact chi_one hs
  · intro s hs
    exact chi_zero hs
  · intro s
    exact chi_bounds s
  · intro t
    simpa only [pow_zero, mul_one] using atlasWeight_abs_le_one kap kap0 B K N t
  · intro t ht
    simpa only [one_mul] using atlasWeight_effective_geometry kap kap0 B K hN t ht

/-- The signed sum of the original proper-power reserves fits any positive
share of the actual singular normalization, with all later choices uniform. -/
theorem eventually_original_singleton_atlas_properPower_singularNormalization
    (kap : ℝ) (hkap : kap < 1) (tol : ℝ) (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, ∀ (B K : ℕ) (kap0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ),
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) →
      (∀ q ∈ Q, |rho q| ≤ 1) →
      ‖∑ js ∈ chartBank (2 * N) 1,
        properPowerReserve (actualLicence kap B N) K (2 * N) N kap0 Q
          (fun q => (rho q : ℂ)) js‖ ≤
        tol * singularNormalization N := by
  filter_upwards [eventually_original_singleton_atlas_properPower_logAccuracy
    kap hkap 2 (tol * twinPrimeConstant) (mul_pos htol twinPrimeConstant_pos)] with N hN
  intro B K kap0 Q rho hQ hrho
  have herr := hN B K kap0 Q rho hQ hrho
  have hnorm := mul_le_mul_of_nonneg_left (singularNormalization_lower N) htol.le
  calc
    _ ≤ (tol * twinPrimeConstant) * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := herr
    _ = tol * (twinPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) := by
      rw [Real.rpow_two]
      ring
    _ ≤ tol * singularNormalization N := hnorm

end
end ImbalancedChen.P1OriginalSingletonAtlasProperPower
