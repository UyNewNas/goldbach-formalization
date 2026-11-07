import ImbalancedChen.ChenInitialPrimeSource
import ImbalancedChen.PowerErrorBudget
import MathlibNt.SieveTheory.LiLiuGoldbachBadBound

/-!
# Actual source and normalization for the current first Chen mean

The literal upstream S1 source is transferred to the actual current-style
sifted prime-difference source at a smaller cutoff. The primes dividing N
are accounted for by their genuine finite count. The actual two singular
series are identified, with no leading factor of two, and the fixed-ratio
four coefficient is evaluated exactly. The complete centre-prime correction
is proved negligible in singularNormalization.

The actual eventual Upsilon1 mean is supplied separately by
`CurrentChenInitialMean`, which consumes these proved source interfaces.
This source module requires strict elaboration, bundled kernel replay and
an independent axiom audit before its candidate status can be removed.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.SwitchingPrinciple (dimensionOneLowerLinearSieveFactor)

/-- Exact reindexing of the two genuine convergent odd-prime products.
The upstream factors at all other natural indices are literally one. -/
theorem currentChen_twinPrimeConstant_eq_liuUniversalProduct :
    twinPrimeConstant = MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct := by
  have hsupp :
      Function.mulSupport
          (fun p : ℕ => 1 + MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation p) ⊆
        {p : ℕ | Nat.Prime p ∧ 2 < p} := by
    intro p hp
    by_contra h
    change 1 + MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation p ≠ 1 at hp
    exact hp (by simp [MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation, h])
  unfold twinPrimeConstant MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct
  rw [← tprod_subtype_eq_of_mulSupport_subset hsupp]
  apply tprod_congr
  intro p
  exact (MathlibNt.SieveTheory.SingularSeries.one_add_liuBaseDeviation_eq_baseFactor
    p.property.1 p.property.2).symm

/-- Both series use the same finite odd-prime-divisor correction and the
same infinite odd-prime product, with no leading factor two. -/
theorem currentChen_singularSeries_eq_liuSingularSeries (N : ℕ) :
    singularSeries N = MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N := by
  rw [singularSeries, currentChen_twinPrimeConstant_eq_liuUniversalProduct,
    MathlibNt.SieveTheory.SingularSeries.liuSingularSeries]
  unfold oddPrimeDivisors MathlibNt.SieveTheory.SingularSeries.liuCorrection
    MathlibNt.SieveTheory.SingularSeries.liuCorrectionFactor
  exact mul_comm _ _

/-- The lower sieve's fixed ratio four has an empty integral correction.
This proves its exact coefficient directly from the actual factor definition. -/
theorem currentChen_initial_sieve_coefficient :
    (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
        dimensionOneLowerLinearSieveFactor 4 =
      (33 / 4 : ℝ) * Real.log 3 := by
  have hf : dimensionOneLowerLinearSieveFactor 4 =
      (2 * Real.exp Real.eulerMascheroniConstant / 4) * Real.log 3 := by
    unfold dimensionOneLowerLinearSieveFactor
    norm_num
  have he : Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp Real.eulerMascheroniConstant = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hf]
  calc
    (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
        ((2 * Real.exp Real.eulerMascheroniConstant / 4) * Real.log 3) =
      ((33 / 4 : ℝ) * Real.log 3) *
        (Real.exp (-Real.eulerMascheroniConstant) *
          Real.exp Real.eulerMascheroniConstant) := by ring
    _ = _ := by rw [he, mul_one]

/-- A literal upstream S1 count is bounded by the actual current-style
sifted source at any smaller cutoff, plus the complete centre-prime loss.
The proof retains every prime endpoint and pays the ignored divisor mask. -/
theorem currentChen_goldbachS1_le_sifted_add_primeFactors
    (N : ℕ) (tau A z : ℝ) (hN : N ≠ 0) (htau : 0 ≤ tau) (hAz : A ≤ z) :
    (goldbachS1 (goldbachDifferenceCarrier N tau) N z : ℝ) ≤
      ((chenSiftedPrimeSource N A).card : ℝ) + (N.primeFactors.card : ℝ) := by
  classical
  let S := (goldbachDifferenceCarrier N tau).filter (literalHPoint N 1 z)
  have hgood :
      S.filter (fun n => Nat.Coprime n N) ⊆ chenSiftedPrimeSource N A := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnS, hcop⟩
    rcases Finset.mem_filter.mp hnS with ⟨hnSource, hsieve⟩
    rcases Finset.mem_image.mp hnSource with ⟨P, hP, rfl⟩
    rcases (mem_goldbachPrimeCarrier_iff htau).mp hP with ⟨hprime, hcut⟩
    have hPNr : (P : ℝ) < N := by
      nlinarith [mul_nonneg htau (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hPN : P < N := by exact_mod_cast hPNr
    have hcopP : Nat.Coprime P N :=
      (Nat.coprime_self_sub_left hPN.le).mp hcop
    have hcarrier : P ∈ chenAdditivePrimeCarrier N :=
      mem_chenAdditivePrimeCarrier.mpr ⟨hPN, hprime, hcopP⟩
    rw [chenSiftedPrimeSource_eq_rough_filter]
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨P, hcarrier, rfl⟩, ?_⟩
    intro q hq hqd
    exact hAz.trans (hsieve.2 q hq hqd
      (hq.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hqd)))
  have hbadSubset :
      S.filter (fun n => ¬Nat.Coprime n N) ⊆
        (goldbachDifferenceCarrier N tau).filter (fun n => ¬Nat.Coprime n N) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnS, hnBad⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnS).1, hnBad⟩
  have hbadOriginal :
      ((goldbachDifferenceCarrier N tau).filter
        (fun n => ¬Nat.Coprime n N)).card ≤ N.primeFactors.card := by
    have hbadBound := goldbachBadCount_le_primeFactors N tau hN
    unfold goldbachBadCount at hbadBound
    exact_mod_cast hbadBound
  have hbad :
      (S.filter (fun n => ¬Nat.Coprime n N)).card ≤ N.primeFactors.card :=
    (Finset.card_le_card hbadSubset).trans hbadOriginal
  have hgoodCount := Finset.card_le_card hgood
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun n => Nat.Coprime n N)
  have hcount : S.card ≤ (chenSiftedPrimeSource N A).card + N.primeFactors.card := by
    omega
  change ((S.card : ℤ) : ℝ) ≤ _
  exact_mod_cast hcount

/-- The exact noncoprime-source correction is negligible in the actual
manuscript normalization. This consumes the proved distinct-prime product
bound and the proved fixed power-log absorption theorem. -/
theorem eventually_currentChen_primeFactors_negligible
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      (N.primeFactors.card : ℝ) ≤ epsilon * singularNormalization N := by
  filter_upwards
    [eventually_powerLog_le_singularNormalization
      (1 / Real.log 2) 0 1 (by norm_num) epsilon hepsilon,
      eventually_ge_atTop (1 : ℕ)] with N herr hN
  calc
    (N.primeFactors.card : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
      have hpow : (2 : ℝ) ^ N.primeFactors.card ≤ (N : ℝ) :=
        chen_pow_primeFactors_card_le (by omega) (by norm_num)
          (fun p hp _ => by exact_mod_cast hp.two_le)
      have hlog := Real.log_le_log (by positivity :
        (0 : ℝ) < (2 : ℝ) ^ N.primeFactors.card) hpow
      rw [Real.log_pow] at hlog
      exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
    _ = (1 / Real.log 2) * (N : ℝ) ^ (0 : ℝ) * Real.log (N : ℝ) ^ 1 := by
      rw [Real.rpow_zero, pow_one]
      ring
    _ ≤ epsilon * singularNormalization N := herr

end

end ImbalancedChen
