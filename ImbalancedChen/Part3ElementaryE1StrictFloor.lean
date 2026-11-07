import ImbalancedChen.Part3ElementaryIntervalDivisibility
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

namespace ImbalancedChen.Part3.ElementaryTauTruncation

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

section StrictFinite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact integer cutoff uses a strict successor power. -/
theorem exists_deletedProduct_le_strict (a : ι → ℕ) {n D : ℕ}
    (hcard : 2 ≤ Fintype.card ι) (hprod : (∏ j, a j) = n)
    (hcut : n ^ (Fintype.card ι - 1) < (D + 1) ^ Fintype.card ι) :
    ∃ i : ι, deletedProduct a i ≤ D := by
  have hcpos : 0 < Fintype.card ι := by omega
  have hne : (Finset.univ : Finset ι).Nonempty :=
    Finset.card_pos.mp (by simpa only [Finset.card_univ] using hcpos)
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ a hne
  refine ⟨i, ?_⟩
  have hbound : deletedProduct a i ≤ a i ^ (Fintype.card ι - 1) := by
    simpa only [deletedProduct, Finset.card_erase_of_mem hi, Finset.card_univ] using
      (Finset.prod_le_pow_card ((Finset.univ : Finset ι).erase i) a (a i)
        (fun j _hj => hmax j (Finset.mem_univ j)))
  have hpower : deletedProduct a i ^ Fintype.card ι ≤ n ^ (Fintype.card ι - 1) := by
    calc
      deletedProduct a i ^ Fintype.card ι =
          deletedProduct a i ^ ((Fintype.card ι - 1) + 1) := by congr 1; omega
      _ = deletedProduct a i ^ (Fintype.card ι - 1) * deletedProduct a i := pow_succ _ _
      _ ≤ deletedProduct a i ^ (Fintype.card ι - 1) * a i ^ (Fintype.card ι - 1) :=
        Nat.mul_le_mul_left _ hbound
      _ = (deletedProduct a i * a i) ^ (Fintype.card ι - 1) := (mul_pow _ _ _).symm
      _ = n ^ (Fintype.card ι - 1) := by rw [deletedProduct_mul, hprod]
  by_contra h
  have hsucc : D + 1 ≤ deletedProduct a i := by omega
  have hmono : (D + 1) ^ Fintype.card ι ≤ deletedProduct a i ^ Fintype.card ι :=
    pow_le_pow_left₀ (Nat.zero_le _) hsucc _
  exact (not_lt_of_ge (hmono.trans hpower)) hcut

/-- The divisor-fiber partition itself does not depend on any cutoff-power premise. -/
theorem card_smallCover_eq_sum_deletionFibers (S : Finset (ι → ℕ)) {n D : ℕ}
    (hn : 0 < n) (hprod : ∀ a ∈ S, (∏ j, a j) = n) (i : ι) :
    (S.filter (fun a => deletedProduct a i ≤ D)).card =
      ∑ d ∈ truncatedDivisors n D, (deletionFiber S i d).card := by
  have hmaps : Set.MapsTo (fun a => deletedProduct a i)
      (S.filter (fun a => deletedProduct a i ≤ D)) (truncatedDivisors n D) := by
    intro a ha
    obtain ⟨haS, haD⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨deletedProduct_dvd (hprod a haS) i, hn.ne'⟩, haD⟩
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => deletedProduct a i)
    (s := S.filter (fun a => deletedProduct a i ≤ D)) (t := truncatedDivisors n D) hmaps]
  apply Finset.sum_congr rfl
  intro d hd
  have hdD : d ≤ D := (Finset.mem_filter.mp hd).2
  have hfiber : ((S.filter (fun a => deletedProduct a i ≤ D)).filter
      (fun a => deletedProduct a i = d)) = S.filter (fun a => deletedProduct a i = d) := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · intro ha
      exact ⟨ha.1.1, ha.2⟩
    · rintro ⟨haS, had⟩
      exact ⟨⟨haS, had.le.trans hdD⟩, had⟩
  rw [hfiber]
  unfold deletionFiber
  symm
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact eraseAt_injective_of_product hn (hprod a (Finset.mem_filter.mp ha).1)
    (hprod b (Finset.mem_filter.mp hb).1) i hab

/-- The original indexed cover consumer, with only the strictly sufficient cutoff changed. -/
theorem card_le_sum_deletionFibers_strict (S : Finset (ι → ℕ)) {n D : ℕ}
    (hn : 0 < n) (hcard : 2 ≤ Fintype.card ι)
    (hprod : ∀ a ∈ S, (∏ j, a j) = n)
    (hcut : n ^ (Fintype.card ι - 1) < (D + 1) ^ Fintype.card ι) :
    S.card ≤ ∑ i : ι, ∑ d ∈ truncatedDivisors n D, (deletionFiber S i d).card := by
  have hcover : S ⊆ (Finset.univ : Finset ι).biUnion
      (fun i => S.filter (fun a => deletedProduct a i ≤ D)) := by
    intro a ha
    obtain ⟨i, hi⟩ := exists_deletedProduct_le_strict a hcard (hprod a ha) hcut
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨ha, hi⟩⟩
  calc
    S.card ≤ ∑ i : ι, (S.filter (fun a => deletedProduct a i ≤ D)).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ = _ := Finset.sum_congr rfl (fun i _ => card_smallCover_eq_sum_deletionFibers S hn hprod i)

end StrictFinite

/-- Exact native tau truncation under the sharp strict-successor condition. -/
theorem fouvryTau_le_truncated_divisor_sum_strict {K n D : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) (hcut : n ^ (K - 1) < (D + 1) ^ K) :
    fouvryTau K n ≤ K *
      (∑ d ∈ n.divisors.filter (fun d => d ≤ D), fouvryTau (K - 1) d) := by
  have hfin : (orderedFactorTuples K n).card ≤
      ∑ i : Fin K, ∑ d ∈ truncatedDivisors n D,
        (deletionFiber (orderedFactorTuples K n) i d).card := by
    apply card_le_sum_deletionFibers_strict (hn := by omega)
    · simpa only [Fintype.card_fin] using hK
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
    · simpa only [Fintype.card_fin] using hcut
  calc
    fouvryTau K n = (orderedFactorTuples K n).card :=
      (card_orderedFactorTuples_eq_fouvryTau K n (by omega)).symm
    _ ≤ ∑ i : Fin K, ∑ d ∈ truncatedDivisors n D,
        (deletionFiber (orderedFactorTuples K n) i d).card := hfin
    _ ≤ ∑ _i : Fin K, ∑ d ∈ truncatedDivisors n D, fouvryTau (K - 1) d := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro d hd
      exact card_deletionFiber_orderedFactorTuples_le_fouvryTau hK (by omega)
        (Finset.mem_filter.mp hd).1 i
    _ = _ := by
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
        truncatedDivisors]

end
end ImbalancedChen.Part3.ElementaryTauTruncation

namespace ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment
noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem sum_fouvryTau_interval_payment_strict {K A B D : ℕ}
    (hK : 2 ≤ K) (hAB : A ≤ B) (hcut : B ^ (K - 1) < (D + 1) ^ K) :
    (∑ n ∈ Ioc A B, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * ∑ d ∈ Icc 1 D,
        (fouvryTau (K - 1) d : ℝ) * (((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1) := by
  have hpoint : ∀ n ∈ Ioc A B, (fouvryTau K n : ℝ) ≤
      (K : ℝ) * ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n),
        (fouvryTau (K - 1) d : ℝ) := by
    intro n hn
    obtain ⟨hAn, hnB⟩ := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le A) hAn
    have hpow : n ^ (K - 1) ≤ B ^ (K - 1) :=
      pow_le_pow_left₀ (Nat.zero_le n) hnB _
    have hnat := fouvryTau_le_truncated_divisor_sum_strict hK (by omega : 1 ≤ n)
      (hpow.trans_lt hcut)
    rw [truncated_divisor_carrier_eq hnpos] at hnat
    exact_mod_cast hnat
  calc
    (∑ n ∈ Ioc A B, (fouvryTau K n : ℝ)) ≤
        ∑ n ∈ Ioc A B, (K : ℝ) *
          ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), (fouvryTau (K - 1) d : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (K : ℝ) * (∑ n ∈ Ioc A B,
        ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), (fouvryTau (K - 1) d : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * ∑ d ∈ Icc 1 D,
        (fouvryTau (K - 1) d : ℝ) * (((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left
        (sum_interval_divisor_weights_le (fun d => (fouvryTau (K - 1) d : ℝ)) hAB
          (fun d _hd => Nat.cast_nonneg _)) (Nat.cast_nonneg K)

/-- The separated reciprocal and ordinary payments needed by the E1 route. -/
theorem sum_fouvryTau_interval_payment_strict_split {K A B D : ℕ}
    (hK : 2 ≤ K) (hAB : A ≤ B) (hcut : B ^ (K - 1) < (D + 1) ^ K) :
    (∑ n ∈ Ioc A B, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * (((B : ℝ) - (A : ℝ)) *
        (∑ d ∈ Icc 1 D, (fouvryTau (K - 1) d : ℝ) / (d : ℝ)) +
        ∑ d ∈ Icc 1 D, (fouvryTau (K - 1) d : ℝ)) := by
  calc
    (∑ n ∈ Ioc A B, (fouvryTau K n : ℝ)) ≤
        (K : ℝ) * ∑ d ∈ Icc 1 D,
          (fouvryTau (K - 1) d : ℝ) * (((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1) :=
      sum_fouvryTau_interval_payment_strict hK hAB hcut
    _ = _ := by
      congr 1
      calc
        (∑ d ∈ Icc 1 D,
            (fouvryTau (K - 1) d : ℝ) * (((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1)) =
            ∑ d ∈ Icc 1 D, (((B : ℝ) - (A : ℝ)) *
              ((fouvryTau (K - 1) d : ℝ) / (d : ℝ)) + (fouvryTau (K - 1) d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d _hd
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The manuscript radius, written as a natural-subtraction quotient exponent. -/
def realDeletionRadius (K : ℕ) (Z : ℝ) : ℝ := Z ^ (((K - 1 : ℕ) : ℝ) / (K : ℝ))

theorem realDeletionRadius_eq_manuscript {K : ℕ} (hK : 2 ≤ K) (Z : ℝ) :
    realDeletionRadius K Z = Z ^ (1 - 1 / (K : ℝ)) := by
  have hKn : K ≠ 0 := by omega
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hKn
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
  unfold realDeletionRadius
  congr 1
  rw [hcast]
  field_simp [hKR]

theorem realDeletionRadius_pow {K : ℕ} (hK : 2 ≤ K) {Z : ℝ} (hZ : 0 ≤ Z) :
    realDeletionRadius K Z ^ K = Z ^ (K - 1) := by
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  unfold realDeletionRadius
  rw [← Real.rpow_mul_natCast hZ _ K, div_mul_cancel₀ _ hKR, Real.rpow_natCast]

theorem realDeletionRadius_bounds {K : ℕ} (hK : 2 ≤ K) {Z : ℝ} (hZ : 1 ≤ Z) :
    1 ≤ realDeletionRadius K Z ∧ realDeletionRadius K Z ≤ Z := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hnum : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.sub_le K 1)
  constructor
  · exact Real.one_le_rpow hZ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact Real.rpow_le_self_of_one_le hZ ((div_le_iff₀ hKR).mpr (by simp))

/-- The true floor supplies a strict successor-power cutoff, without any rounding loss. -/
theorem floor_radius_strict_cutoff {K B : ℕ} (hK : 2 ≤ K) {Z : ℝ}
    (hZ : 1 ≤ Z) (hBZ : (B : ℝ) ≤ Z) :
    B ^ (K - 1) < (⌊realDeletionRadius K Z⌋₊ + 1) ^ K := by
  have hR0 : 0 ≤ realDeletionRadius K Z := le_trans zero_le_one (realDeletionRadius_bounds hK hZ).1
  have hlt : realDeletionRadius K Z ^ K <
      ((⌊realDeletionRadius K Z⌋₊ : ℝ) + 1) ^ K :=
    pow_lt_pow_left₀ (Nat.lt_floor_add_one _) hR0 (by omega : K ≠ 0)
  rw [realDeletionRadius_pow hK (by linarith : 0 ≤ Z)] at hlt
  have hBpow : (B : ℝ) ^ (K - 1) ≤ Z ^ (K - 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg B) hBZ _
  exact_mod_cast hBpow.trans_lt hlt

/-- Exact native means at the genuine real cutoff and its floor; no interval supplier assumed. -/
theorem native_floor_tau_payment {K : ℕ} (hK : 2 ≤ K) {R Z Y : ℝ}
    (hR : 1 ≤ R) (hRZ : R ≤ Z) (hY : 0 ≤ Y) :
    Y * (∑ d ∈ Icc 1 ⌊R⌋₊, (fouvryTau (K - 1) d : ℝ) / (d : ℝ)) +
        (∑ d ∈ Icc 1 ⌊R⌋₊, (fouvryTau (K - 1) d : ℝ)) ≤
      Y * (1 + Real.log Z) ^ (K - 1) + R * (1 + Real.log Z) ^ (K - 2) := by
  have hI : Icc 1 ⌊R⌋₊ = Ioc 0 ⌊R⌋₊ := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hrec := sum_fouvryTau_div_le_real (K - 1) hR
  have hord := sum_fouvryTau_le_real (k := K - 1) (by omega) hR
  have hexp : (K - 1) - 1 = K - 2 := by omega
  rw [← hI] at hrec hord
  rw [hexp] at hord
  have hL0 : 0 ≤ 1 + Real.log R := by
    have := Real.log_nonneg hR
    linarith
  have hL : 1 + Real.log R ≤ 1 + Real.log Z :=
    add_le_add_right (Real.log_le_log (by linarith : 0 < R) hRZ) 1
  have hp1 : (1 + Real.log R) ^ (K - 1) ≤ (1 + Real.log Z) ^ (K - 1) :=
    pow_le_pow_left₀ hL0 hL _
  have hp2 : (1 + Real.log R) ^ (K - 2) ≤ (1 + Real.log Z) ^ (K - 2) :=
    pow_le_pow_left₀ hL0 hL _
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hrec.trans hp1) hY)
    (hord.trans (mul_le_mul_of_nonneg_left hp2 (by linarith : 0 ≤ R)))

/-- Sharp E1 for positive natural-endpoint intervals; no minimum interval length is imposed. -/
theorem sum_fouvryTau_E1_nat_endpoints {K A B : ℕ} (hK : 2 ≤ K)
    (hAB : A ≤ B) {Z : ℝ} (hZ : 2 ≤ Z) (hBZ : (B : ℝ) ≤ Z) :
    (∑ n ∈ Ioc A B, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * (((B : ℝ) - (A : ℝ)) * (1 + Real.log Z) ^ (K - 1) +
        Z ^ (1 - 1 / (K : ℝ)) * (1 + Real.log Z) ^ (K - 2)) := by
  have hZ1 : 1 ≤ Z := by linarith
  have hb := floor_radius_strict_cutoff hK hZ1 hBZ
  have hfin := sum_fouvryTau_interval_payment_strict_split hK hAB hb
  have hlength : 0 ≤ (B : ℝ) - (A : ℝ) := sub_nonneg.mpr (by exact_mod_cast hAB)
  have hmean := native_floor_tau_payment hK (realDeletionRadius_bounds hK hZ1).1
    (realDeletionRadius_bounds hK hZ1).2 hlength
  rw [← realDeletionRadius_eq_manuscript hK Z]
  exact hfin.trans (mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg K))

end
end ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment
