import ImbalancedChen.Part3ElementaryE1StrictFloor
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Order.Interval.Finset.Nat

namespace ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- All natural points of a closed real interval when the upper endpoint is nonnegative. -/
def realClosedNatInterval (a b : ℝ) : Finset ℕ :=
  Icc ⌈a⌉₊ ⌊b⌋₊

theorem mem_realClosedNatInterval {a b : ℝ} (hb : 0 ≤ b) {n : ℕ} :
    n ∈ realClosedNatInterval a b ↔ a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b := by
  simp only [realClosedNatInterval, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hb]

/-- The closed integer-point allowance is one, including a possible singleton. -/
theorem card_nat_ceiling_floor_le_length_add_one {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ((Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) ≤ b - a + 1 := by
  by_cases hcf : ⌈a⌉₊ ≤ ⌊b⌋₊
  · have hsub : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1 := by omega
    rw [Nat.card_Icc, Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
    have hlo : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have hhi : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (ha.trans hab)
    linarith
  · have hempty : (Icc ⌈a⌉₊ ⌊b⌋₊ : Finset ℕ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hcn, hnf⟩ := Finset.mem_Icc.mp hn
      exact hcf (hcn.trans hnf)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

/-- Actual multiples in any real-supported finite set have the exact length/d+1 bound. -/
theorem real_supported_multiples_card_le (S : Finset ℕ) {a b : ℝ} {d : ℕ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hd : 0 < d)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) :
    ((S.filter (fun n => d ∣ n)).card : ℝ) ≤ (b - a) / (d : ℝ) + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmaps : Set.MapsTo (fun n : ℕ => n / d) (S.filter (fun n => d ∣ n))
      (Icc ⌈a / (d : ℝ)⌉₊ ⌊b / (d : ℝ)⌋₊) := by
    intro n hn
    obtain ⟨hnS, hdn⟩ := Finset.mem_filter.mp hn
    have hq : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) :=
      Nat.cast_div_charZero hdn
    apply Finset.mem_Icc.mpr
    constructor
    · apply Nat.ceil_le.mpr
      rw [hq]
      exact div_le_div_of_nonneg_right (hS n hnS).1 hdR.le
    · apply Nat.le_floor
      rw [hq]
      exact div_le_div_of_nonneg_right (hS n hnS).2 hdR.le
  have hinj : (S.filter (fun n => d ∣ n) : Set ℕ).InjOn (fun n => n / d) := by
    intro n hn m hm hnm
    have hdn : d ∣ n := (Finset.mem_filter.mp hn).2
    have hdm : d ∣ m := (Finset.mem_filter.mp hm).2
    calc
      n = (n / d) * d := (Nat.div_mul_cancel hdn).symm
      _ = (m / d) * d := congrArg (fun q : ℕ => q * d) hnm
      _ = m := Nat.div_mul_cancel hdm
  have hcard : (S.filter (fun n => d ∣ n)).card ≤
      (Icc ⌈a / (d : ℝ)⌉₊ ⌊b / (d : ℝ)⌋₊).card :=
    Finset.card_le_card_of_injOn (fun n : ℕ => n / d) hmaps hinj
  have hcardR :
      ((S.filter (fun n => d ∣ n)).card : ℝ) ≤
        ((Icc ⌈a / (d : ℝ)⌉₊ ⌊b / (d : ℝ)⌋₊).card : ℝ) := by
    exact_mod_cast hcard
  have hquot := card_nat_ceiling_floor_le_length_add_one
    (div_nonneg ha hdR.le) (div_le_div_of_nonneg_right hab hdR.le)
  calc
    ((S.filter (fun n => d ∣ n)).card : ℝ) ≤
        ((Icc ⌈a / (d : ℝ)⌉₊ ⌊b / (d : ℝ)⌋₊).card : ℝ) := hcardR
    _ ≤ b / (d : ℝ) - a / (d : ℝ) + 1 := hquot
    _ = (b - a) / (d : ℝ) + 1 := by rw [sub_div]

/-- Exact finite exchange on the actual supported set; weights may have either sign. -/
theorem sum_real_supported_divisor_weights_swap (S : Finset ℕ) (D : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ S, ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), w d) =
      ∑ d ∈ Icc 1 D, w d * ((S.filter (fun n => d ∣ n)).card : ℝ) := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The finite payment retains the true real length b-a. -/
theorem sum_real_supported_divisor_weights_le (S : Finset ℕ) {a b : ℝ} {D : ℕ}
    (w : ℕ → ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b)
    (hw : ∀ d ∈ Icc 1 D, 0 ≤ w d) :
    (∑ n ∈ S, ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), w d) ≤
      ∑ d ∈ Icc 1 D, w d * ((b - a) / (d : ℝ) + 1) := by
  rw [sum_real_supported_divisor_weights_swap]
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (real_supported_multiples_card_le S ha hab (by
      have := (Finset.mem_Icc.mp hd).1
      omega) hS) (hw d hd)

/-- Strict native truncation followed by the real-supported finite payment. -/
theorem sum_fouvryTau_real_support_floor_payment (S : Finset ℕ) {K : ℕ}
    (hK : 2 ≤ K) {a b Z : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hZ : 2 ≤ Z) (hbZ : b ≤ Z)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) :
    (∑ n ∈ S, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * ((b - a) *
        (∑ d ∈ Icc 1 ⌊realDeletionRadius K Z⌋₊,
          (fouvryTau (K - 1) d : ℝ) / (d : ℝ)) +
        ∑ d ∈ Icc 1 ⌊realDeletionRadius K Z⌋₊, (fouvryTau (K - 1) d : ℝ)) := by
  let D : ℕ := ⌊realDeletionRadius K Z⌋₊
  change (∑ n ∈ S, (fouvryTau K n : ℝ)) ≤
    (K : ℝ) * ((b - a) *
      (∑ d ∈ Icc 1 D, (fouvryTau (K - 1) d : ℝ) / (d : ℝ)) +
      ∑ d ∈ Icc 1 D, (fouvryTau (K - 1) d : ℝ))
  have hpoint : ∀ n ∈ S, (fouvryTau K n : ℝ) ≤
      (K : ℝ) * ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n),
        (fouvryTau (K - 1) d : ℝ) := by
    intro n hn
    have hnR : (0 : ℝ) < n :=
      lt_of_lt_of_le (by linarith : 0 < a) (hS n hn).1
    have hnpos : 0 < n := by exact_mod_cast hnR
    have hcut : n ^ (K - 1) < (D + 1) ^ K :=
      floor_radius_strict_cutoff hK (by linarith : 1 ≤ Z) ((hS n hn).2.trans hbZ)
    have hnat := fouvryTau_le_truncated_divisor_sum_strict hK
      (by omega : 1 ≤ n) hcut
    rw [truncated_divisor_carrier_eq hnpos] at hnat
    exact_mod_cast hnat
  calc
    (∑ n ∈ S, (fouvryTau K n : ℝ)) ≤
        ∑ n ∈ S, (K : ℝ) *
          ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), (fouvryTau (K - 1) d : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (K : ℝ) * (∑ n ∈ S,
        ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), (fouvryTau (K - 1) d : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * ∑ d ∈ Icc 1 D,
        (fouvryTau (K - 1) d : ℝ) * ((b - a) / (d : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left
        (sum_real_supported_divisor_weights_le S (fun d => (fouvryTau (K - 1) d : ℝ))
          (by linarith : 0 ≤ a) hab hS (fun d _hd => Nat.cast_nonneg _))
        (Nat.cast_nonneg K)
    _ = _ := by
      congr 1
      calc
        (∑ d ∈ Icc 1 D, (fouvryTau (K - 1) d : ℝ) * ((b - a) / (d : ℝ) + 1)) =
            ∑ d ∈ Icc 1 D, ((b - a) *
              ((fouvryTau (K - 1) d : ℝ) / (d : ℝ)) + (fouvryTau (K - 1) d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d _hd
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Sharp E1 for every finite subset of a real interval inside [1,Z]. -/
theorem sum_fouvryTau_E1_real_support (S : Finset ℕ) {K : ℕ}
    (hK : 2 ≤ K) {a b Z : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hZ : 2 ≤ Z) (hbZ : b ≤ Z)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) :
    (∑ n ∈ S, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * ((b - a) * (1 + Real.log Z) ^ (K - 1) +
        Z ^ (1 - 1 / (K : ℝ)) * (1 + Real.log Z) ^ (K - 2)) := by
  have hZ1 : 1 ≤ Z := by linarith
  have hfin := sum_fouvryTau_real_support_floor_payment S hK ha hab hZ hbZ hS
  have hmean := native_floor_tau_payment hK (realDeletionRadius_bounds hK hZ1).1
    (realDeletionRadius_bounds hK hZ1).2 (sub_nonneg.mpr hab)
  rw [← realDeletionRadius_eq_manuscript hK Z]
  exact hfin.trans (mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg K))

/-- Closed real endpoints, without rounding the geometric length. -/
theorem sum_fouvryTau_E1_real_closed_interval {K : ℕ} (hK : 2 ≤ K)
    {a b Z : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hZ : 2 ≤ Z) (hbZ : b ≤ Z) :
    (∑ n ∈ realClosedNatInterval a b, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * ((b - a) * (1 + Real.log Z) ^ (K - 1) +
        Z ^ (1 - 1 / (K : ℝ)) * (1 + Real.log Z) ^ (K - 2)) := by
  refine sum_fouvryTau_E1_real_support (realClosedNatInterval a b)
    hK ha hab hZ hbZ ?_
  intro n hn
  exact (mem_realClosedNatInterval (by linarith : 0 ≤ b)).mp hn

/-- A concrete finite natural preimage for any choice of interval endpoints. -/
def realIntervalPoints (a b : ℝ) (I : Set ℝ) : Finset ℕ :=
  (realClosedNatInterval a b).filter (fun n => (n : ℝ) ∈ I)

theorem mem_realIntervalPoints {a b : ℝ} {I : Set ℝ} (hb : 0 ≤ b)
    (hI : I ⊆ Set.Icc a b) {n : ℕ} :
    n ∈ realIntervalPoints a b I ↔ (n : ℝ) ∈ I := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · intro hn
    exact Finset.mem_filter.mpr
      ⟨(mem_realClosedNatInterval hb).mpr (hI hn), hn⟩

/-- Any open, closed or half-open real interval uses its exact natural preimage. -/
theorem sum_fouvryTau_E1_real_interval {K : ℕ} (hK : 2 ≤ K)
    {a b Z : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hZ : 2 ≤ Z) (hbZ : b ≤ Z)
    (I : Set ℝ) (hI : I ⊆ Set.Icc a b) :
    (∑ n ∈ realIntervalPoints a b I, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * ((b - a) * (1 + Real.log Z) ^ (K - 1) +
        Z ^ (1 - 1 / (K : ℝ)) * (1 + Real.log Z) ^ (K - 2)) := by
  refine sum_fouvryTau_E1_real_support (realIntervalPoints a b I)
    hK ha hab hZ hbZ ?_
  intro n hn
  exact hI ((mem_realIntervalPoints (by linarith : 0 ≤ b) hI).mp hn)

/-- Literal real-length E1: exact K, all Y>=0, and no minimum-length premise. -/
theorem sum_fouvryTau_E1_real_interval_length {K : ℕ} (hK : 2 ≤ K)
    {a Z Y : ℝ} (ha : 1 ≤ a) (hZ : 2 ≤ Z) (hY : 0 ≤ Y) (haYZ : a + Y ≤ Z)
    (I : Set ℝ) (hI : I ⊆ Set.Icc a (a + Y)) :
    (∑ n ∈ realIntervalPoints a (a + Y) I, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * (Y * (1 + Real.log Z) ^ (K - 1) +
        Z ^ (1 - 1 / (K : ℝ)) * (1 + Real.log Z) ^ (K - 2)) := by
  have hlength : a + Y - a = Y := by ring
  have h := sum_fouvryTau_E1_real_interval hK ha (by linarith : a ≤ a + Y)
    hZ haYZ I hI
  simpa only [hlength] using h

end
end ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment
