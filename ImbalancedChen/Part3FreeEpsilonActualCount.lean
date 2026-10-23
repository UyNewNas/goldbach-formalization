import ImbalancedChen.Part3LichtmanSignedDifferenceMultiplicity
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import ImbalancedChen.Part3ActualM2FinitePoissonAdapter
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
SOURCEONLY / UNCOMPILED. No actual source or parent is changed.
This is a free-epsilon bound on the ACTUAL divisorMaximum and harmonic
factor, followed by the actual block support needed to avoid a spurious
global-Z loss. It neither supplies a spectral estimate nor assumes one.
The final finite beta-carrier restriction / 576 consumer is NOT asserted.
-/
namespace ImbalancedChen.Part3.FreeEpsilonActualCountSourceOnly
noncomputable section
open Classical Finset
open LichtmanSignedDifferenceMultiplicity
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators

/-- A deliberately explicit size, valid even when H or G is not positive. -/
def countSize (R H G : ℝ) : ℝ := 1 + (supportCap R H G : ℝ) + 2 * R

/-- Also applies to a genuine truncated nu-harmonic sum, without erasing
any extra nu^theta or other spectral weight. -/
theorem harmonic_floor_free_epsilon {eps Y : ℝ} (heps : 0 < eps) (hY : 1 ≤ Y) :
    (harmonic (Nat.floor Y) : ℝ) ≤ (1 + 1 / eps) * Y ^ eps := by
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hY) heps
  have hone := Real.one_le_rpow hY heps.le
  calc
    _ ≤ 1 + Real.log Y := harmonic_floor_le_one_add_log Y hY
    _ ≤ 1 + Y ^ eps / eps := by
      simpa only [add_comm] using (add_le_add_left hlog 1)
    _ ≤ (1 + 1 / eps) * Y ^ eps := by
      rw [add_mul, one_mul, div_eq_mul_inv, one_div]
      nlinarith

theorem actual_count_cost_free_epsilon {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ R H G : ℝ, 1 ≤ R →
      (divisorMaximum R H G : ℝ) ^ 5 * (harmonic (Nat.floor (2 * R)) : ℝ) ≤
        C * countSize R H G ^ eps := by
  obtain ⟨K, hK, htau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show 0 < eps / 10 by positivity)
  refine ⟨K ^ 5 * (1 + 1 / (eps / 2)), by positivity, ?_⟩
  intro R H G hR
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  let W := countSize R H G
  have hW : 1 ≤ W := by dsimp [W, countSize]; linarith [Nat.cast_nonneg (supportCap R H G) (α := ℝ)]
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hcapW : (supportCap R H G : ℝ) ≤ W := by
    dsimp [W, countSize]
    linarith
  have hRW : 2 * R ≤ W := by dsimp [W, countSize]; linarith [Nat.cast_nonneg (supportCap R H G) (α := ℝ)]
  have hD : (divisorMaximum R H G : ℝ) ≤ K * W ^ (eps / 10) := by
    by_cases hs : (Icc 1 (supportCap R H G)).Nonempty
    · obtain ⟨n, hn, heq⟩ := exists_mem_eq_sup _ hs (fun n : ℕ => n.divisors.card)
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1
      have hnW : (n : ℝ) ≤ W :=
        (show (n : ℝ) ≤ supportCap R H G by exact_mod_cast (mem_Icc.mp hn).2).trans hcapW
      change (((Icc 1 (supportCap R H G)).sup (fun n : ℕ => n.divisors.card) : ℕ) : ℝ) ≤ _
      rw [heq]
      have ht : (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ (eps / 10) := by
        simpa only [fouvryTau_two] using htau n hnpos
      exact ht.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) hnW (by positivity)) hK.le)
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hs
      simp only [divisorMaximum, hempty, Finset.sup_empty]
      rw [Nat.bot_eq_zero, Nat.cast_zero]
      exact mul_nonneg hK.le (Real.rpow_nonneg hW0.le (eps / 10))
  have hD5 : (divisorMaximum R H G : ℝ) ^ 5 ≤ K ^ 5 * W ^ (eps / 2) := by
    calc
      _ ≤ (K * W ^ (eps / 10)) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hD 5
      _ = K ^ 5 * W ^ (eps / 2) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hW0.le]
        congr 2; ring
  have hhar : (harmonic (Nat.floor (2 * R)) : ℝ) ≤
      (1 + 1 / (eps / 2)) * W ^ (eps / 2) := by
    have hlog := Real.log_le_rpow_div (show 0 ≤ 2 * R by linarith)
      (show 0 < eps / 2 by positivity)
    have hp := Real.rpow_le_rpow (show 0 ≤ 2 * R by linarith) hRW
      (show 0 ≤ eps / 2 by positivity)
    have hone := Real.one_le_rpow hW (show 0 ≤ eps / 2 by positivity)
    calc
      _ ≤ 1 + Real.log (2 * R) := harmonic_floor_le_one_add_log _ (by linarith)
      _ ≤ 1 + W ^ (eps / 2) / (eps / 2) := by
        simpa only [add_comm] using
          (add_le_add_left (hlog.trans (div_le_div_of_nonneg_right hp (by positivity))) 1)
      _ ≤ (1 + 1 / (eps / 2)) * W ^ (eps / 2) := by
        rw [add_mul, one_mul, div_eq_mul_inv, one_div]
        nlinarith
  have hhar0 : (0 : ℝ) ≤ (harmonic (Nat.floor (2 * R)) : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic (Nat.floor (2 * R)) by
      unfold harmonic
      positivity)
  calc
    _ ≤ (K ^ 5 * W ^ (eps / 2)) *
        ((1 + 1 / (eps / 2)) * W ^ (eps / 2)) :=
      mul_le_mul hD5 hhar hhar0 (by positivity)
    _ = (K ^ 5 * (1 + 1 / (eps / 2))) * W ^ eps := by
      have hp : W ^ (eps / 2) * W ^ (eps / 2) = W ^ eps := by
        rw [← Real.rpow_add hW0]
        congr 1; ring
      calc
        _ = (K ^ 5 * (1 + 1 / (eps / 2))) *
            (W ^ (eps / 2) * W ^ (eps / 2)) := by ring
        _ = _ := by rw [hp]

theorem countSize_le_product_square {R H G : ℝ}
    (hR : 1 ≤ R) (hH : 1 ≤ H) (hG : 1 ≤ G) :
    countSize R H G ≤ 12 * (G * H * R) ^ 2 := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hGH : 1 ≤ G * H := by
    simpa only [one_mul] using mul_le_mul hG hH zero_le_one (zero_le_one.trans hG)
  have hUR : R ≤ G * H * R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hGH hR0
  have hU : 1 ≤ G * H * R := hR.trans hUR
  have hUU : G * H * R ≤ (G * H * R) ^ 2 := by
    simpa only [mul_one, pow_two] using
      mul_le_mul_of_nonneg_left hU (zero_le_one.trans hU)
  have hsquare : R ^ 2 ≤ (G * H * R) ^ 2 :=
    (sq_le_sq₀ hR0 (zero_le_one.trans hU)).mpr hUR
  have hmax : max (4 * R ^ 2) (8 * G * H * R) ≤ 8 * (G * H * R) ^ 2 := by
    apply max_le
    · nlinarith [sq_nonneg (G * H * R)]
    · nlinarith
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ max (4 * R ^ 2) (8 * G * H * R) from
      (by positivity : 0 ≤ 4 * R ^ 2).trans (le_max_left _ _))
  change (Nat.ceil (max (4 * R ^ 2) (8 * G * H * R)) : ℝ) < _ at hceil
  unfold countSize supportCap
  nlinarith

/-- Same actual count cost, arbitrary positive exponent, with no H<=x^C premise. -/
theorem actual_count_cost_product_free_epsilon {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ R H G : ℝ, 1 ≤ R → 1 ≤ H → 1 ≤ G →
      (divisorMaximum R H G : ℝ) ^ 5 * (harmonic (Nat.floor (2 * R)) : ℝ) ≤
        C * (G * H * R) ^ eps := by
  obtain ⟨K, hK, hcost⟩ := actual_count_cost_free_epsilon (show 0 < eps / 2 by positivity)
  refine ⟨K * (12 : ℝ) ^ (eps / 2), by positivity, ?_⟩
  intro R H G hR hH hG
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hU : 0 ≤ G * H * R := by positivity
  have hW : 0 ≤ countSize R H G := by unfold countSize; positivity
  calc
    _ ≤ K * countSize R H G ^ (eps / 2) := hcost R H G hR
    _ ≤ K * (12 * (G * H * R) ^ 2) ^ (eps / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hW
        (countSize_le_product_square hR hH hG) (by positivity)) hK.le
    _ = (K * (12 : ℝ) ^ (eps / 2)) * (G * H * R) ^ eps := by
      have hp : ((G * H * R) ^ 2) ^ (eps / 2) = (G * H * R) ^ eps := by
        rw [← Real.rpow_natCast_mul hU]
        congr 1
        ring
      rw [Real.mul_rpow (by norm_num) (sq_nonneg _), hp]
      ring

open _root_.P3ActualLogAdapterSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly

/-- The actual shortened block retains this Z-independent frequency height. -/
theorem actual_block_abs_le {d : MediumAtom} {D : ℕ} {Z : ℝ}
    {tag : ℕ × Bool} {h : ℤ} (hh : h ∈ block d D Z tag) :
    h ≠ 0 ∧ |(h : ℝ)| ≤ (2 * Hnat tag.1 : ℕ) := by
  have hf := block_facts hh
  refine ⟨hf.1, ?_⟩
  have hi := (div_le_iff₀ (Hreal_pos tag.1)).mp hf.2.2.2
  change |(h : ℝ)| ≤ 2 * (Hnat tag.1 : ℝ) at hi
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hi

/-- This is the ORIGINAL mode coefficient, including its residue and sign gates. -/
theorem actual_omega_zero_above_block (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l)) (h : ℤ)
    (hh : (2 * Hnat tag.1 : ℕ) < |(h : ℝ)|) :
    actualModeOmega e D g l Z tag m negative k h = 0 := by
  have hnot : h ∉ block e D Z tag := fun hb => (not_lt_of_ge (actual_block_abs_le hb).2) hh
  exact if_neg hnot

/-- Separation of the geometric cost from block decay; independent of Z. -/
theorem block_product_le_scale_times_decay {T G R L : ℝ}
    (hT : 0 < T) (hG : 0 ≤ G) (hR : 0 ≤ R) (hL : 0 ≤ L) :
    G * (2 * L) * R ≤ (1 + 2 * G * R / T) * (1 + T * L) := by
  have heq : (1 + 2 * G * R / T) * (1 + T * L) =
      G * (2 * L) * R + (1 + T * L + 2 * G * R / T) := by
    field_simp [hT.ne']
    ring
  rw [heq]
  exact le_add_of_nonneg_right (by positivity)

end
end ImbalancedChen.Part3.FreeEpsilonActualCountSourceOnly
