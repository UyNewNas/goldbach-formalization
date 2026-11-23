import ImbalancedChen.Part3RoughAuxiliarySWPrimeFactor
import ImbalancedChen.Part3RoughAuxiliarySWWeighted
import ImbalancedChen.Part3RoughAuxiliarySWMellin

/-!
# Full auxiliary SW for chart-rough integer and Möbius slots

The prime estimate at the largest-prime quotient scale is summed before
partial summation. The final statement allows any complex profile with the
stated variation bound on the same interval and no dependence on `k`, `q`,
or the moving reduced residue.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Filter Finset
open scoped BigOperators

private theorem roughPrimeFactorSlot_norm_le (signed : Bool) (z n : ℕ) :
    ‖roughPrimeFactorSlot signed z n‖ ≤ 1 := by
  cases signed
  · simpa [roughPrimeFactorSlot] using roughOneSlot_norm_le (z : ℝ) n
  · simpa [roughPrimeFactorSlot] using roughMoebiusSlot_norm_le (z : ℝ) n

private theorem roughPrimeFactorSlot_support (signed : Bool) (z n : ℕ)
    (hn : roughPrimeFactorSlot signed z n ≠ 0) (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) :
    (z : ℝ) < p := by
  cases signed
  · exact roughOneSlot_support (z : ℝ) n (by simpa [roughPrimeFactorSlot] using hn) p hp hpn
  · exact roughMoebiusSlot_support (z : ℝ) n (by simpa [roughPrimeFactorSlot] using hn) p hp hpn

/-- Arbitrary logarithmic accuracy for the actual rough slots with a profile
of fixed logarithmic variation, uniformly over the interval and all moduli. -/
theorem exists_chart_rough_auxiliarySW_one_logAccuracy (A J : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x : ℝ, x0 ≤ x → ∀ z : ℝ, x ^ (1 / (Real.log (Real.log x)) ^ 3) ≤ z →
      ∀ signed : Bool, ∀ L H q b : ℕ, ∀ w : ℕ → ℂ,
        1 ≤ L → (H : ℝ) ≤ 2 * x → 0 < q → b.Coprime q →
        ‖w H‖ + (∑ n ∈ Ioc L (H - 1), ‖w (n + 1) - w n‖) ≤ Real.log x ^ J →
        ‖auxiliarySWError (Ioc L H)
          (fun n => w n * roughPrimeFactorSlot signed ⌊z⌋₊ n)
          1 q b‖ ≤ C * H / Real.log x ^ A := by
  let B : ℕ := ⌈A + J⌉₊
  obtain ⟨C, hC, hprime⟩ :=
    eventually_norm_auxiliarySWError_roughPrimeFactorSlot_le_sum (2 * (B + 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hprime
  have htail : ∀ᶠ x : ℝ in atTop, 1 < x ∧ 1 ≤ Real.log x ∧
      ((max N 2 : ℕ) : ℝ) ≤ x ^ (1 / (Real.log (Real.log x)) ^ 3) ∧
      ∀ z : ℝ, x ^ (1 / (Real.log (Real.log x)) ^ 3) ≤ z →
      ∀ H : ℕ, (H : ℝ) ≤ 2 * x →
        (∑ m ∈ Icc 1 (H / (⌊z⌋₊ + 1)),
          C * (H / m : ℕ) / Real.log (H / m : ℕ) ^ (2 * (B + 1))) ≤
          3 * C * H / Real.log x ^ B := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      Real.tendsto_log_atTop.eventually_ge_atTop ((max N 2 : ℕ) : ℝ),
      eventually_log_rpow_le_roughCutoff 1,
      eventually_roughPrimeFactor_sum_logAccuracy B C hC.le] with x hx hl hlarge hcut hsum
    exact ⟨hx, hl, hlarge.trans (by simpa only [Real.rpow_one] using hcut), hsum⟩
  obtain ⟨X, hX⟩ := eventually_atTop.mp htail
  refine ⟨3 * C, by positivity, max 2 X,
    (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _), ?_⟩
  intro x hx z hzcut signed L H q b w hL hH hq hb hvar
  obtain ⟨hx1, hlog, hcut, hsum⟩ := hX x ((le_max_right _ _).trans hx)
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hz0 : 0 ≤ z := (Real.rpow_nonneg hxpos.le _).trans hzcut
  have hz : max N 2 ≤ ⌊z⌋₊ := (Nat.le_floor_iff hz0).mpr (hcut.trans hzcut)
  have hprefix (T : ℕ) (hTH : T ≤ H) :
      ‖auxiliarySWError (Ioc L T) (roughPrimeFactorSlot signed ⌊z⌋₊) 1 q b‖ ≤
        3 * C * H / Real.log x ^ B := by
    have hT : (T : ℝ) ≤ 2 * x := (Nat.cast_le.mpr hTH).trans hH
    calc
      _ ≤ _ := hN N le_rfl signed ⌊z⌋₊ L T q b ((le_max_left _ _).trans hz)
        ((le_max_right _ _).trans hz) hL hq hb
      _ ≤ 3 * C * T / Real.log x ^ B := hsum z hzcut T hT
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hTH) (by positivity)) (by positivity)
  have hlogpos := zero_lt_one.trans_le hlog
  have hB : A + J ≤ (B : ℝ) := Nat.le_ceil _
  have hden : Real.log x ^ A * Real.log x ^ J ≤ Real.log x ^ B := by
    rw [← Real.rpow_add hlogpos, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlog hB
  calc
    _ ≤ (‖w H‖ + ∑ n ∈ Ioc L (H - 1), ‖w (n + 1) - w n‖) *
        (3 * C * H / Real.log x ^ B) :=
      auxiliarySWError_weighted_Ioc_norm_le L H 1 q b (roughPrimeFactorSlot signed ⌊z⌋₊) w _
        (by positivity) hprefix
    _ ≤ Real.log x ^ J * (3 * C * H / Real.log x ^ B) :=
      mul_le_mul_of_nonneg_right hvar (by positivity)
    _ = 3 * C * H * Real.log x ^ J / Real.log x ^ B := by ring
    _ ≤ 3 * C * H * Real.log x ^ J / (Real.log x ^ A * Real.log x ^ J) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      rw [mul_div_mul_right _ _ (Real.rpow_pos_of_pos hlogpos J).ne']

/-- The common interval and the one fixed rough profile furnish full
auxiliary SW with divisor order one, including moving `k`, `q` and `b`. -/
theorem uniformAuxiliarySW_of_chart_rough_slot {ι : Type*} (F : ι → MediumAtom)
    (L H : ι → ℕ) (Z : ι → ℝ) (signed : ι → Bool) (w : ι → ℕ → ℂ) (J Xvar : ℝ)
    (hU : ∀ i, 0 < (F i).U) (hV : ∀ i, 1 ≤ (F i).V) (hL : ∀ i, 1 ≤ L i)
    (hH : ∀ i, (H i : ℝ) ≤ 2 * (F i).U)
    (hZ : ∀ i, (F i).scale ^ (1 / (Real.log (Real.log (F i).scale)) ^ 3) ≤ Z i)
    (hcarrier : ∀ i, (F i).alphaCarrier = Ioc (L i) (H i))
    (hprofile : ∀ i n, n ∈ (F i).alphaCarrier → ‖w i n‖ ≤ 1)
    (hcoeff : ∀ i n, n ∈ (F i).alphaCarrier → (F i).alpha n =
      w i n * roughPrimeFactorSlot (signed i) ⌊Z i⌋₊ n)
    (hvar : ∀ i, Xvar ≤ (F i).scale → ‖w i (H i)‖ +
      (∑ n ∈ Ioc (L i) (H i - 1), ‖w i (n + 1) - w i n‖) ≤ Real.log (F i).scale ^ J) :
    UniformAuxiliarySW F 1 := by
  apply uniformAuxiliarySW_of_rough_one F hU
  · intro i n hn
    rw [hcoeff i n hn, norm_mul]
    exact (mul_le_mul (hprofile i n hn) (roughPrimeFactorSlot_norm_le _ _ _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · intro i n hn hne p hp hpn
    have hs : 0 < (F i).scale := mul_pos (hU i) (zero_lt_one.trans_le (hV i))
    have hz : 0 ≤ Z i := (Real.rpow_nonneg hs.le _).trans (hZ i)
    have hne' : roughPrimeFactorSlot (signed i) ⌊Z i⌋₊ n ≠ 0 := by
      intro hzero
      exact hne (by rw [hcoeff i n hn, hzero, mul_zero])
    exact (hZ i).trans_lt ((Nat.floor_lt hz).mp
      (Nat.cast_lt.mp (roughPrimeFactorSlot_support _ _ _ hne' p hp hpn)))
  · intro A _
    obtain ⟨C, hC, x0, hx0, hbound⟩ := exists_chart_rough_auxiliarySW_one_logAccuracy A J
    refine ⟨2 * C, by positivity, max x0 Xvar, hx0.trans_le (le_max_left _ _), ?_⟩
    intro i hi q b hq hb
    have hi0 := (le_max_left _ _).trans hi
    have hivar := (le_max_right _ _).trans hi
    have hUscale : (F i).U ≤ (F i).scale := le_mul_of_one_le_right (hU i).le (hV i)
    have hHscale : (H i : ℝ) ≤ 2 * (F i).scale := (hH i).trans
      (mul_le_mul_of_nonneg_left hUscale (by norm_num))
    let α (n : ℕ) := w i n * roughPrimeFactorSlot (signed i) ⌊Z i⌋₊ n
    have heq : (F i).auxSWError 1 q b = auxiliarySWError (Ioc (L i) (H i)) α 1 q b := by
      rw [MediumAtom.auxSWError_eq_auxiliarySWError]
      unfold auxiliarySWError
      have hcongr (P : ℕ → Prop) [DecidablePred P] :
          (∑ n ∈ (F i).alphaCarrier, if P n then (F i).alpha n else 0) =
            ∑ n ∈ Ioc (L i) (H i), if P n then α n else 0 := by
        rw [← hcarrier i]
        exact sum_congr rfl fun n hn => by simp only [hcoeff i n hn, α]
      rw [hcongr, hcongr]
    rw [heq]
    calc
      _ ≤ C * H i / Real.log (F i).scale ^ A :=
        hbound (F i).scale hi0 (Z i) (hZ i) (signed i) (L i) (H i) q b (w i)
          (hL i) hHscale hq hb (hvar i hivar)
      _ ≤ C * (2 * (F i).U) / Real.log (F i).scale ^ A :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hH i) hC.le)
          (Real.rpow_nonneg (Real.log_nonneg (hx0.le.trans hi0)) A)
      _ = _ := by ring

/-- The literal dyadic carrier and real open-closed interval have one pair
of natural endpoints. In particular the closed left dyadic boundary is
included even when `U` is an integer. -/
theorem MediumAtom.alphaCarrier_eq_Ioc (d : MediumAtom) (hU : 1 < d.U) :
    d.alphaCarrier = Ioc (max (⌈d.U⌉₊ - 1) ⌊d.intervalLo⌋₊)
      (min ⌊2 * d.U⌋₊ ⌊d.intervalHi⌋₊) := by
  have hceil : 1 < ⌈d.U⌉₊ := Nat.lt_ceil.mpr (by simpa using hU)
  ext n
  simp only [MediumAtom.alphaCarrier, mem_filter, mem_Icc, mem_Ioc, max_lt_iff, le_min_iff]
  by_cases hn : n = 0
  · simp only [hn, Nat.not_lt_zero, false_and]
    have hceil0 : ¬⌈d.U⌉₊ ≤ 0 := by omega
    simp [hceil0]
  · simp only [Nat.floor_lt' hn, Nat.le_floor_iff' hn]
    constructor
    · rintro ⟨⟨hleft, hright⟩, hlo, hhi⟩
      exact ⟨⟨by omega, hlo⟩, hright, hhi⟩
    · rintro ⟨⟨hleft, hlo⟩, hright, hhi⟩
      exact ⟨⟨by omega, hright⟩, hlo, hhi⟩

/-- The actual real-cutoff rough coefficient with a normalized profile and
Mellin twist. A fixed variation budget covers the profile and frequency.
The natural endpoints are read from the medium atom's original interval. -/
theorem uniformAuxiliarySW_of_chart_mellin_slot {ι : Type*} (F : ι → MediumAtom)
    (Z t : ι → ℝ) (signed : ι → Bool) (f : ι → ℕ → ℂ) (J Xvar : ℝ)
    (hU : ∀ i, 1 < (F i).U) (hV : ∀ i, 1 ≤ (F i).V)
    (hZ : ∀ i, (F i).scale ^ (1 / (Real.log (Real.log (F i).scale)) ^ 3) ≤ Z i)
    (hprofile : ∀ i n, n ∈ (F i).alphaCarrier → ‖f i n‖ ≤ 1)
    (hcoeff : ∀ i n, n ∈ (F i).alphaCarrier → (F i).alpha n =
      (f i n * (n : ℂ) ^ (Complex.I * (t i : ℂ))) *
        (if signed i then roughMoebiusSlot (Z i) n else roughOneSlot (Z i) n))
    (hvar : ∀ i, Xvar ≤ (F i).scale →
      1 + (∑ n ∈ Ioc (max (⌈(F i).U⌉₊ - 1) ⌊(F i).intervalLo⌋₊)
        (min ⌊2 * (F i).U⌋₊ ⌊(F i).intervalHi⌋₊ - 1), ‖f i (n + 1) - f i n‖) +
          |t i| ≤ Real.log (F i).scale ^ J) :
    UniformAuxiliarySW F 1 := by
  let L (i : ι) := max (⌈(F i).U⌉₊ - 1) ⌊(F i).intervalLo⌋₊
  let H (i : ι) := min ⌊2 * (F i).U⌋₊ ⌊(F i).intervalHi⌋₊
  let w (i : ι) (n : ℕ) :=
    if L i < H i then f i n * (n : ℂ) ^ (Complex.I * (t i : ℂ)) else 0
  have hL (i : ι) : 1 ≤ L i := by
    have hc : 1 < ⌈(F i).U⌉₊ := Nat.lt_ceil.mpr (by simpa using hU i)
    exact (show 1 ≤ ⌈(F i).U⌉₊ - 1 by omega).trans (le_max_left _ _)
  have hUpos (i : ι) : 0 < (F i).U := zero_lt_one.trans (hU i)
  have hH (i : ι) : (H i : ℝ) ≤ 2 * (F i).U :=
    (Nat.cast_le.mpr (min_le_left _ _)).trans
      (Nat.floor_le (mul_nonneg (by norm_num) (hUpos i).le))
  have hcarrier (i : ι) : (F i).alphaCarrier = Ioc (L i) (H i) :=
    (F i).alphaCarrier_eq_Ioc (hU i)
  apply uniformAuxiliarySW_of_chart_rough_slot F L H Z signed w J Xvar
    hUpos hV hL hH hZ hcarrier
  · intro i n hn
    have hmem := mem_Ioc.mp (hcarrier i ▸ hn)
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr ((Nat.zero_le (L i)).trans_lt hmem.1)
    have htwist : ‖(n : ℂ) ^ (Complex.I * (t i : ℂ))‖ = 1 := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos hnpos (Complex.I * (t i : ℂ))
    simpa only [w, if_pos (hmem.1.trans_le hmem.2), norm_mul, htwist, mul_one] using hprofile i n hn
  · intro i n hn
    have hmem := mem_Ioc.mp (hcarrier i ▸ hn)
    have hscale : 0 < (F i).scale := mul_pos (hUpos i) (zero_lt_one.trans_le (hV i))
    have hZ0 : 0 ≤ Z i := (Real.rpow_nonneg hscale.le _).trans (hZ i)
    rw [hcoeff i n hn, roughPrimeFactorSlot_floor_eq (signed i) (Z i) n hZ0,
      show w i n = _ from if_pos (hmem.1.trans_le hmem.2)]
  · intro i hi
    by_cases hLH : L i < H i
    · have hc : ⌈(F i).U⌉₊ ≤ L i + 1 := by
        have hl : ⌈(F i).U⌉₊ - 1 ≤ L i := le_max_left _ _
        omega
      have hUL : (F i).U ≤ ((L i + 1 : ℕ) : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hc)
      have hH2 : H i ≤ 2 * (L i + 1) := by
        exact_mod_cast (hH i).trans (mul_le_mul_of_nonneg_left hUL (by norm_num : 0 ≤ (2 : ℝ)))
      have hprof (n : ℕ) (hn : n ∈ Ioc (L i) (H i)) : ‖f i n‖ ≤ 1 :=
        hprofile i n ((hcarrier i).symm ▸ hn)
      calc
        _ ≤ 1 + (∑ n ∈ Ioc (L i) (H i - 1), ‖f i (n + 1) - f i n‖) + |t i| := by
          simpa only [w, if_pos hLH] using
            roughMellin_profile_variation_le (f i) (t i) (hL i) hLH hH2 hprof
        _ ≤ _ := hvar i hi
    · simp only [w, if_neg hLH, sub_self, norm_zero, sum_const_zero, add_zero]
      have hscale : 1 ≤ (F i).scale := (hU i).le.trans (le_mul_of_one_le_right (hUpos i).le (hV i))
      exact Real.rpow_nonneg (Real.log_nonneg hscale) _

end

end ImbalancedChen.Part3
