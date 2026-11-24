import ImbalancedChen.Part3E4PrimitiveMeanAssembly

/-!
# Signed two-long Brun comparison on the original carriers

The discrepancy of the positive comparison weight and its primitive mean
are both evaluated using the same original smooth majorants.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators SchwartzMap FourierTransform

/-- The modulus weight multiplies the actual joint error on the same carriers. -/
def twoLongJointSignedError (Q A S T : Finset ℕ) (a : ℕ) (ρ : ℕ → ℂ)
    (w : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ q ∈ Q, ρ q * twoLongJointError q a A S T w

/-- The positive profile used to bound the difference of the two projectors. -/
def twoLongBrunMajorant (P : Finset ℕ) (h : ℕ) (α : ℕ → ℂ) (F G : ℝ → ℂ)
    (U V : ℝ) (m n k : ℕ) : ℝ :=
  ‖α m‖ * (F ((n : ℝ) / U)).re * (G ((k : ℝ) / V)).re * twoLongBrunGap P h n k

/-- The signed rough-to-upper comparison, with the full primitive-mean
budget and the discrepancy of the literal nonnegative comparison weight. -/
theorem twoLongJointSignedError_rough_sub_upper_norm_le_of_gap
    (Q A S T P : Finset ℕ) (α ρ f g : ℕ → ℂ) (a R J z h : ℕ)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hR : 1 ≤ R) (hQ : Q ⊆ Ioc 0 R) (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ (q.divisors.card : ℝ) ^ J)
    (hz : 1 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) (hh : Even h)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    (hFmaj : ∀ n ∈ S, ‖f n‖ ≤ (F ((n : ℝ) / U)).re)
    (hGmaj : ∀ n ∈ T, ‖g n‖ ≤ (G ((n : ℝ) / V)).re)
    {C D E : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ D / (1 + |x|) ^ 2)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hE : (∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial ≤ E) :
    let y : ℝ := (z : ℝ) ^ (h + 1)
    ‖twoLongJointSignedError Q A S T a ρ (fun m n k => α m * f n * g k *
      ((brunRoughIndicator P n * brunRoughIndicator P k : ℤ) : ℂ)) -
      twoLongJointSignedError Q A S T a ρ (fun m n k => α m * f n * g k *
        ((brunProjector P h n * brunProjector P h k : ℤ) : ℂ))‖ ≤
      (∑ q ∈ Q, ‖ρ q‖ * ‖twoLongJointError q a A S T
        (fun m n k => ((twoLongBrunMajorant P h α F G U V m n k) : ℂ))‖) +
      2 * ((∑ m ∈ A, ‖α m‖) * C * D * (4 * U * V * E + 6 * (U + V) * y + 8 * y ^ 2) *
        (1 + Real.log (R : ℝ)) ^ (2 * 2 ^ (J + 2))) := by
  let W := twoLongBrunMajorant P h α F G U V
  have hmean := sum_twoLongJointMean_brunGap_smooth_le Q A S T P α ρ R J z h F G
    hU hV hR hQ hρ hz hP hh hFneg hGneg hS hT
    (fun n hn => (norm_nonneg _).trans (hFmaj n hn))
    (fun n hn => (norm_nonneg _).trans (hGmaj n hn)) hC hD hF hG hE0 hE1 hE
  dsimp only at hmean ⊢
  change _ ≤ (∑ q ∈ Q, ‖ρ q‖ * ‖twoLongJointError q a A S T
    (fun m n k => (W m n k : ℂ))‖) + _
  calc
    _ ≤ ∑ q ∈ Q, ‖ρ q‖ * (‖twoLongJointError q a A S T (fun m n k => (W m n k : ℂ))‖ +
        2 * twoLongJointMean q A S T W) := by
      unfold twoLongJointSignedError
      rw [← sum_sub_distrib]
      refine (norm_sum_le _ _).trans (sum_le_sum fun q _ => ?_)
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (twoLongJointError_sub_norm_le_brun q a A S T P h α f g
          (fun n => (F ((n : ℝ) / U)).re) (fun n => (G ((n : ℝ) / V)).re)
          (fun p hp => (hP p hp).1) hh hFmaj hGmaj) (norm_nonneg _)
    _ = (∑ q ∈ Q, ‖ρ q‖ * ‖twoLongJointError q a A S T (fun m n k => (W m n k : ℂ))‖) +
          2 * ∑ q ∈ Q, ‖ρ q‖ * twoLongJointMean q A S T W := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hmean (by norm_num))

private theorem productError_add (q a m : ℕ) (S T : Finset ℕ) (f g : ℕ → ℕ → ℂ) :
    twoLongProductError q a m S T (fun n k => f n k + g n k) =
      twoLongProductError q a m S T f + twoLongProductError q a m S T g := by
  have hite (p : Prop) [Decidable p] (r s : ℂ) : (if p then r + s else 0) =
      (if p then r else 0) + (if p then s else 0) := by split_ifs <;> simp
  simp only [twoLongProductError, hite, sum_add_distrib, add_div]
  ring

/-- Both contributions to the comparison gap expand over the same
physical carriers and retain the exact primitive mean. -/
theorem twoLongProductError_brunGap_smooth_norm_le
    (q a m : ℕ) [NeZero q] (S T P : Finset ℕ) (z h : ℕ) (F G : 𝓢(ℝ, ℂ))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (ha : a.Coprime q)
    (hz : 1 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) (hh : Even h)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ D / (1 + |x|) ^ 2) :
    ‖twoLongProductError q a m S T (fun n k => F ((n : ℝ) / U) * G ((k : ℝ) / V) *
      (twoLongBrunGap P h n k : ℂ))‖ ≤
      8 * C * D * ((z : ℝ) ^ (h + 1)) ^ 2 * (q.divisors.card : ℝ) ^ 2 *
        (Real.sqrt q + 1 / q.totient) := by
  let Ds := brunDivisors P h
  let Es := brunGapDivisors P h
  let c (d : ℕ) := (-1 : ℂ) ^ d.primeFactors.card
  let b (_ : ℕ) := (1 : ℂ)
  let Y := z ^ (h + 1)
  have hPprime (p : ℕ) (hp : p ∈ P) := (hP p hp).1
  have hDs : Ds ⊆ Icc 1 Y := (brunDivisors_subset_Icc P z h hz hP).trans
    (Icc_subset_Icc_right (pow_le_pow_right₀ hz (Nat.le_succ h)))
  have hEs : Es ⊆ Icc 1 Y := brunGapDivisors_subset_Icc P z h hz hP
  have hDpos (d : ℕ) (hd : d ∈ Ds) : 0 < d := (mem_Icc.mp (hDs hd)).1
  have hEpos (d : ℕ) (hd : d ∈ Es) : 0 < d := (mem_Icc.mp (hEs hd)).1
  have hY : (Y : ℝ) = (z : ℝ) ^ (h + 1) := by simp only [Y, Nat.cast_pow]
  have hDcard : (∑ d ∈ Ds, ‖c d‖) ≤ (Y : ℝ) := by
    have hcard : Ds.card ≤ Y := (card_le_card hDs).trans_eq (by simp)
    simpa [c] using (Nat.cast_le.mpr hcard : (Ds.card : ℝ) ≤ Y)
  have hEcard : (∑ d ∈ Es, ‖b d‖) ≤ (Y : ℝ) := by
    have hcard : Es.card ≤ Y := (card_le_card hEs).trans_eq (by simp)
    simpa [b] using (Nat.cast_le.mpr hcard : (Es.card : ℝ) ≤ Y)
  have hupper (n : ℕ) : (brunProjector P h n : ℂ) = part3DivisorExpansion Ds c n := by
    simp only [brunProjector_eq_divisor_sum P h n hPprime, Ds, c, part3DivisorExpansion,
      Int.cast_sum, apply_ite ((↑) : ℤ → ℂ), Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_zero]
  have hgap (n : ℕ) : ((brunProjector P h n - brunProjector P (h + 1) n : ℤ) : ℂ) =
      part3DivisorExpansion Es b n := by
    simp only [brunProjector_gap_eq_divisor_sum P h n hPprime hh, Es, b, part3DivisorExpansion,
      Int.cast_sum, apply_ite ((↑) : ℤ → ℂ), Int.cast_one, Int.cast_zero]
  have hgapProd (n k : ℕ) : (twoLongBrunGap P h n k : ℂ) =
      part3DivisorExpansion Es b n * part3DivisorExpansion Ds c k +
      part3DivisorExpansion Ds c n * part3DivisorExpansion Es b k := by
    simp only [twoLongBrunGap, Int.cast_add, Int.cast_mul, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_intCast, hupper, hgap]
  let f (n k : ℕ) := F ((n : ℝ) / U) * G ((k : ℝ) / V) *
    part3DivisorExpansion Es b n * part3DivisorExpansion Ds c k
  let g (n k : ℕ) := F ((n : ℝ) / U) * G ((k : ℝ) / V) *
    part3DivisorExpansion Ds c n * part3DivisorExpansion Es b k
  have heq : (fun n k : ℕ => F ((n : ℝ) / U) * G ((k : ℝ) / V) *
      (twoLongBrunGap P h n k : ℂ)) = fun n k => f n k + g n k := by
    funext n k
    rw [hgapProd]
    dsimp [f, g]
    ring
  let B : ℝ := 4 * C * D * (q.divisors.card : ℝ) ^ 2 * (Real.sqrt q + 1 / q.totient)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hf : ‖twoLongProductError q a m S T f‖ ≤ (Y : ℝ) * Y * B :=
    (twoLongProductError_smooth_divisorExpansion_norm_le q a m S T Es Ds F G b c hU hV ha
      hEpos hDpos hFneg hGneg hS hT hC hD hF hG).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hEcard hDcard (by positivity) (Nat.cast_nonneg Y)) hB)
  have hg : ‖twoLongProductError q a m S T g‖ ≤ (Y : ℝ) * Y * B :=
    (twoLongProductError_smooth_divisorExpansion_norm_le q a m S T Ds Es F G c b hU hV ha
      hDpos hEpos hFneg hGneg hS hT hC hD hF hG).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hDcard hEcard (by positivity) (Nat.cast_nonneg Y)) hB)
  rw [heq, productError_add]
  exact (norm_add_le _ _).trans ((add_le_add hf hg).trans_eq (by rw [hY]; dsimp [B]; ring))

/-- The whole modulus sum of the comparison discrepancies uses the fixed
smooth divisor bounds on both terms of the literal gap. -/
theorem sum_twoLongJointGapError_smooth_le
    (Q A S T P : Finset ℕ) (α ρ : ℕ → ℂ) (a R J z h : ℕ)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hR : 1 ≤ R) (hQ : Q ⊆ Ioc 0 R) (ha : ∀ q ∈ Q, a.Coprime q)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ (q.divisors.card : ℝ) ^ J)
    (hz : 1 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) (hh : Even h)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    (hFim : ∀ n ∈ S, (F ((n : ℝ) / U)).im = 0)
    (hGim : ∀ n ∈ T, (G ((n : ℝ) / V)).im = 0)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ D / (1 + |x|) ^ 2) :
    let y : ℝ := (z : ℝ) ^ (h + 1)
    (∑ q ∈ Q, ‖ρ q‖ * ‖twoLongJointError q a A S T
      (fun m n k => ((twoLongBrunMajorant P h α F G U V m n k) : ℂ))‖) ≤
      16 * C * D * (∑ m ∈ A, ‖α m‖) * y ^ 2 * ((R : ℝ) * Real.sqrt R) *
        (1 + Real.log R) ^ (2 ^ (J + 2) - 1) := by
  let y : ℝ := (z : ℝ) ^ (h + 1)
  let W := twoLongBrunMajorant P h α F G U V
  let M := ∑ m ∈ A, ‖α m‖
  let B (q : ℕ) := 8 * C * D * y ^ 2 * (q.divisors.card : ℝ) ^ 2 *
    (Real.sqrt q + 1 / q.totient)
  have hM : 0 ≤ M := sum_nonneg (fun _ _ => norm_nonneg _)
  have hFre (n : ℕ) : ((F ((n : ℝ) / U)).re : ℂ) = F ((n : ℝ) / U) := by
    by_cases hn : F ((n : ℝ) / U) = 0
    · simp [hn]
    · simpa [hFim n (hS n hn)] using Complex.re_add_im (F ((n : ℝ) / U))
  have hGre (n : ℕ) : ((G ((n : ℝ) / V)).re : ℂ) = G ((n : ℝ) / V) := by
    by_cases hn : G ((n : ℝ) / V) = 0
    · simp [hn]
    · simpa [hGim n (hT n hn)] using Complex.re_add_im (G ((n : ℝ) / V))
  let w (n k : ℕ) := F ((n : ℝ) / U) * G ((k : ℝ) / V) * (twoLongBrunGap P h n k : ℂ)
  have hJ (q : ℕ) (hq : q ∈ Q) :
      ‖twoLongJointError q a A S T (fun m n k => (W m n k : ℂ))‖ ≤ M * B q := by
    let _ : NeZero q := ⟨(mem_Ioc.mp (hQ hq)).1.ne'⟩
    have heq : (fun m n k : ℕ => (W m n k : ℂ)) = fun m n k => (‖α m‖ : ℂ) * w n k := by
      funext m n k
      simp only [W, twoLongBrunMajorant, Complex.ofReal_mul, hFre, hGre, w]
      ring
    rw [heq, twoLongJointError_factor_short]
    calc
      _ ≤ ∑ m ∈ A, ‖α m‖ * B q := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_left
          (twoLongProductError_brunGap_smooth_norm_le q a m S T P z h F G hU hV (ha q hq)
            hz hP hh hFneg hGneg hS hT hC hD hF hG) (norm_nonneg _)
      _ = _ := by rw [sum_mul]
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRroot : 1 ≤ Real.sqrt R := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hR'
  let K := 16 * C * D * M * y ^ 2 * Real.sqrt R
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint (q : ℕ) (hq : q ∈ Q) :
      ‖ρ q‖ * ‖twoLongJointError q a A S T (fun m n k => (W m n k : ℂ))‖ ≤
        K * (q.divisors.card : ℝ) ^ (J + 2) := by
    obtain ⟨hq0, hqR⟩ := mem_Ioc.mp (hQ hq)
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
    have hsqrt : Real.sqrt q + 1 / q.totient ≤ 2 * Real.sqrt R := by
      have hqroot := Real.sqrt_le_sqrt (Nat.cast_le.mpr hqR : (q : ℝ) ≤ R)
      have hφ' := div_le_self (show (0 : ℝ) ≤ 1 by norm_num) hφ
      linarith
    calc
      _ ≤ ‖ρ q‖ * (M * B q) := mul_le_mul_of_nonneg_left (hJ q hq) (norm_nonneg _)
      _ ≤ (q.divisors.card : ℝ) ^ J * (M * (8 * C * D * y ^ 2 * (q.divisors.card : ℝ) ^ 2 *
          (2 * Real.sqrt R))) := by
        exact mul_le_mul (hρ q hq)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hM)
          (by dsimp [B]; positivity) (by positivity)
      _ ≤ _ := le_of_eq (by dsimp only [K]; rw [pow_add]; ring)
  have hsum : (∑ q ∈ Q, (q.divisors.card : ℝ) ^ (J + 2)) ≤
      (R : ℝ) * (1 + Real.log R) ^ (2 ^ (J + 2) - 1) := by
    refine (sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)).trans ?_
    simpa only [Nat.floor_natCast, fouvryTau_two] using
      (sum_fouvryTau_pow_le_real (k := 2) (by norm_num) (J + 2) hR')
  dsimp only
  calc
    _ ≤ ∑ q ∈ Q, K * (q.divisors.card : ℝ) ^ (J + 2) := sum_le_sum hpoint
    _ = K * ∑ q ∈ Q, (q.divisors.card : ℝ) ^ (J + 2) := by rw [mul_sum]
    _ ≤ K * ((R : ℝ) * (1 + Real.log R) ^ (2 ^ (J + 2) - 1)) :=
      mul_le_mul_of_nonneg_left hsum hK
    _ ≤ _ := le_of_eq (by dsimp [K, M, y]; ring)

/-- The rough-to-upper replacement has the finite (E3)–(E4) bound summed
over the physical modulus support, with the two signed discrepancies left
on their original carriers. -/
theorem twoLongJointSignedError_rough_sub_upper_norm_le
    (Q A S T P : Finset ℕ) (α ρ f g : ℕ → ℂ) (a R J z h : ℕ)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hR : 1 ≤ R) (hQ : Q ⊆ Ioc 0 R) (ha : ∀ q ∈ Q, a.Coprime q)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ (q.divisors.card : ℝ) ^ J)
    (hz : 1 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) (hh : Even h)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    (hFim : ∀ n ∈ S, (F ((n : ℝ) / U)).im = 0)
    (hGim : ∀ n ∈ T, (G ((n : ℝ) / V)).im = 0)
    (hFmaj : ∀ n ∈ S, ‖f n‖ ≤ (F ((n : ℝ) / U)).re)
    (hGmaj : ∀ n ∈ T, ‖g n‖ ≤ (G ((n : ℝ) / V)).re)
    {C D E : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ D / (1 + |x|) ^ 2)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hE : (∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial ≤ E) :
    let y : ℝ := (z : ℝ) ^ (h + 1)
    ‖twoLongJointSignedError Q A S T a ρ (fun m n k => α m * f n * g k *
      ((brunRoughIndicator P n * brunRoughIndicator P k : ℤ) : ℂ)) -
      twoLongJointSignedError Q A S T a ρ (fun m n k => α m * f n * g k *
        ((brunProjector P h n * brunProjector P h k : ℤ) : ℂ))‖ ≤
      16 * C * D * (∑ m ∈ A, ‖α m‖) * y ^ 2 * ((R : ℝ) * Real.sqrt R) *
        (1 + Real.log R) ^ (2 ^ (J + 2) - 1) +
      2 * ((∑ m ∈ A, ‖α m‖) * C * D * (4 * U * V * E + 6 * (U + V) * y + 8 * y ^ 2) *
        (1 + Real.log R) ^ (2 * 2 ^ (J + 2))) := by
  have hbase := twoLongJointSignedError_rough_sub_upper_norm_le_of_gap Q A S T P α ρ f g a R J z h
    F G hU hV hR hQ hρ hz hP hh hFneg hGneg hS hT hFmaj hGmaj hC hD hF hG hE0 hE1 hE
  have hgap := sum_twoLongJointGapError_smooth_le Q A S T P α ρ a R J z h F G hU hV hR hQ ha hρ
    hz hP hh hFneg hGneg hS hT hFim hGim hC hD hF hG
  exact hbase.trans (add_le_add hgap le_rfl)

end

end ImbalancedChen.Part3
