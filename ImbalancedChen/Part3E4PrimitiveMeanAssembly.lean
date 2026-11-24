import ImbalancedChen.Part3E4PrimitiveMean

namespace ImbalancedChen.Part3

noncomputable section

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators SchwartzMap FourierTransform

private def primitiveRealMass (q : ℕ) (S : Finset ℕ) (F : ℝ → ℂ) (U : ℝ) (c : ℕ → ℤ) : ℝ :=
  ∑ n ∈ S, if n.Coprime q then (F ((n : ℝ) / U)).re * (c n : ℝ) else 0

private theorem primitiveRealMass_eq_re (q : ℕ) (S : Finset ℕ) (F : ℝ → ℂ) (U : ℝ) (c : ℕ → ℤ) :
    primitiveRealMass q S F U c =
      (∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) * (c n : ℂ) else 0).re := by
  rw [primitiveRealMass, Complex.re_sum]
  apply sum_congr rfl
  intro n _
  by_cases hn : n.Coprime q
  · simp only [if_pos hn, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero]
  · simp only [if_neg hn, Complex.zero_re]

private theorem jointMean_add (q : ℕ) (A S T : Finset ℕ) (f g : ℕ → ℕ → ℕ → ℝ) :
    twoLongJointMean q A S T (fun m n k => f m n k + g m n k) =
      twoLongJointMean q A S T f + twoLongJointMean q A S T g := by
  change (∑ m ∈ A, ∑ n ∈ S, ∑ k ∈ T,
    if (m * n * k).Coprime q then f m n k + g m n k else 0) / (q.totient : ℝ) =
    (∑ m ∈ A, ∑ n ∈ S, ∑ k ∈ T, if (m * n * k).Coprime q then f m n k else 0) / (q.totient : ℝ) +
    (∑ m ∈ A, ∑ n ∈ S, ∑ k ∈ T, if (m * n * k).Coprime q then g m n k else 0) / (q.totient : ℝ)
  simp only [← add_div, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

private theorem primitiveBrunMass_scalarBounds
    (q : ℕ) [NeZero q] (S P : Finset ℕ) (z h : ℕ) (F : 𝓢(ℝ, ℂ))
    {U : ℝ} (hU : 0 < U) (hz : 1 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) (hh : Even h)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hFpos : ∀ n ∈ S, 0 ≤ (F ((n : ℝ) / U)).re)
    {C E : ℝ} (hC : 0 ≤ C) (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hE : (∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial ≤ E) :
    let τ : ℝ := q.divisors.card
    let y : ℝ := (z : ℝ) ^ (h + 1)
    let A := primitiveRealMass q S F U (brunProjector P h)
    let G := primitiveRealMass q S F U (fun n => brunProjector P h n - brunProjector P (h + 1) n)
    0 ≤ A ∧ A ≤ C * (2 * U + 2 * y) * τ ∧
    0 ≤ G ∧ G ≤ C * (U * E + 2 * y) * τ := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hφ : (q.totient : ℝ) / q ≤ 1 := (div_le_one₀ hqpos).mpr (Nat.cast_le.mpr (Nat.totient_le q))
  have hτ : (1 : ℝ) ≤ q.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr
      (show q.divisors.Nonempty from ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne q)⟩)
  have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hPow : (z : ℝ) ^ h ≤ (z : ℝ) ^ (h + 1) := pow_le_pow_right₀ hz' (Nat.le_succ h)
  have hZ : ‖(𝓕 F) 0‖ ≤ C := by simpa using hF 0
  have hM : (q.totient : ℝ) * (U / (q : ℝ)) * ‖(𝓕 F) 0‖ ≤ U * C := by
    calc
      _ = (((q.totient : ℝ) / q) * U) * ‖(𝓕 F) 0‖ := by ring
      _ ≤ (1 * U) * C := mul_le_mul (mul_le_mul_of_nonneg_right hφ hU.le) hZ (norm_nonneg _) (by positivity)
      _ = _ := by rw [one_mul]
  let Eq := (∑ p ∈ P with p.Coprime q, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial
  have hEsub : Eq ≤ E := by
    have hs : (∑ p ∈ P with p.Coprime q, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
    exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) hs _)
      (by positivity)).trans hE
  have hEq0 : 0 ≤ Eq := by dsimp [Eq]; positivity
  obtain ⟨hA, hG⟩ := smoothProfile_primitiveBrunFactors_norm_le q S P z h F hU hz hP hh
    hFneg hS hC hF
  obtain ⟨hA0, hG0⟩ := smoothProfile_primitiveBrunFactors_re_nonneg q S P h F U
    (fun p hp => (hP p hp).1) hh hFpos
  dsimp only
  rw [primitiveRealMass_eq_re, primitiveRealMass_eq_re]
  refine ⟨hA0, (Complex.re_le_norm _).trans (hA.trans ?_), hG0,
    (Complex.re_le_norm _).trans (hG.trans ?_)⟩
  · calc
      _ ≤ U * C * 2 + (z : ℝ) ^ (h + 1) * (2 * C * (q.divisors.card : ℝ)) :=
        add_le_add (mul_le_mul hM (by linarith [hEsub.trans hE1] : 1 + Eq ≤ 2)
          (by positivity) (by positivity)) (mul_le_mul_of_nonneg_right hPow (by positivity))
      _ ≤ (U * C * 2) * (q.divisors.card : ℝ) +
          (z : ℝ) ^ (h + 1) * (2 * C * (q.divisors.card : ℝ)) :=
        add_le_add (le_mul_of_one_le_right (by positivity) hτ) le_rfl
      _ ≤ _ := le_of_eq (by ring)
  · calc
      _ ≤ U * C * E + (z : ℝ) ^ (h + 1) * (2 * C * (q.divisors.card : ℝ)) :=
        add_le_add (mul_le_mul hM hEsub hEq0 (by positivity)) le_rfl
      _ ≤ (U * C * E) * (q.divisors.card : ℝ) +
          (z : ℝ) ^ (h + 1) * (2 * C * (q.divisors.card : ℝ)) :=
        add_le_add (le_mul_of_one_le_right (by positivity) hτ) le_rfl
      _ ≤ _ := le_of_eq (by ring)

/-- The primitive mean of the positive two-factor Brun comparison weight,
with the original coprimality gate and a single physical totient. -/
theorem twoLongJointMean_brunGap_smooth_le
    (q : ℕ) [NeZero q] (A S T P : Finset ℕ) (α : ℕ → ℂ) (z h : ℕ)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hz : 1 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) (hh : Even h)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    (hFpos : ∀ n ∈ S, 0 ≤ (F ((n : ℝ) / U)).re)
    (hGpos : ∀ n ∈ T, 0 ≤ (G ((n : ℝ) / V)).re)
    {C D E : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ D / (1 + |x|) ^ 2)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hE : (∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial ≤ E) :
    let y : ℝ := (z : ℝ) ^ (h + 1)
    twoLongJointMean q A S T (fun m n k => ‖α m‖ * (F ((n : ℝ) / U)).re *
      (G ((k : ℝ) / V)).re * twoLongBrunGap P h n k) ≤
      (∑ m ∈ A, ‖α m‖) * C * D * (4 * U * V * E + 6 * (U + V) * y + 8 * y ^ 2) *
        (q.divisors.card : ℝ) ^ 2 / (q.totient : ℝ) := by
  let y : ℝ := (z : ℝ) ^ (h + 1)
  let τ : ℝ := q.divisors.card
  let Fup := primitiveRealMass q S F U (brunProjector P h)
  let Gup := primitiveRealMass q T G V (brunProjector P h)
  let Fgap := primitiveRealMass q S F U (fun n => brunProjector P h n - brunProjector P (h + 1) n)
  let Ggap := primitiveRealMass q T G V (fun n => brunProjector P h n - brunProjector P (h + 1) n)
  let short := ∑ m ∈ A, if m.Coprime q then ‖α m‖ else 0
  let total := ∑ m ∈ A, ‖α m‖
  have hshort : short ≤ total := by
    apply sum_le_sum
    intro m _
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have htotal : 0 ≤ total := sum_nonneg fun _ _ => norm_nonneg _
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hτ : 0 ≤ τ := Nat.cast_nonneg _
  obtain ⟨hFup0, hFup, hFgap0, hFgap⟩ := primitiveBrunMass_scalarBounds q S P z h F
    hU hz hP hh hFneg hS hFpos hC hF hE0 hE1 hE
  obtain ⟨hGup0, hGup, hGgap0, hGgap⟩ := primitiveBrunMass_scalarBounds q T P z h G
    hV hz hP hh hGneg hT hGpos hD hG hE0 hE1 hE
  have hterms : Fgap * Gup + Fup * Ggap ≤
      C * D * (4 * U * V * E + 6 * (U + V) * y + 8 * y ^ 2) * τ ^ 2 := by
    have hleft := mul_le_mul hFgap hGup hGup0 (show 0 ≤ C * (U * E + 2 * y) * τ by positivity)
    have hright := mul_le_mul hFup hGgap hGgap0 (show 0 ≤ C * (2 * U + 2 * y) * τ by positivity)
    have hp : (U * E + 2 * y) * (2 * V + 2 * y) + (2 * U + 2 * y) * (V * E + 2 * y) ≤
        4 * U * V * E + 6 * (U + V) * y + 8 * y ^ 2 := by
      nlinarith only [mul_nonneg (mul_nonneg (add_nonneg hU.le hV.le) hy) (sub_nonneg.mpr hE1)]
    calc
      _ ≤ _ := add_le_add hleft hright
      _ = (C * D * τ ^ 2) * ((U * E + 2 * y) * (2 * V + 2 * y) +
          (2 * U + 2 * y) * (V * E + 2 * y)) := by ring
      _ ≤ (C * D * τ ^ 2) * (4 * U * V * E + 6 * (U + V) * y + 8 * y ^ 2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ := le_of_eq (by ring)
  have hmean : twoLongJointMean q A S T (fun m n k => ‖α m‖ * (F ((n : ℝ) / U)).re *
      (G ((k : ℝ) / V)).re * twoLongBrunGap P h n k) =
      short * (Fgap * Gup + Fup * Ggap) / (q.totient : ℝ) := by
    let FupW (n : ℕ) := (F ((n : ℝ) / U)).re * (brunProjector P h n : ℝ)
    let GupW (n : ℕ) := (G ((n : ℝ) / V)).re * (brunProjector P h n : ℝ)
    let FgapW (n : ℕ) := (F ((n : ℝ) / U)).re *
      ((brunProjector P h n - brunProjector P (h + 1) n : ℤ) : ℝ)
    let GgapW (n : ℕ) := (G ((n : ℝ) / V)).re *
      ((brunProjector P h n - brunProjector P (h + 1) n : ℤ) : ℝ)
    have heq : (fun m n k : ℕ => ‖α m‖ * (F ((n : ℝ) / U)).re * (G ((k : ℝ) / V)).re *
        twoLongBrunGap P h n k) =
        (fun m n k => (‖α m‖ * FgapW n * GupW k) + (‖α m‖ * FupW n * GgapW k)) := by
      funext m n k
      simp only [twoLongBrunGap, Int.cast_add, Int.cast_mul, FupW, GupW, FgapW, GgapW]
      ring
    rw [heq, jointMean_add, twoLongJointMean_mul_profile, twoLongJointMean_mul_profile]
    change short * Fgap * Gup / (q.totient : ℝ) + short * Fup * Ggap / (q.totient : ℝ) = _
    ring
  dsimp only
  rw [hmean]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ total * (C * D * (4 * U * V * E + 6 * (U + V) * y + 8 * y ^ 2) * τ ^ 2) :=
      mul_le_mul hshort hterms (add_nonneg (mul_nonneg hFgap0 hGup0) (mul_nonneg hFup0 hGgap0)) htotal
    _ ≤ _ := le_of_eq (by ring)

/-- The primitive mean part of (E4) under the fixed divisor order of the
actual modulus coefficients. The full support cap remains on the product. -/
theorem sum_twoLongJointMean_brunGap_smooth_le
    (Q A S T P : Finset ℕ) (α ρ : ℕ → ℂ) (R J z h : ℕ)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hR : 1 ≤ R) (hQ : Q ⊆ Ioc 0 R) (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ (q.divisors.card : ℝ) ^ J)
    (hz : 1 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) (hh : Even h)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    (hFpos : ∀ n ∈ S, 0 ≤ (F ((n : ℝ) / U)).re)
    (hGpos : ∀ n ∈ T, 0 ≤ (G ((n : ℝ) / V)).re)
    {C D E : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ D / (1 + |x|) ^ 2)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hE : (∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial ≤ E) :
    let y : ℝ := (z : ℝ) ^ (h + 1)
    (∑ q ∈ Q, ‖ρ q‖ * twoLongJointMean q A S T (fun m n k => ‖α m‖ *
      (F ((n : ℝ) / U)).re * (G ((k : ℝ) / V)).re * twoLongBrunGap P h n k)) ≤
        (∑ m ∈ A, ‖α m‖) * C * D * (4 * U * V * E + 6 * (U + V) * y + 8 * y ^ 2) *
          (1 + Real.log (R : ℝ)) ^ (2 * 2 ^ (J + 2)) := by
  let y : ℝ := (z : ℝ) ^ (h + 1)
  let K : ℝ := (∑ m ∈ A, ‖α m‖) * C * D * (4 * U * V * E + 6 * (U + V) * y + 8 * y ^ 2)
  have hK : 0 ≤ K := by dsimp [K, y]; positivity
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hpoint (q : ℕ) (hq : q ∈ Q) :
      ‖ρ q‖ * twoLongJointMean q A S T (fun m n k => ‖α m‖ * (F ((n : ℝ) / U)).re *
        (G ((k : ℝ) / V)).re * twoLongBrunGap P h n k) ≤
          K * ((fouvryTau (2 ^ (J + 2)) q : ℝ) / q.totient) := by
    let _ : NeZero q := ⟨(mem_Ioc.mp (hQ hq)).1.ne'⟩
    have hτ : (q.divisors.card : ℝ) ^ (J + 2) ≤ (fouvryTau (2 ^ (J + 2)) q : ℝ) := by
      have hn := fouvryTau_pow_le 2 (J + 2) (NeZero.ne q)
      rw [fouvryTau_two] at hn
      exact_mod_cast hn
    calc
      _ ≤ ‖ρ q‖ * (K * (q.divisors.card : ℝ) ^ 2 / q.totient) :=
        mul_le_mul_of_nonneg_left (twoLongJointMean_brunGap_smooth_le q A S T P α z h F G
          hU hV hz hP hh hFneg hGneg hS hT hFpos hGpos hC hD hF hG hE0 hE1 hE) (norm_nonneg _)
      _ ≤ (q.divisors.card : ℝ) ^ J * (K * (q.divisors.card : ℝ) ^ 2 / q.totient) :=
        mul_le_mul_of_nonneg_right (hρ q hq) (by positivity)
      _ = K * ((q.divisors.card : ℝ) ^ (J + 2) / q.totient) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hτ (Nat.cast_nonneg _)) hK
  have hsum : (∑ q ∈ Q, (fouvryTau (2 ^ (J + 2)) q : ℝ) / q.totient) ≤
      (1 + Real.log (R : ℝ)) ^ (2 * 2 ^ (J + 2)) := by
    refine (sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)).trans ?_
    simpa only [Nat.floor_natCast] using sum_fouvryTau_div_totient_le_real (2 ^ (J + 2)) hR'
  change _ ≤ K * _
  exact (sum_le_sum hpoint).trans (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hsum hK)

end

end ImbalancedChen.Part3
