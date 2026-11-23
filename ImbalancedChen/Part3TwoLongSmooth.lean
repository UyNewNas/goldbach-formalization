import ImbalancedChen.Part3TwoLongCompletion
import ImbalancedChen.Part3SmoothReciprocalWeil
import ImbalancedChen.Part3TwoLongBrunComparison
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean

/-!
# Smooth two-long products with the exact primitive main term

The finite sum is grouped by the actual pair of natural residues. When
the short multiplier is a unit, the resulting completed graph is the
unit inverse graph. A nonunit short multiplier contributes zero.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators SchwartzMap FourierTransform

private def longResidueMass (q : ℕ) (S : Finset ℕ) (w : ℕ → ℂ) (u : ZMod q) : ℂ :=
  ∑ n ∈ S, if (n : ZMod q) = u then w n else 0

private theorem indicator_sum_units (q : ℕ) [NeZero q] (n : ℕ) (z : ℂ) :
    (∑ u : (ZMod q)ˣ, if (n : ZMod q) = u then z else 0) =
      if n.Coprime q then z else 0 := by
  classical
  by_cases hn : n.Coprime q
  · let u := ZMod.unitOfCoprime n hn
    have hu : (u : ZMod q) = n := rfl
    rw [if_pos hn, sum_eq_single u]
    · simp [hu]
    · intro v _ hv
      exact if_neg (fun he => hv (Units.ext (he.symm.trans hu.symm)))
    · simp
  · rw [if_neg hn]
    have hnone (u : (ZMod q)ˣ) : (n : ZMod q) ≠ u := by
      intro hu
      exact hn ((ZMod.isUnit_iff_coprime n q).mp ⟨u, hu.symm⟩)
    simp only [hnone, if_false, sum_const_zero]

private theorem longResidueMass_sum_units (q : ℕ) [NeZero q] (S : Finset ℕ) (w : ℕ → ℂ) :
    (∑ u : (ZMod q)ˣ, longResidueMass q S w (u : ZMod q)) =
      ∑ n ∈ S, if n.Coprime q then w n else 0 := by
  unfold longResidueMass
  rw [sum_comm]
  exact sum_congr rfl (fun n _ => indicator_sum_units q n (w n))

private theorem product_indicator_sum_units (q : ℕ) [NeZero q] (b : (ZMod q)ˣ)
    (x y : ℕ) (v w : ℂ) :
    (∑ u : (ZMod q)ˣ, (if (x : ZMod q) = u then v else 0) *
      (if (y : ZMod q) = (↑(b * u⁻¹) : ZMod q) then w else 0)) =
      if (x : ZMod q) * (y : ZMod q) = (b : ZMod q) then v * w else 0 := by
  classical
  by_cases hx : IsUnit (x : ZMod q)
  · obtain ⟨u, hu⟩ := hx
    have he : (x : ZMod q) * (↑(b * u⁻¹) : ZMod q) = b := by
      rw [← hu]
      simpa only [Units.val_mul] using congrArg (fun u : (ZMod q)ˣ => (u : ZMod q))
        (show u * (b * u⁻¹) = b by rw [← mul_assoc, mul_comm u b, mul_assoc, mul_inv_cancel, mul_one])
    have hy : (y : ZMod q) = (↑(b * u⁻¹) : ZMod q) ↔ (x : ZMod q) * (y : ZMod q) = b := by
      rw [← he]
      exact (IsUnit.mul_right_inj (show IsUnit (x : ZMod q) from ⟨u, hu⟩)).symm
    rw [sum_eq_single u]
    · rw [hu, if_pos rfl]
      by_cases hp : (x : ZMod q) * (y : ZMod q) = (b : ZMod q)
      · rw [if_pos (hy.mpr hp), if_pos hp]
      · rw [if_neg (fun h => hp (hy.mp h)), if_neg hp, mul_zero]
    · intro u' _ hne
      have heq : (x : ZMod q) ≠ u' := fun h => hne (Units.ext (h.symm.trans hu.symm))
      simp only [heq, if_false, zero_mul]
    · simp
  · have hprod : (x : ZMod q) * (y : ZMod q) ≠ b := by
      intro he
      exact hx ((IsUnit.mul_iff).mp (he.symm ▸ b.isUnit)).1
    have hnone (u : (ZMod q)ˣ) : (x : ZMod q) ≠ u := fun h => hx ⟨u, h.symm⟩
    simp only [hnone, hprod, if_false, zero_mul, sum_const_zero]

private theorem product_weight_sum_eq_residues (q : ℕ) [NeZero q] (b : (ZMod q)ˣ)
    (S T : Finset ℕ) (f g : ℕ → ℂ) :
    (∑ u : (ZMod q)ˣ, longResidueMass q S f u * longResidueMass q T g (↑(b * u⁻¹) : ZMod q)) =
      ∑ x ∈ S, ∑ y ∈ T, if (x : ZMod q) * (y : ZMod q) = (b : ZMod q) then f x * g y else 0 := by
  have hexpand (u : (ZMod q)ˣ) : longResidueMass q S f u * longResidueMass q T g (↑(b * u⁻¹) : ZMod q) =
      ∑ x ∈ S, ∑ y ∈ T, (if (x : ZMod q) = u then f x else 0) *
        (if (y : ZMod q) = (↑(b * u⁻¹) : ZMod q) then g y else 0) := by
    unfold longResidueMass
    rw [sum_mul]
    exact sum_congr rfl fun _ _ => mul_sum ..
  simp_rw [hexpand]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  exact sum_congr rfl fun y _ => product_indicator_sum_units q b x y (f x) (g y)

/-- A short multiplier sharing a factor with the modulus contributes
zero to both the actual progression and the primitive mass. -/
theorem twoLongProductError_eq_zero_of_nonunit (q a m : ℕ) (S T : Finset ℕ) (w : ℕ → ℕ → ℂ)
    (ha : a.Coprime q) (hm : ¬m.Coprime q) : twoLongProductError q a m S T w = 0 := by
  have hc (x y : ℕ) : ¬(m * x * y).Coprime q := by
    intro h
    exact hm (Nat.coprime_mul_iff_left.mp (Nat.coprime_mul_iff_left.mp h).1).1
  have hAP (x y : ℕ) : ¬m * x * y ≡ a [MOD q] := by
    intro h
    apply hc x y
    change Nat.gcd (m * x * y) q = 1
    exact h.gcd_eq.trans ha.gcd_eq_one
  simp [twoLongProductError, hAP, hc]

/-- Exact residue-class grouping of the finite product error for the
actual multiplier and the original two separated weights. -/
private theorem twoLongProductError_eq_residueError (q a m : ℕ) [NeZero q] (S T : Finset ℕ)
    (f g : ℕ → ℂ) (ha : a.Coprime q) (hm : m.Coprime q) :
    twoLongProductError q a m S T (fun x y => f x * g y) =
      twoLongResidueError ((ZMod.unitOfCoprime m hm)⁻¹ * ZMod.unitOfCoprime a ha)
        (longResidueMass q S f) (longResidueMass q T g) := by
  let mu := ZMod.unitOfCoprime m hm
  let au := ZMod.unitOfCoprime a ha
  let b := mu⁻¹ * au
  have hmu : (mu : ZMod q) = m := rfl
  have hmul : (m : ZMod q) * (b : ZMod q) = a := by
    rw [← hmu, ← Units.val_mul]
    change (↑(mu * (mu⁻¹ * au)) : ZMod q) = a
    rw [← mul_assoc, mul_inv_cancel, one_mul]
    rfl
  have hgate (x y : ℕ) : m * x * y ≡ a [MOD q] ↔ (x : ZMod q) * (y : ZMod q) = (b : ZMod q) := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_mul, mul_assoc, ← hmul]
    exact (show IsUnit (m : ZMod q) from ⟨mu, hmu⟩).mul_right_inj
  have hc (x y : ℕ) : (m * x * y).Coprime q ↔ x.Coprime q ∧ y.Coprime q := by
    simp only [Nat.coprime_mul_iff_left]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hm, h.1⟩, h.2⟩⟩
  have hmean : (∑ x ∈ S, ∑ y ∈ T,
      if (m * x * y).Coprime q then f x * g y else 0) =
      (∑ x ∈ S, if x.Coprime q then f x else 0) * (∑ y ∈ T, if y.Coprime q then g y else 0) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro x _
    rw [mul_sum]
    apply sum_congr rfl
    intro y _
    simp only [hc]
    by_cases hx : x.Coprime q
    · by_cases hy : y.Coprime q
      · rw [if_pos ⟨hx, hy⟩, if_pos hx, if_pos hy]
      · rw [if_neg (fun h => hy h.2), if_neg hy, mul_zero]
    · rw [if_neg (fun h => hx h.1), if_neg hx, zero_mul]
  change _ = twoLongResidueError b _ _
  rw [twoLongProductError, twoLongResidueError, product_weight_sum_eq_residues,
    longResidueMass_sum_units, longResidueMass_sum_units, hmean]
  simp only [hgate]

/-- The exact finite coprime mass of a smooth slot differs from its zero
Fourier mode by the completed nonzero Ramanujan series. -/
theorem smoothProfile_primitiveMean_norm_le (q : ℕ) [NeZero q] (S : Finset ℕ)
    (F : 𝓢(ℝ, ℂ)) {U : ℝ} (hU : 0 < U)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2) :
    ‖(∑ n ∈ S, if n.Coprime q then F ((n : ℝ) / U) else 0) -
      (q.totient : ℂ) * ((U / (q : ℝ)) • (𝓕 F) 0)‖ ≤ 2 * C * (q.divisors.card : ℝ) := by
  let fhat : 𝓢(ℝ, ℂ) := 𝓕 F
  have hf : longResidueMass q S (fun n => F ((n : ℝ) / U)) =
      twoLongFourierProfile (U / (q : ℝ)) fhat := by
    funext u
    exact smoothProfile_progression_eq_tsum q u hU F S hFneg hS
  rw [← longResidueMass_sum_units, hf]
  exact twoLongFourierProfile_primitiveMean_norm_le
    (div_pos hU (Nat.cast_pos.mpr (NeZero.pos q))) fhat hC hF

/-- The smooth two-long error with the exact finite natural product and
primitive main term. The divisor-power factor is fixed before the scales. -/
theorem twoLongProductError_smooth_norm_le (q a m : ℕ) [NeZero q]
    (S T : Finset ℕ) (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (ha : a.Coprime q)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ D / (1 + |x|) ^ 2) :
    ‖twoLongProductError q a m S T (fun x y => F ((x : ℝ) / U) * G ((y : ℝ) / V))‖ ≤
      4 * C * D * (q.divisors.card : ℝ) ^ 2 * (Real.sqrt q + 1 / q.totient) := by
  by_cases hm : m.Coprime q
  · let fhat : 𝓢(ℝ, ℂ) := 𝓕 F
    let ghat : 𝓢(ℝ, ℂ) := 𝓕 G
    have hf : longResidueMass q S (fun n => F ((n : ℝ) / U)) =
        twoLongFourierProfile (U / (q : ℝ)) fhat := by
      funext u
      exact smoothProfile_progression_eq_tsum q u hU F S hFneg hS
    have hg : longResidueMass q T (fun n => G ((n : ℝ) / V)) =
        twoLongFourierProfile (V / (q : ℝ)) ghat := by
      funext u
      exact smoothProfile_progression_eq_tsum q u hV G T hGneg hT
    rw [twoLongProductError_eq_residueError q a m S T _ _ ha hm, hf, hg]
    have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
    exact twoLongResidueError_fourierProfiles_norm_le _ (div_pos hU hq) (div_pos hV hq)
      fhat ghat hC hD hF hG
  · rw [twoLongProductError_eq_zero_of_nonunit q a m S T _ ha hm, norm_zero]
    positivity

/-- The smooth estimate survives the exact two-slot divisor push-back.
The quotient profile is completed at its rescaled mesh for each pair of divisors. -/
theorem twoLongProductError_smooth_divisorExpansion_norm_le (q a m : ℕ) [NeZero q]
    (S T D E : Finset ℕ) (F G : 𝓢(ℝ, ℂ)) (c b : ℕ → ℂ)
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (ha : a.Coprime q)
    (hD : ∀ d ∈ D, 0 < d) (hE : ∀ e ∈ E, 0 < e)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ K / (1 + |x|) ^ 2) :
    ‖twoLongProductError q a m S T (fun x y =>
      F ((x : ℝ) / U) * G ((y : ℝ) / V) * part3DivisorExpansion D c x *
        part3DivisorExpansion E b y)‖ ≤
      ((∑ d ∈ D, ‖c d‖) * ∑ e ∈ E, ‖b e‖) *
        (4 * C * K * (q.divisors.card : ℝ) ^ 2 * (Real.sqrt q + 1 / q.totient)) := by
  let B := 4 * C * K * (q.divisors.card : ℝ) ^ 2 * (Real.sqrt q + 1 / q.totient)
  have hsupport (W : ℝ → ℂ) (Y : ℝ) (I : Finset ℕ)
      (hI : ∀ n : ℕ, W ((n : ℝ) / Y) ≠ 0 → n ∈ I) {d : ℕ} (hd : 0 < d) :
      ∀ n : ℕ, W ((n : ℝ) / (Y / (d : ℝ))) ≠ 0 → n ∈ twoLongQuotientCarrier I d := by
    intro n hn
    apply (mem_twoLongQuotientCarrier I hd).mpr
    apply hI
    rwa [Nat.cast_mul, mul_comm (d : ℝ), ← div_div_eq_mul_div]
  rw [twoLongProductError_divisorExpansion_scale_eq_sum q a m S T D E U V F G c b hD hE]
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ E, ‖c d‖ * ‖b e‖ * B := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun d hd => ?_)
      refine (norm_sum_le _ _).trans (sum_le_sum fun e he => ?_)
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (twoLongProductError_smooth_norm_le q a (m * d * e) _ _ F G
          (div_pos hU (Nat.cast_pos.mpr (hD d hd))) (div_pos hV (Nat.cast_pos.mpr (hE e he)))
          ha hFneg hGneg (hsupport F U S hS (hD d hd)) (hsupport G V T hT (hE e he))
          hC hK hF hG) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      change _ = ((∑ d ∈ D, ‖c d‖) * ∑ e ∈ E, ‖b e‖) * B
      rw [sum_mul D (fun d => ‖c d‖), sum_mul]
      apply sum_congr rfl
      intro d _
      rw [mul_sum, sum_mul]

/-- Signed modulus and short-factor weights on the shared exact carrier. -/
def twoLongProductSignedError (S T A Q : Finset ℕ) (a : ℕ)
    (α ρ : ℕ → ℂ) (w : ℕ → ℕ → ℂ) : ℂ :=
  ∑ q ∈ Q, ρ q * ∑ m ∈ A, α m * twoLongProductError q a m S T w

/-- A pointwise error bound for every short factor composes with the
literal complex short weights and physical modulus weights. -/
theorem twoLongProductSignedError_norm_le (S T A Q : Finset ℕ) (a : ℕ)
    (α ρ : ℕ → ℂ) (w : ℕ → ℕ → ℂ) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Q, ∀ m ∈ A, ‖twoLongProductError q a m S T w‖ ≤ B q) :
    ‖twoLongProductSignedError S T A Q a α ρ w‖ ≤
      (∑ m ∈ A, ‖α m‖) * ∑ q ∈ Q, ‖ρ q‖ * B q := by
  have hshort (q : ℕ) (hq : q ∈ Q) : ‖∑ m ∈ A, α m * twoLongProductError q a m S T w‖ ≤
      (∑ m ∈ A, ‖α m‖) * B q := by
    refine (norm_sum_le _ _).trans ?_
    rw [sum_mul]
    apply sum_le_sum
    intro m hm
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB q hq m hm) (norm_nonneg _)
  unfold twoLongProductSignedError
  refine (norm_sum_le _ _).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  rw [norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hshort q hq) (norm_nonneg _)

/-- The smooth two-long divisor-moment bound. All primitive moduli in
the physical range are covered with the fixed logarithmic exponent. -/
theorem twoLongProductSignedError_smooth_norm_le (S T A Q : Finset ℕ) (a R J : ℕ)
    (α ρ : ℕ → ℂ) (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hR : 1 ≤ R) (hQ : Q ⊆ Ioc 0 R) (ha : ∀ q ∈ Q, a.Coprime q)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ (q.divisors.card : ℝ) ^ J)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ D / (1 + |x|) ^ 2) :
    ‖twoLongProductSignedError S T A Q a α ρ (fun x y => F ((x : ℝ) / U) * G ((y : ℝ) / V))‖ ≤
      8 * C * D * (∑ m ∈ A, ‖α m‖) * ((R : ℝ) * Real.sqrt R) *
        (1 + Real.log R) ^ (2 ^ (J + 2) - 1) := by
  let B (q : ℕ) := 4 * C * D * (q.divisors.card : ℝ) ^ 2 * (Real.sqrt q + 1 / q.totient)
  let P := ∑ m ∈ A, ‖α m‖
  have hP : 0 ≤ P := sum_nonneg (fun _ _ => norm_nonneg _)
  have hB (q : ℕ) (hq : q ∈ Q) (m : ℕ) :
      ‖twoLongProductError q a m S T (fun x y => F ((x : ℝ) / U) * G ((y : ℝ) / V))‖ ≤ B q := by
    let _ : NeZero q := ⟨(mem_Ioc.mp (hQ hq)).1.ne'⟩
    exact twoLongProductError_smooth_norm_le q a m S T F G hU hV (ha q hq)
      hFneg hGneg hS hT hC hD hF hG
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRroot : 1 ≤ Real.sqrt R := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hR'
  have hpoint (q : ℕ) (hq : q ∈ Q) :
      ‖ρ q‖ * B q ≤ (8 * C * D * Real.sqrt R) * (q.divisors.card : ℝ) ^ (J + 2) := by
    obtain ⟨hq0, hqR⟩ := mem_Ioc.mp (hQ hq)
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
    have hsqrt : Real.sqrt q + 1 / q.totient ≤ 2 * Real.sqrt R := by
      have hqroot := Real.sqrt_le_sqrt (Nat.cast_le.mpr hqR : (q : ℝ) ≤ R)
      have hφ' := div_le_self (show (0 : ℝ) ≤ 1 by norm_num) hφ
      linarith
    calc
      _ ≤ (q.divisors.card : ℝ) ^ J * (4 * C * D * (q.divisors.card : ℝ) ^ 2 * (2 * Real.sqrt R)) := by
        exact mul_le_mul (hρ q hq) (mul_le_mul_of_nonneg_left hsqrt (by positivity))
          (by dsimp [B]; positivity) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hsum : (∑ q ∈ Q, (q.divisors.card : ℝ) ^ (J + 2)) ≤
      (R : ℝ) * (1 + Real.log R) ^ (2 ^ (J + 2) - 1) := by
    refine (sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)).trans ?_
    simpa only [Nat.floor_natCast, fouvryTau_two] using
      (sum_fouvryTau_pow_le_real (k := 2) (by norm_num) (J + 2) hR')
  calc
    _ ≤ P * ∑ q ∈ Q, ‖ρ q‖ * B q :=
      twoLongProductSignedError_norm_le S T A Q a α ρ _ B (fun q hq m _ => hB q hq m)
    _ ≤ P * ((8 * C * D * Real.sqrt R) * ∑ q ∈ Q, (q.divisors.card : ℝ) ^ (J + 2)) := by
      rw [mul_sum (s := Q) (a := 8 * C * D * Real.sqrt R)]
      exact mul_le_mul_of_nonneg_left (sum_le_sum hpoint) hP
    _ ≤ P * ((8 * C * D * Real.sqrt R) * ((R : ℝ) * (1 + Real.log R) ^ (2 ^ (J + 2) - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) hP
    _ = _ := by ring

end

end ImbalancedChen.Part3
