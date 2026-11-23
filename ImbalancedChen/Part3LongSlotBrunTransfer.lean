import ImbalancedChen.Part3LongSlotDivisorExpansion
import ImbalancedChen.Part3BrunWeights

/-!
# The one-long Brun comparison with the exact coprime mean

The same long-slot weight occurs in the progression and the primitive-source
mean. A pointwise upper approximation and nonnegative gap transfer their
errors to the original weight, retaining the exact gap mean in the comparison.
-/

namespace ImbalancedChen

noncomputable section

open Classical Finset
open scoped BigOperators

private def part3LongSlotWeightedAP (L U q a m : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ (Ioc L U).filter (fun n => m * n ≡ a [MOD q]), w n

/-- The mean of the actual primitive products in the fixed interval. -/
def part3LongSlotWeightedMean (L U q m : ℕ) (w : ℕ → ℝ) : ℝ :=
  (∑ n ∈ (Ioc L U).filter (fun n => (m * n).Coprime q), w n) / q.totient

/-- The literal progression minus the exact weighted primitive mean. -/
def part3LongSlotWeightedRemainder (L U q a m : ℕ) (w : ℕ → ℝ) : ℝ :=
  part3LongSlotWeightedAP L U q a m w - part3LongSlotWeightedMean L U q m w

/-- Positivity transfers the exact discrepancy from a divisor upper
approximation to the original long-slot weight. -/
theorem part3LongSlotWeightedRemainder_abs_le_of_brun_gap (L U q a m : ℕ)
    (w upper gap : ℕ → ℝ)
    (hgap : ∀ n ∈ Ioc L U, 0 ≤ upper n - w n ∧ upper n - w n ≤ gap n) :
    |part3LongSlotWeightedRemainder L U q a m w| ≤
      |part3LongSlotWeightedRemainder L U q a m upper| +
      |part3LongSlotWeightedRemainder L U q a m gap| +
      2 * part3LongSlotWeightedMean L U q m gap := by
  let loss : ℕ → ℝ := fun n => upper n - w n
  have hsum (S : Finset ℕ) (hS : S ⊆ Ioc L U) :
      0 ≤ (∑ n ∈ S, loss n) ∧ (∑ n ∈ S, loss n) ≤ ∑ n ∈ S, gap n :=
    ⟨sum_nonneg (fun n hn => (hgap n (hS hn)).1),
      sum_le_sum (fun n hn => (hgap n (hS hn)).2)⟩
  have hAP := hsum _ (filter_subset (fun n => m * n ≡ a [MOD q]) (Ioc L U))
  have hC := hsum _ (filter_subset (fun n => (m * n).Coprime q) (Ioc L U))
  have hmean0 : 0 ≤ part3LongSlotWeightedMean L U q m loss :=
    div_nonneg hC.1 (Nat.cast_nonneg _)
  have hmean : part3LongSlotWeightedMean L U q m loss ≤
      part3LongSlotWeightedMean L U q m gap :=
    div_le_div_of_nonneg_right hC.2 (Nat.cast_nonneg _)
  have hlin : part3LongSlotWeightedRemainder L U q a m w =
      part3LongSlotWeightedRemainder L U q a m upper -
      part3LongSlotWeightedRemainder L U q a m loss := by
    unfold part3LongSlotWeightedRemainder part3LongSlotWeightedAP part3LongSlotWeightedMean
    simp only [loss, sum_sub_distrib, sub_div]
    ring
  have hloss : |part3LongSlotWeightedRemainder L U q a m loss| ≤
      part3LongSlotWeightedAP L U q a m gap + part3LongSlotWeightedMean L U q m gap := by
    have hAP0 : 0 ≤ part3LongSlotWeightedAP L U q a m loss := hAP.1
    calc
      _ ≤ |part3LongSlotWeightedAP L U q a m loss| +
          |part3LongSlotWeightedMean L U q m loss| := abs_sub _ _
      _ = part3LongSlotWeightedAP L U q a m loss + part3LongSlotWeightedMean L U q m loss :=
        by rw [abs_of_nonneg hAP0, abs_of_nonneg hmean0]
      _ ≤ _ := add_le_add hAP.2 hmean
  have hgapError : part3LongSlotWeightedAP L U q a m gap + part3LongSlotWeightedMean L U q m gap ≤
      |part3LongSlotWeightedRemainder L U q a m gap| +
        2 * part3LongSlotWeightedMean L U q m gap := by
    have h := le_abs_self (part3LongSlotWeightedRemainder L U q a m gap)
    unfold part3LongSlotWeightedRemainder at h ⊢
    linarith only [h]
  rw [hlin]
  calc
    _ ≤ |part3LongSlotWeightedRemainder L U q a m upper| +
        |part3LongSlotWeightedRemainder L U q a m loss| := abs_sub _ _
    _ ≤ |part3LongSlotWeightedRemainder L U q a m upper| +
        (|part3LongSlotWeightedRemainder L U q a m gap| +
          2 * part3LongSlotWeightedMean L U q m gap) := add_le_add le_rfl (hloss.trans hgapError)
    _ = _ := by ring

/-- The exact gap mean is bounded by the harmonic divisor mass. The factor
`U` pays the original right endpoint before the choice of primitive residue. -/
theorem part3LongSlotWeightedMean_divisorExpansion_le (L U q m : ℕ)
    (D : Finset ℕ) (gap : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d)
    (hnonneg : ∀ d ∈ D, 0 ≤ gap d) :
    part3LongSlotWeightedMean L U q m (part3DivisorExpansion D gap) ≤
      (U : ℝ) / q.totient * ∑ d ∈ D, gap d / d := by
  let P : ℕ → Prop := fun n => (m * n).Coprime q
  have hcount (d : ℕ) (hd : d ∈ D) :
      (((Ico (L / d + 1) (U / d + 1)).filter (fun k => P (d * k))).card : ℝ) ≤
        (U : ℝ) / d := by
    have hcard : ((Ico (L / d + 1) (U / d + 1)).filter (fun k => P (d * k))).card ≤ U / d := by
      refine (card_filter_le _ _).trans ?_
      rw [Nat.card_Ico, Nat.add_sub_add_right]
      exact Nat.sub_le _ _
    have hmul := (Nat.le_div_iff_mul_le (hD d hd)).mp hcard
    exact (le_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast hD d hd)).mpr (by exact_mod_cast hmul)
  unfold part3LongSlotWeightedMean
  change (∑ n ∈ (Ioc L U).filter P, part3DivisorExpansion D gap n) / q.totient ≤ _
  rw [part3_sum_divisorExpansion_filter_eq L U D gap P hD]
  calc
    _ ≤ (∑ d ∈ D, gap d * ((U : ℝ) / d)) / q.totient :=
      div_le_div_of_nonneg_right
        (sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hcount d hd) (hnonneg d hd)))
        (Nat.cast_nonneg _)
    _ = _ := by
      have hsum : (∑ d ∈ D, gap d * ((U : ℝ) / d)) = (U : ℝ) * ∑ d ∈ D, gap d / d := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        ring
      rw [hsum]
      ring

private theorem part3_ofReal_divisorExpansion (D : Finset ℕ) (coeff : ℕ → ℝ) (n : ℕ) :
    ((part3DivisorExpansion D coeff n : ℝ) : ℂ) =
      part3DivisorExpansion D (fun d => (coeff d : ℂ)) n := by
  unfold part3DivisorExpansion
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro d _
  by_cases hd : d ∣ n <;> simp [hd]

private theorem part3LongSlotWeightedRemainder_abs_le_of_divisorExpansion (L U q a m : ℕ)
    (D : Finset ℕ) (coeff : ℕ → ℝ) (hD : ∀ d ∈ D, 0 < d) (hq : 0 < q) (ha : a.Coprime q) :
    |part3LongSlotWeightedRemainder L U q a m (part3DivisorExpansion D coeff)| ≤
      2 * ∑ d ∈ D, |coeff d| := by
  have hcast : (part3LongSlotWeightedRemainder L U q a m (part3DivisorExpansion D coeff) : ℂ) =
      part3LongSlotDivisorExpansionRemainder L U q a m D (fun d => (coeff d : ℂ)) := by
    unfold part3LongSlotWeightedRemainder part3LongSlotWeightedAP part3LongSlotWeightedMean
      part3LongSlotDivisorExpansionRemainder
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_sum,
      part3_ofReal_divisorExpansion]
  have h := part3LongSlotDivisorExpansionRemainder_norm_le L U q a m D
    (fun d => (coeff d : ℂ)) hD hq ha
  rw [← hcast] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

/-- The fixed-short-factor Brun estimate combines both finite divisor errors
with the harmonic bound on the gap mean. -/
theorem part3LongSlotWeightedRemainder_abs_le_of_brun (L U q a m : ℕ)
    (w : ℕ → ℝ) (D E : Finset ℕ) (coeff gap : ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d) (hE : ∀ d ∈ E, 0 < d) (hnonneg : ∀ d ∈ E, 0 ≤ gap d)
    (hgap : ∀ n ∈ Ioc L U,
      0 ≤ part3DivisorExpansion D coeff n - w n ∧
      part3DivisorExpansion D coeff n - w n ≤ part3DivisorExpansion E gap n)
    (hq : 0 < q) (ha : a.Coprime q) :
    |part3LongSlotWeightedRemainder L U q a m w| ≤
      2 * ((∑ d ∈ D, |coeff d|) + ∑ d ∈ E, gap d) +
        2 * ((U : ℝ) / q.totient * ∑ d ∈ E, gap d / d) := by
  have htransfer := part3LongSlotWeightedRemainder_abs_le_of_brun_gap L U q a m w _ _ hgap
  have hupper := part3LongSlotWeightedRemainder_abs_le_of_divisorExpansion L U q a m D coeff hD hq ha
  have herror := part3LongSlotWeightedRemainder_abs_le_of_divisorExpansion L U q a m E gap hE hq ha
  have habs : (∑ d ∈ E, |gap d|) = ∑ d ∈ E, gap d :=
    sum_congr rfl (fun d hd => abs_of_nonneg (hnonneg d hd))
  rw [habs] at herror
  have hmean := part3LongSlotWeightedMean_divisorExpansion_le L U q m E gap hE hnonneg
  linarith only [htransfer, hupper, herror, hmean]

/-- The weighted progression errors retain the original short and
physical-modulus coefficients in the same finite sum. -/
def part3LongSlotWeightedSignedError (S Q : Finset ℕ) (alpha rho : ℕ → ℂ)
    (L U a : ℕ) (w : ℕ → ℝ) : ℂ :=
  ∑ q ∈ Q, rho q * ∑ m ∈ S, alpha m * (part3LongSlotWeightedRemainder L U q a m w : ℂ)

/-- The Brun comparison is uniform over short factors and physical moduli.
The harmonic gap cost retains its modulus-dependent `1 / φ(q)` factor. -/
theorem part3LongSlotWeightedSignedError_norm_le_of_brun (S Q D E : Finset ℕ)
    (alpha rho : ℕ → ℂ) (L U a : ℕ) (w coeff gap : ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d) (hE : ∀ d ∈ E, 0 < d) (hnonneg : ∀ d ∈ E, 0 ≤ gap d)
    (hgap : ∀ n ∈ Ioc L U,
      0 ≤ part3DivisorExpansion D coeff n - w n ∧
      part3DivisorExpansion D coeff n - w n ≤ part3DivisorExpansion E gap n)
    (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q) :
    ‖part3LongSlotWeightedSignedError S Q alpha rho L U a w‖ ≤
      (∑ m ∈ S, ‖alpha m‖) * ∑ q ∈ Q, ‖rho q‖ *
        (2 * ((∑ d ∈ D, |coeff d|) + ∑ d ∈ E, gap d) +
          2 * ((U : ℝ) / q.totient * ∑ d ∈ E, gap d / d)) := by
  let cost (q : ℕ) : ℝ := 2 * ((∑ d ∈ D, |coeff d|) + ∑ d ∈ E, gap d) +
    2 * ((U : ℝ) / q.totient * ∑ d ∈ E, gap d / d)
  have hshort (q : ℕ) (hqQ : q ∈ Q) :
      ‖∑ m ∈ S, alpha m * (part3LongSlotWeightedRemainder L U q a m w : ℂ)‖ ≤
        (∑ m ∈ S, ‖alpha m‖) * cost q := by
    calc
      _ ≤ ∑ m ∈ S, ‖alpha m * (part3LongSlotWeightedRemainder L U q a m w : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ S, ‖alpha m‖ * cost q := by
        apply sum_le_sum
        intro m _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (part3LongSlotWeightedRemainder_abs_le_of_brun L U q a m w D E coeff gap
            hD hE hnonneg hgap (hq q hqQ) (ha q hqQ)) (norm_nonneg _)
      _ = _ := by rw [← sum_mul]
  unfold part3LongSlotWeightedSignedError
  change _ ≤ (∑ m ∈ S, ‖alpha m‖) * ∑ q ∈ Q, ‖rho q‖ * cost q
  calc
    _ ≤ ∑ q ∈ Q, ‖rho q * ∑ m ∈ S, alpha m *
      (part3LongSlotWeightedRemainder L U q a m w : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ((∑ m ∈ S, ‖alpha m‖) * cost q) := by
      apply sum_le_sum
      intro q hqQ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hshort q hqQ) (norm_nonneg _)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring

open Part3 in
/-- The actual rough indicator on the exact long interval is controlled by
the two Brun divisor supports and the factorial reciprocal-mass bound. -/
theorem part3LongSlotBrunRoughSignedError_norm_le (S Q P : Finset ℕ)
    (alpha rho : ℕ → ℂ) (L U a h : ℕ) (hP : ∀ p ∈ P, p.Prime) (hh : Even h)
    (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q) :
    ‖part3LongSlotWeightedSignedError S Q alpha rho L U a
      (fun n => (brunRoughIndicator P n : ℝ))‖ ≤
      (∑ m ∈ S, ‖alpha m‖) * ∑ q ∈ Q, ‖rho q‖ *
        (2 * (((brunDivisors P h).card : ℝ) + (brunGapDivisors P h).card) +
          2 * ((U : ℝ) / q.totient *
            ((∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial))) := by
  let D := brunDivisors P h
  let E := brunGapDivisors P h
  let coeff : ℕ → ℝ := fun d => (-1 : ℝ) ^ d.primeFactors.card
  let gap : ℕ → ℝ := fun _ => 1
  let w : ℕ → ℝ := fun n => (brunRoughIndicator P n : ℝ)
  have hD (d : ℕ) (hd : d ∈ D) : 0 < d := by
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hd
    exact prod_pos fun p hp => (hP p ((mem_powersetCard.mp (mem_sigma.mp hu).2).1 hp)).pos
  have hE (d : ℕ) (hd : d ∈ E) : 0 < d := by
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hd
    exact prod_pos fun p hp => (hP p ((mem_powersetCard.mp hs).1 hp)).pos
  have hupper (n : ℕ) : (brunProjector P h n : ℝ) = part3DivisorExpansion D coeff n := by
    rw [brunProjector_eq_divisor_sum P h n hP]
    unfold part3DivisorExpansion D coeff
    push_cast
    apply sum_congr rfl
    intro d _
    by_cases hd : d ∣ n <;> simp [hd]
  have hgap (n : ℕ) : (brunProjector P h n : ℝ) - (brunProjector P (h + 1) n : ℝ) =
      part3DivisorExpansion E gap n := by
    rw [← Int.cast_sub, brunProjector_gap_eq_divisor_sum P h n hP hh]
    unfold part3DivisorExpansion E gap
    push_cast
    apply sum_congr rfl
    intro d _
    by_cases hd : d ∣ n <;> simp [hd]
  have hbracket (n : ℕ) (_ : n ∈ Ioc L U) :
      0 ≤ part3DivisorExpansion D coeff n - w n ∧
      part3DivisorExpansion D coeff n - w n ≤ part3DivisorExpansion E gap n := by
    obtain ⟨hlo, hhi, _⟩ := brunProjector_brackets P h n hP hh
    have hloReal : (brunProjector P (h + 1) n : ℝ) ≤ (brunRoughIndicator P n : ℝ) :=
      by exact_mod_cast hlo
    have hhiReal : (brunRoughIndicator P n : ℝ) ≤ (brunProjector P h n : ℝ) :=
      by exact_mod_cast hhi
    rw [← hupper, ← hgap]
    exact ⟨sub_nonneg.mpr hhiReal, sub_le_sub_left hloReal _⟩
  have hcoeff : (∑ d ∈ D, |coeff d|) = (D.card : ℝ) := by simp [coeff, abs_pow]
  have hgapCard : (∑ d ∈ E, gap d) = (E.card : ℝ) := by simp [gap]
  have hharmonic : (∑ d ∈ E, gap d / d) ≤
      (∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial := by
    simpa only [gap, one_div] using brunGapDivisors_sum_reciprocal_le P h hP
  refine (part3LongSlotWeightedSignedError_norm_le_of_brun S Q D E alpha rho L U a
    w coeff gap hD hE (fun _ _ => zero_le_one) hbracket hq ha).trans ?_
  rw [hcoeff, hgapCard]
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg (fun _ _ => norm_nonneg _))
  apply sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hharmonic (by positivity)) (by norm_num)

open Part3 in
/-- The original rank caps make the coefficient cost depend only on the
prime cutoff and Brun order. -/
theorem part3LongSlotBrunRoughSignedError_norm_le_of_prime_cap (S Q P : Finset ℕ)
    (alpha rho : ℕ → ℂ) (L U a z h : ℕ) (hz : 1 ≤ z)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) (hh : Even h)
    (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q) :
    ‖part3LongSlotWeightedSignedError S Q alpha rho L U a
      (fun n => (brunRoughIndicator P n : ℝ))‖ ≤
      (∑ m ∈ S, ‖alpha m‖) * ∑ q ∈ Q, ‖rho q‖ *
        (2 * ((z : ℝ) ^ h + (z : ℝ) ^ (h + 1)) +
          2 * ((U : ℝ) / q.totient *
            ((∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial))) := by
  have hupper : ((brunDivisors P h).card : ℝ) ≤ (z : ℝ) ^ h := by
    have hcard := card_le_card (brunDivisors_subset_Icc P z h hz hP)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    exact_mod_cast hcard
  have hgap : ((brunGapDivisors P h).card : ℝ) ≤ (z : ℝ) ^ (h + 1) := by
    have hcard := card_le_card (brunGapDivisors_subset_Icc P z h hz hP)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    exact_mod_cast hcard
  refine (part3LongSlotBrunRoughSignedError_norm_le S Q P alpha rho L U a h
    (fun p hp => (hP p hp).1) hh hq ha).trans ?_
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg (fun _ _ => norm_nonneg _))
  apply sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hupper hgap) (by norm_num)) le_rfl

end

end ImbalancedChen
