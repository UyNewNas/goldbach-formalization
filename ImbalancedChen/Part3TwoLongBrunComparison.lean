import ImbalancedChen.Part3BrunWeights
import ImbalancedChen.Part3LongSlotDivisorExpansion

/-!
# Finite Brun comparison for two long variables

The same finite carrier and complex coefficient occur in the progression
count and the exact coprime mean. The upper Brun projectors are compared
using the nonnegative two-variable gap and nonnegative majorants of the
two profiles.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

/-- The exact discrepancy for the two long variables at one short factor. -/
def twoLongProductError (q a m : ℕ) (S T : Finset ℕ) (w : ℕ → ℕ → ℂ) : ℂ :=
  (∑ x ∈ S, ∑ y ∈ T, if m * x * y ≡ a [MOD q] then w x y else 0) -
    (∑ x ∈ S, ∑ y ∈ T, if (m * x * y).Coprime q then w x y else 0) / (q.totient : ℂ)


/-- The signed short sequence stays inside the discrepancy sum. -/
def twoLongJointError (q a : ℕ) (M S T : Finset ℕ) (w : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ m ∈ M, twoLongProductError q a m S T (w m)

private def twoLongFilteredSum {R : Type*} [AddCommMonoid R]
    (M S T : Finset ℕ) (P : ℕ → ℕ → ℕ → Prop)
    [∀ m x y, Decidable (P m x y)] (w : ℕ → ℕ → ℕ → R) : R :=
  ∑ m ∈ M, ∑ x ∈ S, ∑ y ∈ T, if P m x y then w m x y else 0

/-- The exact primitive-product mean, with its physical totient divisor. -/
def twoLongJointMean (q : ℕ) (M S T : Finset ℕ) (W : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  twoLongFilteredSum M S T (fun m x y => (m * x * y).Coprime q) W / (q.totient : ℝ)

private theorem twoLongJointError_eq_mass_sub_mean
    (q a : ℕ) (M S T : Finset ℕ) (w : ℕ → ℕ → ℕ → ℂ) :
    twoLongJointError q a M S T w =
      twoLongFilteredSum M S T (fun m x y => m * x * y ≡ a [MOD q]) w -
      twoLongFilteredSum M S T (fun m x y => (m * x * y).Coprime q) w / (q.totient : ℂ) := by
  simp only [twoLongJointError, twoLongProductError, twoLongFilteredSum, sum_sub_distrib, sum_div]

private theorem twoLongFilteredSum_sub
    (M S T : Finset ℕ) (P : ℕ → ℕ → ℕ → Prop) [∀ m x y, Decidable (P m x y)]
    (w v : ℕ → ℕ → ℕ → ℂ) :
    twoLongFilteredSum M S T P (fun m x y => w m x y - v m x y) =
      twoLongFilteredSum M S T P w - twoLongFilteredSum M S T P v := by
  simp only [twoLongFilteredSum, ← sum_sub_distrib]
  refine sum_congr rfl fun m _ => sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases h : P m x y <;> simp [h]

private theorem twoLongFilteredSum_ofReal
    (M S T : Finset ℕ) (P : ℕ → ℕ → ℕ → Prop) [∀ m x y, Decidable (P m x y)]
    (W : ℕ → ℕ → ℕ → ℝ) :
    (↑(twoLongFilteredSum (R := ℝ) M S T P W) : ℂ) =
      twoLongFilteredSum M S T P (fun m x y => (W m x y : ℂ)) := by
  simp only [twoLongFilteredSum, Complex.ofReal_sum, apply_ite Complex.ofReal,
    Complex.ofReal_zero]

private theorem twoLongFilteredSum_norm_le
    (M S T : Finset ℕ) (P : ℕ → ℕ → ℕ → Prop) [∀ m x y, Decidable (P m x y)]
    (w : ℕ → ℕ → ℕ → ℂ) (W : ℕ → ℕ → ℕ → ℝ)
    (hW : ∀ m ∈ M, ∀ x ∈ S, ∀ y ∈ T, ‖w m x y‖ ≤ W m x y) :
    ‖twoLongFilteredSum M S T P w‖ ≤ twoLongFilteredSum M S T P W := by
  unfold twoLongFilteredSum
  refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
  refine (norm_sum_le _ _).trans (sum_le_sum fun x hx => ?_)
  refine (norm_sum_le _ _).trans (sum_le_sum fun y hy => ?_)
  by_cases h : P m x y
  · simpa only [if_pos h] using hW m hm x hx y hy
  · simp only [if_neg h, norm_zero, le_refl]

/-- A joint complex discrepancy comparison. The comparison weight
majorizes the pointwise norm of the change, and its discrepancy is still
the joint signed sum with one exact primitive mean. -/
theorem twoLongJointError_sub_norm_le_of_majorant
    (q a : ℕ) (M S T : Finset ℕ) (w v : ℕ → ℕ → ℕ → ℂ) (W : ℕ → ℕ → ℕ → ℝ)
    (hW : ∀ m ∈ M, ∀ x ∈ S, ∀ y ∈ T, ‖w m x y - v m x y‖ ≤ W m x y) :
    ‖twoLongJointError q a M S T w - twoLongJointError q a M S T v‖ ≤
      ‖twoLongJointError q a M S T (fun m x y => (W m x y : ℂ))‖ +
        2 * twoLongJointMean q M S T W := by
  let A := twoLongFilteredSum M S T (fun m x y => m * x * y ≡ a [MOD q]) W
  let loss : ℕ → ℕ → ℕ → ℂ := fun m x y => w m x y - v m x y
  have hsub : twoLongJointError q a M S T w - twoLongJointError q a M S T v =
      twoLongJointError q a M S T loss := by
    simp only [twoLongJointError_eq_mass_sub_mean, loss, twoLongFilteredSum_sub]
    ring
  have hmean : ‖twoLongFilteredSum M S T (fun m x y => (m * x * y).Coprime q) loss /
      (q.totient : ℂ)‖ ≤ twoLongJointMean q M S T W := by
    rw [norm_div, Complex.norm_natCast, twoLongJointMean]
    exact div_le_div_of_nonneg_right (twoLongFilteredSum_norm_le M S T _ loss W hW)
      (Nat.cast_nonneg _)
  have hreal : twoLongJointError q a M S T (fun m x y => (W m x y : ℂ)) =
      ((A - twoLongJointMean q M S T W : ℝ) : ℂ) := by
    simp only [twoLongJointError_eq_mass_sub_mean, A, twoLongJointMean,
      Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast, twoLongFilteredSum_ofReal]
  calc
    _ = ‖twoLongJointError q a M S T loss‖ := by rw [hsub]
    _ ≤ A + twoLongJointMean q M S T W := by
      rw [twoLongJointError_eq_mass_sub_mean]
      exact (norm_sub_le _ _).trans
        (add_le_add (twoLongFilteredSum_norm_le M S T _ loss W hW) hmean)
    _ ≤ _ := by
      rw [hreal, Complex.norm_real, Real.norm_eq_abs]
      linarith only [le_abs_self (A - twoLongJointMean q M S T W)]

/-- The product gap is one upper projector times the other slot's gap,
summed over the two slots. -/
def twoLongBrunGap (P : Finset ℕ) (h x y : ℕ) : ℝ :=
  (((brunProjector P h x - brunProjector P (h + 1) x) * brunProjector P h y +
    brunProjector P h x * (brunProjector P h y - brunProjector P (h + 1) y) : ℤ) : ℝ)

private theorem twoLongBrun_difference_norm_le
    (P : Finset ℕ) (h x y : ℕ) (hP : ∀ p ∈ P, p.Prime) (hh : Even h) :
    ‖((brunRoughIndicator P x * brunRoughIndicator P y : ℤ) : ℂ) -
        ((brunProjector P h x * brunProjector P h y : ℤ) : ℂ)‖ ≤ twoLongBrunGap P h x y := by
  obtain ⟨hpos, hgap⟩ := brunProjector_product_gap P h x y hP hh
  have h : |brunRoughIndicator P x * brunRoughIndicator P y -
      brunProjector P h x * brunProjector P h y| ≤
      (brunProjector P h x - brunProjector P (h + 1) x) * brunProjector P h y +
        brunProjector P h x * (brunProjector P h y - brunProjector P (h + 1) y) := by
    rw [← abs_neg, neg_sub, abs_of_nonneg hpos]
    exact hgap
  rw [← Int.cast_sub, Complex.norm_intCast, twoLongBrunGap]
  exact_mod_cast h

/-- Manuscript (E3) on the original finite carriers. The two coefficients
retain their signs on the left. On the right the normalized coprime
mean and the discrepancy use the same nonnegative product gap profile. -/
theorem twoLongJointError_sub_norm_le_brun
    (q a : ℕ) (M S T P : Finset ℕ) (h : ℕ)
    (α f g : ℕ → ℂ) (F G : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hh : Even h)
    (hF : ∀ x ∈ S, ‖f x‖ ≤ F x) (hG : ∀ y ∈ T, ‖g y‖ ≤ G y) :
    ‖twoLongJointError q a M S T (fun m x y => α m * f x * g y *
          ((brunRoughIndicator P x * brunRoughIndicator P y : ℤ) : ℂ)) -
      twoLongJointError q a M S T (fun m x y => α m * f x * g y *
          ((brunProjector P h x * brunProjector P h y : ℤ) : ℂ))‖ ≤
      ‖twoLongJointError q a M S T (fun m x y =>
        ((‖α m‖ * F x * G y * twoLongBrunGap P h x y : ℝ) : ℂ))‖ +
      2 * twoLongJointMean q M S T (fun m x y => ‖α m‖ * F x * G y * twoLongBrunGap P h x y) := by
  apply twoLongJointError_sub_norm_le_of_majorant
  intro m _ x hx y hy
  rw [← mul_sub, norm_mul, norm_mul, norm_mul]
  have hFx : 0 ≤ F x := (norm_nonneg _).trans (hF x hx)
  have hFG : ‖α m‖ * ‖f x‖ * ‖g y‖ ≤ ‖α m‖ * F x * G y :=
    mul_le_mul (mul_le_mul_of_nonneg_left (hF x hx) (norm_nonneg _)) (hG y hy)
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) hFx)
  exact mul_le_mul hFG (twoLongBrun_difference_norm_le P h x y hP hh) (norm_nonneg _)
    (mul_nonneg (mul_nonneg (norm_nonneg _) hFx) ((norm_nonneg _).trans (hG y hy)))

/-- The exact mean of a product profile separates into its three primitive
masses, with a single totient divisor. -/
theorem twoLongJointMean_mul_profile
    (q : ℕ) (M S T : Finset ℕ) (A B C : ℕ → ℝ) :
    twoLongJointMean q M S T (fun m x y => A m * B x * C y) =
      (∑ m ∈ M, if m.Coprime q then A m else 0) *
        (∑ x ∈ S, if x.Coprime q then B x else 0) *
        (∑ y ∈ T, if y.Coprime q then C y else 0) / (q.totient : ℝ) := by
  unfold twoLongJointMean twoLongFilteredSum
  congr 1
  let u (m : ℕ) := if m.Coprime q then A m else 0
  let v (x : ℕ) := if x.Coprime q then B x else 0
  let z (y : ℕ) := if y.Coprime q then C y else 0
  change _ = (∑ m ∈ M, u m) * (∑ x ∈ S, v x) * (∑ y ∈ T, z y)
  rw [sum_mul M u, sum_mul M (fun m => u m * ∑ x ∈ S, v x)]
  apply sum_congr rfl
  intro m _
  rw [mul_sum S v, sum_mul S (fun x => u m * v x)]
  apply sum_congr rfl
  intro x _
  rw [mul_sum T z]
  apply sum_congr rfl
  intro y _
  simp only [u, v, z, Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

private def twoLongDiscrepancyKernel (q a z : ℕ) : ℂ :=
  (if z ≡ a [MOD q] then 1 else 0) -
    (if z.Coprime q then 1 else 0) / (q.totient : ℂ)

private theorem twoLongProductError_eq_sum_kernel
    (q a m : ℕ) (S T : Finset ℕ) (w : ℕ → ℕ → ℂ) :
    twoLongProductError q a m S T w =
      ∑ x ∈ S, ∑ y ∈ T, w x y * twoLongDiscrepancyKernel q a (m * x * y) := by
  have hmul (c : ℂ) (P : Prop) [Decidable P] :
      c * (if P then 1 else 0) = (if P then c else 0) := by
    by_cases h : P <;> simp [h]
  simp only [twoLongProductError, twoLongDiscrepancyKernel, mul_sub, ← mul_div_assoc,
    sum_sub_distrib, ← sum_div, hmul]

/-- A separated short coefficient can be pulled outside each fixed-short
discrepancy. The short sum itself remains inside the norm in (E3). -/
theorem twoLongJointError_factor_short (q a : ℕ) (M S T : Finset ℕ)
    (α : ℕ → ℂ) (w : ℕ → ℕ → ℂ) :
    twoLongJointError q a M S T (fun m x y => α m * w x y) =
      ∑ m ∈ M, α m * twoLongProductError q a m S T w := by
  unfold twoLongJointError
  apply sum_congr rfl
  intro m _
  simp only [twoLongProductError_eq_sum_kernel, mul_assoc, ← mul_sum]

/-- The exact quotient of the part of a carrier divisible by d. -/
def twoLongQuotientCarrier (S : Finset ℕ) (d : ℕ) : Finset ℕ :=
  (S.filter fun n => d ∣ n).image fun n => n / d

theorem mem_twoLongQuotientCarrier (S : Finset ℕ) {d n : ℕ} (hd : 0 < d) :
    n ∈ twoLongQuotientCarrier S d ↔ d * n ∈ S := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := mem_image.mp h
    obtain ⟨hxS, hdx⟩ := mem_filter.mp hx
    rwa [Nat.mul_div_cancel_left' hdx]
  · intro hn
    exact mem_image.mpr ⟨d * n, mem_filter.mpr ⟨hn, dvd_mul_right d n⟩,
      Nat.mul_div_cancel_left n hd⟩

private theorem sum_twoLongQuotientCarrier
    (S : Finset ℕ) {d : ℕ} (hd : 0 < d) (f : ℕ → ℂ) :
    (∑ n ∈ twoLongQuotientCarrier S d, f (d * n)) =
      ∑ n ∈ S.filter (fun n => d ∣ n), f n := by
  refine sum_bij (fun n _ => d * n) ?_ ?_ ?_ ?_
  · intro n hn
    exact mem_filter.mpr ⟨(mem_twoLongQuotientCarrier S hd).mp hn, dvd_mul_right d n⟩
  · intro n _ j _ h
    exact Nat.mul_left_cancel hd h
  · intro n hn
    obtain ⟨hnS, k, rfl⟩ := mem_filter.mp hn
    exact ⟨k, (mem_twoLongQuotientCarrier S hd).mpr hnS, rfl⟩
  · intros
    rfl

private theorem sum_divisorExpansion_mul_eq_sum
    (S D : Finset ℕ) (c f : ℕ → ℂ) (hD : ∀ d ∈ D, 0 < d) :
    (∑ n ∈ S, part3DivisorExpansion D c n * f n) =
      ∑ d ∈ D, c d * ∑ n ∈ twoLongQuotientCarrier S d, f (d * n) := by
  unfold part3DivisorExpansion
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_twoLongQuotientCarrier S (hD d hd), mul_sum, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hn : d ∣ n <;> simp [hn]

/-- Expanding both divisor weights retains the exact congruence and
primitive mean on their two quotient carriers. The physical short
factor is multiplied by both divisors. -/
theorem twoLongProductError_divisorExpansion_eq_sum
    (q a m : ℕ) (S T D E : Finset ℕ) (f g c b : ℕ → ℂ)
    (hD : ∀ d ∈ D, 0 < d) (hE : ∀ e ∈ E, 0 < e) :
    twoLongProductError q a m S T (fun x y =>
        f x * g y * part3DivisorExpansion D c x * part3DivisorExpansion E b y) =
      ∑ d ∈ D, ∑ e ∈ E, c d * b e *
        twoLongProductError q a (m * d * e) (twoLongQuotientCarrier S d)
          (twoLongQuotientCarrier T e) (fun x y => f (d * x) * g (e * y)) := by
  simp only [twoLongProductError_eq_sum_kernel]
  calc
    _ = ∑ x ∈ S, part3DivisorExpansion D c x * ∑ y ∈ T,
        part3DivisorExpansion E b y * (f x * g y * twoLongDiscrepancyKernel q a (m * x * y)) := by
      simp only [mul_sum]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      ring
    _ = ∑ d ∈ D, c d * ∑ x ∈ twoLongQuotientCarrier S d, ∑ y ∈ T,
        part3DivisorExpansion E b y *
          (f (d * x) * g y * twoLongDiscrepancyKernel q a (m * (d * x) * y)) :=
      sum_divisorExpansion_mul_eq_sum S D c _ hD
    _ = _ := by
      apply sum_congr rfl
      intro d _
      simp_rw [sum_divisorExpansion_mul_eq_sum T E b _ hE]
      rw [sum_comm]
      simp only [mul_sum]
      refine sum_congr rfl fun e _ => sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      have heq : m * (d * x) * (e * y) = m * d * e * x * y := by ac_rfl
      rw [heq]
      ring

/-- The quotient profiles are the original real profiles sampled at the
rescaled lengths. -/
theorem twoLongProductError_divisorExpansion_scale_eq_sum
    (q a m : ℕ) (S T D E : Finset ℕ) (U V : ℝ) (f g : ℝ → ℂ) (c b : ℕ → ℂ)
    (hD : ∀ d ∈ D, 0 < d) (hE : ∀ e ∈ E, 0 < e) :
    twoLongProductError q a m S T (fun x y =>
        f ((x : ℝ) / U) * g ((y : ℝ) / V) *
          part3DivisorExpansion D c x * part3DivisorExpansion E b y) =
      ∑ d ∈ D, ∑ e ∈ E, c d * b e *
        twoLongProductError q a (m * d * e) (twoLongQuotientCarrier S d)
          (twoLongQuotientCarrier T e)
          (fun x y => f ((x : ℝ) / (U / (d : ℝ))) * g ((y : ℝ) / (V / (e : ℝ)))) := by
  rw [twoLongProductError_divisorExpansion_eq_sum q a m S T D E
    (fun x => f ((x : ℝ) / U)) (fun y => g ((y : ℝ) / V)) c b hD hE]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  simp only [Nat.cast_mul, div_div_eq_mul_div]
  congr 1
  congr 1
  funext x y
  rw [mul_comm (d : ℝ) (x : ℝ), mul_comm (e : ℝ) (y : ℝ)]

end

end ImbalancedChen.Part3
