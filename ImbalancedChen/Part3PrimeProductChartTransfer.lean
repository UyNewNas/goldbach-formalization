import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.Part3LongSlotBrunTransfer
import ImbalancedChen.Part3TwoLongSmooth

/-!
# Complete-product coefficients for chart assembly

The arithmetic kernel depends only on the complete product. Grouping the
labelled source by that product therefore preserves both weighted counts
and the exact primitive mean. A separated chart can be matched at the
coefficient level to a long-slot supplier.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators Pointwise SchwartzMap FourierTransform

/-- The full coefficient mass of one value of the finite product map. -/
def finiteProductMass {I : Type*} (S : Finset I) (p : I → ℕ) (w : I → ℂ) (b : ℕ) : ℂ :=
  ∑ t ∈ S, if p t = b then w t else 0

/-- The arithmetic count-minus-mean kernel depends on the actual product. -/
def finiteProductKernel (q a b : ℕ) : ℂ :=
  (if b ≡ a [MOD q] then 1 else 0) -
    (if b.Coprime q then 1 else 0) / (q.totient : ℂ)

/-- Signed distribution error of finite complete-product coefficients. -/
def finiteProductSignedError (B Q : Finset ℕ) (a : ℕ) (ρ c : ℕ → ℂ) : ℂ :=
  ∑ q ∈ Q, ρ q * ∑ b ∈ B, c b * finiteProductKernel q a b

private theorem sum_mul_finiteProductKernel {I : Type*} (S : Finset I)
    (q a : ℕ) (p : I → ℕ) (w : I → ℂ) :
    (∑ t ∈ S, w t * finiteProductKernel q a (p t)) =
      (∑ t ∈ S, if p t ≡ a [MOD q] then w t else 0) -
        (∑ t ∈ S, if (p t).Coprime q then w t else 0) / (q.totient : ℂ) := by
  have hterm (c : ℂ) (P : Prop) [Decidable P] :
      c * (if P then 1 else 0) = (if P then c else 0) := by
    by_cases h : P <;> simp [h]
  simp only [finiteProductKernel, mul_sub, ← mul_div_assoc, sum_sub_distrib, ← sum_div, hterm]

/-- Product fibres preserve every labelled summand in both sides of
the discrepancy, including distinct tuples with the same product. -/
theorem finiteProductSignedError_fibres {I : Type*} (S : Finset I) (p : I → ℕ) (w : I → ℂ)
    (B Q : Finset ℕ) (a : ℕ) (ρ : ℕ → ℂ) (hB : ∀ t ∈ S, w t ≠ 0 → p t ∈ B) :
    finiteProductSignedError B Q a ρ (finiteProductMass S p w) =
      ∑ q ∈ Q, ρ q * ∑ t ∈ S, w t * finiteProductKernel q a (p t) := by
  unfold finiteProductSignedError finiteProductMass
  apply sum_congr rfl
  intro q _
  congr 1
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  rw [sum_eq_single (p t)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    have hz : w t = 0 := by
      by_contra hn
      exact h (hB t ht hn)
    simp [hz]

/-- The complete-product coefficients of the actual labelled prime source. -/
def labelledPrimeProductMass (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) : ℕ → ℂ :=
  finiteProductMass (labelledPrimeTuples k P) labelledProduct (fun t => (W t : ℂ))

/-- Exact transfer of the literal prime-product target to complete-product
coefficients. The modulus weights and mean denominator are unchanged. -/
theorem primeProductSignedError_eq_fibreError (k P N : ℕ) (Q B : Finset ℕ) (ρ : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ)
    (hB : ∀ t ∈ labelledPrimeTuples k P, W t ≠ 0 → labelledProduct t ∈ B) :
    (primeProductSignedError k P N Q ρ W : ℂ) =
      finiteProductSignedError B Q N (fun q => (ρ q : ℂ)) (labelledPrimeProductMass k P W) := by
  unfold labelledPrimeProductMass
  rw [finiteProductSignedError_fibres _ _ _ _ _ _ _
    (fun t ht hn => hB t ht (by exact_mod_cast hn))]
  simp only [primeProductSignedError, finiteProductKernel, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
    apply_ite Complex.ofReal, Complex.ofReal_zero, Complex.ofReal_one]

/-- The complete-product coefficients of a single long-slot chart. -/
def oneLongProductMass (A : Finset ℕ) (L U : ℕ) (α : ℕ → ℂ) (w : ℕ → ℝ) : ℕ → ℂ :=
  finiteProductMass (A ×ˢ Ioc L U) (fun t => t.1 * t.2)
    (fun t => α t.1 * (w t.2 : ℂ))

/-- The complete-product coefficients of a two-long chart. -/
def twoLongProductMass (S T A : Finset ℕ) (α : ℕ → ℂ) (w : ℕ → ℕ → ℂ) : ℕ → ℂ :=
  finiteProductMass (A ×ˢ (S ×ˢ T)) (fun t => t.1 * t.2.1 * t.2.2)
    (fun t => α t.1 * w t.2.1 t.2.2)

/-- The existing signed one-long error is exactly the complete-product
error of its coefficient mass. -/
theorem oneLongSignedError_eq_fibreError
    (A Q B : Finset ℕ) (L U a : ℕ) (α ρ : ℕ → ℂ) (w : ℕ → ℝ)
    (hB : ∀ m ∈ A, ∀ n ∈ Ioc L U, α m * (w n : ℂ) ≠ 0 → m * n ∈ B) :
    part3LongSlotWeightedSignedError A Q α ρ L U a w =
      finiteProductSignedError B Q a ρ (oneLongProductMass A L U α w) := by
  unfold oneLongProductMass
  rw [finiteProductSignedError_fibres]
  · unfold part3LongSlotWeightedSignedError
    apply sum_congr rfl
    intro q _
    congr 1
    rw [Finset.sum_product]
    apply sum_congr rfl
    intro m _
    simp only [mul_assoc, ← mul_sum, sum_mul_finiteProductKernel]
    congr 1
    unfold part3LongSlotWeightedRemainder part3LongSlotWeightedMean
    change
      (↑((∑ n ∈ (Ioc L U).filter (fun n => m * n ≡ a [MOD q]), w n) -
        (∑ n ∈ (Ioc L U).filter (fun n => (m * n).Coprime q), w n) / (q.totient : ℝ)) : ℂ) = _
    simp only [sum_filter, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_sum, apply_ite Complex.ofReal, Complex.ofReal_zero]
  · intro t ht hn
    exact hB t.1 (mem_product.mp ht).1 t.2 (mem_product.mp ht).2 hn

/-- The existing signed two-long error is exactly the complete-product
error of its coefficient mass. -/
theorem twoLongSignedError_eq_fibreError
    (S T A Q B : Finset ℕ) (a : ℕ) (α ρ : ℕ → ℂ) (w : ℕ → ℕ → ℂ)
    (hB : ∀ m ∈ A, ∀ x ∈ S, ∀ y ∈ T, α m * w x y ≠ 0 → m * x * y ∈ B) :
    twoLongProductSignedError S T A Q a α ρ w =
      finiteProductSignedError B Q a ρ (twoLongProductMass S T A α w) := by
  unfold twoLongProductMass
  rw [finiteProductSignedError_fibres]
  · unfold twoLongProductSignedError
    apply sum_congr rfl
    intro q _
    congr 1
    rw [Finset.sum_product]
    apply sum_congr rfl
    intro m _
    simp only [mul_assoc, ← mul_sum, sum_mul_finiteProductKernel, twoLongProductError,
      Finset.sum_product]
  · intro t ht hn
    obtain ⟨hm, hp⟩ := mem_product.mp ht
    obtain ⟨hx, hy⟩ := mem_product.mp hp
    exact hB t.1 hm t.2.1 hx t.2.2 hy hn

/-- A coefficient identity on a complete finite carrier transfers the
literal labelled prime error to a separated two-long chart. -/
theorem primeProductSignedError_eq_twoLong_of_mass
    (k P N : ℕ) (Q B S T A : Finset ℕ) (ρ : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (α : ℕ → ℂ) (w : ℕ → ℕ → ℂ)
    (hB : ∀ t ∈ labelledPrimeTuples k P, W t ≠ 0 → labelledProduct t ∈ B)
    (hLong : ∀ m ∈ A, ∀ x ∈ S, ∀ y ∈ T, α m * w x y ≠ 0 → m * x * y ∈ B)
    (hMass : ∀ b ∈ B, labelledPrimeProductMass k P W b = twoLongProductMass S T A α w b) :
    (primeProductSignedError k P N Q ρ W : ℂ) =
      twoLongProductSignedError S T A Q N α (fun q => (ρ q : ℂ)) w := by
  rw [primeProductSignedError_eq_fibreError _ _ _ _ _ _ _ hB,
    twoLongSignedError_eq_fibreError _ _ _ _ _ _ _ _ _ hLong]
  unfold finiteProductSignedError
  apply sum_congr rfl
  intro q _
  congr 1
  exact sum_congr rfl fun b hb => congrArg (fun c => c * finiteProductKernel q N b) (hMass b hb)

/-- The same coefficient-level transfer for a single long slot. -/
theorem primeProductSignedError_eq_oneLong_of_mass
    (k P N : ℕ) (Q B A : Finset ℕ) (L U : ℕ) (ρ : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (α : ℕ → ℂ) (w : ℕ → ℝ)
    (hB : ∀ t ∈ labelledPrimeTuples k P, W t ≠ 0 → labelledProduct t ∈ B)
    (hLong : ∀ m ∈ A, ∀ n ∈ Ioc L U, α m * (w n : ℂ) ≠ 0 → m * n ∈ B)
    (hMass : ∀ b ∈ B, labelledPrimeProductMass k P W b = oneLongProductMass A L U α w b) :
    (primeProductSignedError k P N Q ρ W : ℂ) =
      part3LongSlotWeightedSignedError A Q α (fun q => (ρ q : ℂ)) L U N w := by
  rw [primeProductSignedError_eq_fibreError _ _ _ _ _ _ _ hB,
    oneLongSignedError_eq_fibreError _ _ _ _ _ _ _ _ _ hLong]
  unfold finiteProductSignedError
  apply sum_congr rfl
  intro q _
  congr 1
  exact sum_congr rfl fun b hb => congrArg (fun c => c * finiteProductKernel q N b) (hMass b hb)

private theorem finiteProductSignedError_congr (B Q : Finset ℕ) (a : ℕ)
    (ρ c d : ℕ → ℂ) (h : ∀ b ∈ B, c b = d b) :
    finiteProductSignedError B Q a ρ c = finiteProductSignedError B Q a ρ d := by
  unfold finiteProductSignedError
  apply sum_congr rfl
  intro q _
  congr 1
  exact sum_congr rfl fun b hb => congrArg (fun z => z * finiteProductKernel q a b) (h b hb)

private theorem finiteProductSignedError_add (B Q : Finset ℕ) (a : ℕ)
    (ρ c d : ℕ → ℂ) :
    finiteProductSignedError B Q a ρ (fun b => c b + d b) =
      finiteProductSignedError B Q a ρ c + finiteProductSignedError B Q a ρ d := by
  simp only [finiteProductSignedError, add_mul, sum_add_distrib, mul_add]

private theorem finiteProductSignedError_mul (B Q : Finset ℕ) (a : ℕ)
    (ρ c : ℕ → ℂ) (s : ℂ) :
    finiteProductSignedError B Q a ρ (fun b => s * c b) =
      s * finiteProductSignedError B Q a ρ c := by
  unfold finiteProductSignedError
  rw [mul_sum]
  apply sum_congr rfl
  intro q _
  simp only [mul_assoc, ← mul_sum]
  ac_rfl

private theorem finiteProductSignedError_sum {I : Type*} (J : Finset I)
    (B Q : Finset ℕ) (a : ℕ) (ρ : ℕ → ℂ) (c : I → ℕ → ℂ) :
    finiteProductSignedError B Q a ρ (fun b => ∑ j ∈ J, c j b) =
      ∑ j ∈ J, finiteProductSignedError B Q a ρ (c j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [finiteProductSignedError]
  | @insert j J hJ ih =>
      simp only [sum_insert hJ, finiteProductSignedError_add, ih]

/-- A finite chart expansion of complete-product coefficients transfers
to the actual prime discrepancy. A coefficient residual contributes its
own signed error, including its coprime mean. -/
theorem primeProductSignedError_eq_sum_chartErrors {I : Type*} (J : Finset I)
    (k P N : ℕ) (Q B : Finset ℕ) (ρ : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (s : I → ℂ)
    (c : I → ℕ → ℂ) (e : ℕ → ℂ)
    (hB : ∀ t ∈ labelledPrimeTuples k P, W t ≠ 0 → labelledProduct t ∈ B)
    (hMass : ∀ b ∈ B, labelledPrimeProductMass k P W b = e b + ∑ j ∈ J, s j * c j b) :
    (primeProductSignedError k P N Q ρ W : ℂ) =
      finiteProductSignedError B Q N (fun q => (ρ q : ℂ)) e +
        ∑ j ∈ J, s j * finiteProductSignedError B Q N (fun q => (ρ q : ℂ)) (c j) := by
  rw [primeProductSignedError_eq_fibreError _ _ _ _ _ _ _ hB,
    finiteProductSignedError_congr _ _ _ _ _ _ hMass, finiteProductSignedError_add,
    finiteProductSignedError_sum]
  simp only [finiteProductSignedError_mul]

private theorem finiteProductKernel_norm_le (q a b : ℕ) :
    ‖finiteProductKernel q a b‖ ≤
      (if b ≡ a [MOD q] then (1 : ℝ) else 0) +
        (if b.Coprime q then (1 : ℝ) / q.totient else 0) := by
  unfold finiteProductKernel
  refine (norm_sub_le _ _).trans_eq ?_
  simp only [norm_div, Complex.norm_natCast]
  split_ifs <;> simp

/-- Exact coefficient errors can be estimated before expanding any
coprimality or residue condition. The genuine product equal to the
target remains in the progression count. -/
theorem finiteProductSignedError_norm_le_residual
    (B Q : Finset ℕ) (a : ℕ) (ρ e : ℕ → ℂ) :
    ‖finiteProductSignedError B Q a ρ e‖ ≤
      ∑ b ∈ B, ‖e b‖ * ∑ q ∈ Q, ‖ρ q‖ *
        ((if b ≡ a [MOD q] then (1 : ℝ) else 0) +
          (if b.Coprime q then (1 : ℝ) / q.totient else 0)) := by
  let C (q b : ℕ) : ℝ :=
    (if b ≡ a [MOD q] then 1 else 0) +
      (if b.Coprime q then (1 : ℝ) / q.totient else 0)
  unfold finiteProductSignedError
  calc
    _ ≤ ∑ q ∈ Q, ‖ρ q * ∑ b ∈ B, e b * finiteProductKernel q a b‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖ρ q‖ * ∑ b ∈ B, ‖e b‖ * C q b := by
      apply sum_le_sum
      intro q _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      refine (norm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (finiteProductKernel_norm_le q a b) (norm_nonneg _)
    _ = _ := by
      change _ = ∑ b ∈ B, ‖e b‖ * ∑ q ∈ Q, ‖ρ q‖ * C q b
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun b _ => sum_congr rfl fun q _ => by ring

/-- The existing smooth two-long estimate supplies a bound for the
actual labelled prime discrepancy on any outer chart whose coefficients
have the indicated separated product mass. -/
theorem primeProductSignedError_abs_le_smooth_twoLong_of_mass
    (k P N : ℕ) (Q B S T A : Finset ℕ) (R J : ℕ)
    (ρ : ℕ → ℝ) (W : (Fin k → Fin (P + 1)) → ℝ) (α : ℕ → ℂ)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hB : ∀ t ∈ labelledPrimeTuples k P, W t ≠ 0 → labelledProduct t ∈ B)
    (hLong : ∀ m ∈ A, ∀ x ∈ S, ∀ y ∈ T,
      α m * (F ((x : ℝ) / U) * G ((y : ℝ) / V)) ≠ 0 → m * x * y ∈ B)
    (hMass : ∀ b ∈ B, labelledPrimeProductMass k P W b =
      twoLongProductMass S T A α (fun x y => F ((x : ℝ) / U) * G ((y : ℝ) / V)) b)
    (hR : 1 ≤ R) (hQ : Q ⊆ Ioc 0 R) (hN : ∀ q ∈ Q, N.Coprime q)
    (hρ : ∀ q ∈ Q, |ρ q| ≤ (q.divisors.card : ℝ) ^ J)
    (hFneg : ∀ x : ℝ, x < 0 → F x = 0) (hGneg : ∀ x : ℝ, x < 0 → G x = 0)
    (hS : ∀ n : ℕ, F ((n : ℝ) / U) ≠ 0 → n ∈ S)
    (hT : ∀ n : ℕ, G ((n : ℝ) / V) ≠ 0 → n ∈ T)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖(𝓕 F) x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖(𝓕 G) x‖ ≤ D / (1 + |x|) ^ 2) :
    |primeProductSignedError k P N Q ρ W| ≤
      8 * C * D * (∑ m ∈ A, ‖α m‖) * ((R : ℝ) * Real.sqrt R) *
        (1 + Real.log R) ^ (2 ^ (J + 2) - 1) := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real,
    primeProductSignedError_eq_twoLong_of_mass k P N Q B S T A ρ W α _ hB hLong hMass]
  exact twoLongProductSignedError_smooth_norm_le S T A Q N R J α (fun q => (ρ q : ℂ))
    F G hU hV hR hQ hN (fun q hq => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ q hq)
    hFneg hGneg hS hT hC hD hF hG

end

end ImbalancedChen.Part3
