import ImbalancedChen.P5ActualAllRankOccurrenceFourierBridge
import ImbalancedChen.P5OriginalPrimeEndpointDivisors
import ImbalancedChen.DivisorMomentBudget
import ImbalancedChen.Part3ShiftedTauFiniteInterval

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual finite complete-modulus Fourier-tail accounting. The q=1 row is
cancelled exactly before taking absolute values. Products b=T are isolated
before divisor counting, so tau(0) is never evaluated by a moment bound.
All tuple labels and repeated complete products keep their absolute fibre
multiplicity. Count and exact coprime mean retain the same physical rho.
-/
namespace ImbalancedChen.P5Z.ActualCompleteModulusFourierTail
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open P5OriginalPrimeEndpoint
open AllRankCoordinateFourierIBP AllRankMixedOperatorBudget
open AdmissibleAllRankIntegerGeometricFamily
open ActualEuclideanPhysicalFourier ActualAllRankOccurrenceFourierBridge

abbrev tau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

def effectiveModuli (Q : Finset ℕ) : Finset ℕ := Q.erase 1

theorem residueKernel_one (T b : ℕ) :
    MellinInsertion20261028.residueKernel 1 T b = 0 := by
  simp [MellinInsertion20261028.residueKernel]

/-- The exact q=1 count and mean cancel before every norm or envelope. -/
theorem discrepancy_erase_one {ι : Type*} (s : Finset ι) (Q : Finset ℕ)
    (rho : ℕ → ℂ) (product : ι → ℕ) (T : ℕ) (w : ι → ℂ) :
    MellinInsertion20261028.exactDiscrepancy s Q rho product T w =
      MellinInsertion20261028.exactDiscrepancy s (effectiveModuli Q) rho product T w := by
  unfold MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  symm
  by_cases h1 : 1 ∈ Q
  · have h := Finset.sum_erase_add Q
      (fun q => rho q * MellinInsertion20261028.residueKernel q T (product i)) h1
    simpa only [residueKernel_one, mul_zero, add_zero] using h
  · simp only [effectiveModuli, Finset.erase_eq_of_not_mem h1]

def rhoMass (Q : Finset ℕ) (rho : ℕ → ℂ) : ℝ := ∑ q ∈ effectiveModuli Q, ‖rho q‖

def rhoMeanMass (Q : Finset ℕ) (rho : ℕ → ℂ) : ℝ :=
  ∑ q ∈ effectiveModuli Q, ‖rho q‖ / (q.totient : ℝ)

def residueMass (Q : Finset ℕ) (rho : ℕ → ℂ) (T b : ℕ) : ℝ :=
  ∑ q ∈ effectiveModuli Q with Nat.ModEq q b T, ‖rho q‖

theorem rhoMass_nonneg (Q : Finset ℕ) (rho : ℕ → ℂ) : 0 ≤ rhoMass Q rho :=
  Finset.sum_nonneg (fun q hq => norm_nonneg _)

theorem rhoMeanMass_nonneg (Q : Finset ℕ) (rho : ℕ → ℂ) : 0 ≤ rhoMeanMass Q rho :=
  Finset.sum_nonneg (fun q hq => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

theorem residueMass_nonneg (Q : Finset ℕ) (rho : ℕ → ℂ) (T b : ℕ) :
    0 ≤ residueMass Q rho T b := Finset.sum_nonneg (fun q hq => norm_nonneg _)

@[simp] theorem residueMass_exact (Q : Finset ℕ) (rho : ℕ → ℂ) (T : ℕ) :
    residueMass Q rho T T = rhoMass Q rho := by
  simp only [residueMass, rhoMass, Nat.ModEq.refl, Finset.filter_true_of_mem]

theorem tau_divisor_le {d q : ℕ} (hd : d ≠ 0) (hq : q ∣ d) : tau q ≤ tau d := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro u hu
  exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hu).1.trans hq, hd⟩

/-- Collapse the full actual modulus sum at a NONZERO complete product
before applying any Fourier error. This never substitutes a quotient
product and never uses divisors of zero. -/
theorem residueMass_nonzero_le (Q : Finset ℕ) (rho : ℕ → ℂ) (T b : ℕ)
    (hb : b ≠ T) (Cρ : ℝ) (J : ℕ) (hCρ : 0 ≤ Cρ)
    (hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J) :
    residueMass Q rho T b ≤ Cρ * tau (distance T b) ^ (J + 1) := by
  have hd : distance T b ≠ 0 := (distance_pos hb).ne'
  have hsub : (effectiveModuli Q).filter (fun q => Nat.ModEq q b T) ⊆
      (distance T b).divisors := by
    intro q hq
    exact Nat.mem_divisors.mpr ⟨(modEq_iff_dvd_distance T b q).mp
      (Finset.mem_filter.mp hq).2, hd⟩
  calc
    residueMass Q rho T b ≤ ∑ q ∈ effectiveModuli Q with Nat.ModEq q b T,
        Cρ * tau q ^ J :=
      Finset.sum_le_sum (fun q hq => hrho q (Finset.mem_filter.mp hq).1)
    _ = Cρ * ∑ q ∈ effectiveModuli Q with Nat.ModEq q b T, tau q ^ J := by
      rw [Finset.mul_sum]
    _ ≤ Cρ * ∑ q ∈ (distance T b).divisors, tau q ^ J := by
      apply mul_le_mul_of_nonneg_left _ hCρ
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq hnot => by positivity)
    _ ≤ Cρ * ∑ q ∈ (distance T b).divisors, tau (distance T b) ^ J := by
      apply mul_le_mul_of_nonneg_left _ hCρ
      apply Finset.sum_le_sum
      intro q hq
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (tau_divisor_le hd (Nat.mem_divisors.mp hq).1) J
    _ = Cρ * tau (distance T b) ^ (J + 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul, tau]
      rw [pow_succ]
      ring

theorem residueKernel_norm_le (q T b : ℕ) :
    ‖MellinInsertion20261028.residueKernel q T b‖ ≤
      (if Nat.ModEq q b T then (1 : ℝ) else 0) +
        (if Nat.Coprime b q then (1 : ℝ) else 0) / (q.totient : ℝ) := by
  have h := norm_sub_le
    (if b % q = T % q then (1 : ℂ) else 0)
    ((if Nat.Coprime b q then (1 : ℂ) else 0) / (q.totient : ℂ))
  have hcount : ‖(if b % q = T % q then (1 : ℂ) else 0)‖ =
      if Nat.ModEq q b T then (1 : ℝ) else 0 := by
    by_cases hmod : b % q = T % q <;> simp [hmod, Nat.ModEq]
  have hmean : ‖(if Nat.Coprime b q then (1 : ℂ) else 0)‖ =
      if Nat.Coprime b q then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  simpa only [MellinInsertion20261028.residueKernel, norm_div, hcount, hmean,
    Complex.norm_natCast] using h

/-- The exact mean is bounded only by its reciprocal-totient mass; no
factor equal to the modulus support cap is charged to this half. -/
theorem signed_row_norm_le (Q : Finset ℕ) (rho : ℕ → ℂ) (T b : ℕ) :
    ‖∑ q ∈ effectiveModuli Q, rho q *
      MellinInsertion20261028.residueKernel q T b‖ ≤
      residueMass Q rho T b + rhoMeanMass Q rho := by
  calc
    ‖∑ q ∈ effectiveModuli Q, rho q *
        MellinInsertion20261028.residueKernel q T b‖ ≤
      ∑ q ∈ effectiveModuli Q, ‖rho q‖ *
        ‖MellinInsertion20261028.residueKernel q T b‖ := by
      simpa only [norm_mul] using norm_sum_le
        (effectiveModuli Q) (fun q => rho q * MellinInsertion20261028.residueKernel q T b)
    _ ≤ ∑ q ∈ effectiveModuli Q, ‖rho q‖ *
      ((if Nat.ModEq q b T then (1 : ℝ) else 0) + 1 / (q.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (residueKernel_norm_le q T b).trans
      apply add_le_add_left
      exact div_le_div_of_nonneg_right (by split_ifs <;> norm_num) (Nat.cast_nonneg _)
    _ = residueMass Q rho T b + rhoMeanMass Q rho := by
      simp only [mul_add, Finset.sum_add_distrib, residueMass, rhoMeanMass,
        Finset.sum_filter, mul_one, mul_zero, mul_div_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> simp

def fibreMass {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (product : ι → ℕ) (b : ℕ) : ℝ := ∑ i ∈ s with product i = b, ‖β i‖

def tupleMass {ι : Type*} (s : Finset ι) (β : ι → ℂ) : ℝ := ∑ i ∈ s, ‖β i‖

def nonzeroMoment {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (product : ι → ℕ) (T S : ℕ) : ℝ :=
  ∑ i ∈ s with product i ≠ T, ‖β i‖ * tau (distance T (product i)) ^ S

/-- The factorization-fibre sum retains all labels even when different
ordered tuples produce the same complete integer. No injectivity of
product, no sorting and no duplicate deletion is assumed. -/
theorem nonzeroMoment_eq_fibres {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (product : ι → ℕ) (T S : ℕ) :
    nonzeroMoment s β product T S =
      ∑ b ∈ s.image product with b ≠ T,
        fibreMass s β product b * tau (distance T b) ^ S := by
  let s₀ := s.filter (fun i => product i ≠ T)
  let B := (s.image product).filter (fun b => b ≠ T)
  have hmap : ∀ i ∈ s₀, product i ∈ B := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem product (Finset.mem_filter.mp hi).1,
      (Finset.mem_filter.mp hi).2⟩
  have hf := Finset.sum_fiberwise_of_maps_to (s := s₀) (t := B) (g := product) hmap
    (fun i => ‖β i‖ * tau (distance T (product i)) ^ S)
  change (∑ i ∈ s₀, ‖β i‖ * tau (distance T (product i)) ^ S) = _
  rw [← hf]
  apply Finset.sum_congr rfl
  intro b hb
  have hbne := (Finset.mem_filter.mp hb).2
  have hfilter : s₀.filter (fun i => product i = b) = s.filter (fun i => product i = b) := by
    ext i
    simp only [s₀, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, by simpa [h.2] using hbne⟩, h.2⟩
  calc
    (∑ i ∈ s₀ with product i = b, ‖β i‖ * tau (distance T (product i)) ^ S) =
      ∑ i ∈ s₀ with product i = b, ‖β i‖ * tau (distance T b) ^ S := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = fibreMass s β product b * tau (distance T b) ^ S := by
      rw [hfilter, ← Finset.sum_mul]
      rfl

def fullTailMass {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (product : ι → ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (T J : ℕ) (Cρ : ℝ) : ℝ :=
  Cρ * nonzeroMoment s β product T (J + 1) +
    fibreMass s β product T * rhoMass Q rho + tupleMass s β * rhoMeanMass Q rho

/-- Complete-modulus accounting, BEFORE the Fourier error is inserted. -/
theorem tuple_kernel_mass_le {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (product : ι → ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) (T J : ℕ)
    (Cρ : ℝ) (hCρ : 0 ≤ Cρ)
    (hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J) :
    (∑ i ∈ s, ‖β i‖ * (residueMass Q rho T (product i) + rhoMeanMass Q rho)) ≤
      fullTailMass s β product Q rho T J Cρ := by
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => product i = T)
    (fun i => ‖β i‖ * residueMass Q rho T (product i))
  have hexact : (∑ i ∈ s with product i = T,
      ‖β i‖ * residueMass Q rho T (product i)) = fibreMass s β product T * rhoMass Q rho := by
    unfold fibreMass
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2, residueMass_exact]
  have hnonzero : (∑ i ∈ s with product i ≠ T,
      ‖β i‖ * residueMass Q rho T (product i)) ≤
      Cρ * nonzeroMoment s β product T (J + 1) := by
    unfold nonzeroMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left
      (residueMass_nonzero_le Q rho T (product i) (Finset.mem_filter.mp hi).2 Cρ J hCρ hrho)
      (norm_nonneg (β i))
    simpa only [mul_left_comm] using h
  have hmean : (∑ i ∈ s, ‖β i‖ * rhoMeanMass Q rho) =
      tupleMass s β * rhoMeanMass Q rho := by rw [← Finset.sum_mul]; rfl
  rw [show (fun i => ‖β i‖ * (residueMass Q rho T (product i) + rhoMeanMass Q rho)) =
    fun i => ‖β i‖ * residueMass Q rho T (product i) + ‖β i‖ * rhoMeanMass Q rho
    from funext (fun i => mul_add _ _ _), Finset.sum_add_distrib, hmean]
  unfold fullTailMass
  rw [← hsplit, hexact]
  linarith

/-- A Fourier truncation error is charged only AFTER the preceding
complete modulus and exact-mean bound. The arithmetic functional on both
sides is the original same-rho one. -/
theorem discrepancy_tail_le {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (product : ι → ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) (T J : ℕ)
    (Cρ δ : ℝ) (hCρ : 0 ≤ Cρ) (hδ : 0 ≤ δ)
    (hrho : ∀ q ∈ effectiveModuli Q, ‖rho q‖ ≤ Cρ * tau q ^ J)
    (w v : ι → ℂ) (herr : ∀ i ∈ s, ‖w i - v i‖ ≤ δ) :
    ‖MellinInsertion20261028.exactDiscrepancy s Q rho product T (fun i => β i * w i) -
      MellinInsertion20261028.exactDiscrepancy s Q rho product T (fun i => β i * v i)‖ ≤
      δ * fullTailMass s β product Q rho T J Cρ := by
  rw [discrepancy_erase_one, discrepancy_erase_one s Q]
  let c : ι → ℂ := fun i => ∑ q ∈ effectiveModuli Q,
    rho q * MellinInsertion20261028.residueKernel q T (product i)
  have heq :
      MellinInsertion20261028.exactDiscrepancy s (effectiveModuli Q) rho product T (fun i => β i*w i) -
      MellinInsertion20261028.exactDiscrepancy s (effectiveModuli Q) rho product T (fun i => β i*v i) =
        ∑ i ∈ s, β i * (w i-v i) * c i := by
    unfold MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    ‖∑ i ∈ s, β i * (w i-v i) * c i‖ ≤
      ∑ i ∈ s, ‖β i‖ * ‖w i-v i‖ * ‖c i‖ := by
      simpa only [norm_mul] using norm_sum_le s (fun i => β i*(w i-v i)*c i)
    _ ≤ ∑ i ∈ s, δ * (‖β i‖ *
        (residueMass Q rho T (product i) + rhoMeanMass Q rho)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hrow := signed_row_norm_le Q rho T (product i)
      change ‖c i‖ ≤ residueMass Q rho T (product i) + rhoMeanMass Q rho at hrow
      have hh := mul_le_mul (herr i hi) hrow (norm_nonneg _) hδ
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hh (norm_nonneg (β i))
    _ = δ * ∑ i ∈ s, ‖β i‖ *
        (residueMass Q rho T (product i) + rhoMeanMass Q rho) := by rw [Finset.mul_sum]
    _ ≤ δ * fullTailMass s β product Q rho T J Cρ :=
      mul_le_mul_of_nonneg_left (tuple_kernel_mass_le s β product Q rho T J Cρ hCρ hrho) hδ

end
end ImbalancedChen.P5Z.ActualCompleteModulusFourierTail
