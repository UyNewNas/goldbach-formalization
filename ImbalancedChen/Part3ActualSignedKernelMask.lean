import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.ActualUpperCountingInputs
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / NOT ACCEPTED -- 20261024z P3, continuation 2.
All three original factorCarrier ranges and the signed residue in the
congruence remain literal. A product-modulus mask stays inside their sum;
it is not asserted to factor into three independent gamma coefficients.
The single-factor mask below is represented by an actual MediumAtom record
update. No preservation of MediumAdmissible is asserted. The prime-product
bridge updates the actual rho function parameter, not a nonexistent field.
No desired distribution estimate is assumed or provided.
-/

namespace ImbalancedChen.Part3.ActualSignedKernelMask_20261024z
noncomputable section
open Classical
open scoped BigOperators

/-- A complex mask shared at the same physical product modulus. -/
def signedKernelMask (d : MediumAtom) (mask : ℕ → ℂ) : ℂ :=
  ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
    ∑ q3 ∈ factorCarrier d.Q3,
      d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 * mask (q1*q2*q3) *
        d.discrepancy (q1*q2*q3)

theorem signedKernelMask_one (d : MediumAtom) :
    signedKernelMask d (fun _ => 1) = d.signedError := by
  simp only [signedKernelMask, MediumAtom.signedError, mul_one]

theorem signedKernelMask_add (d : MediumAtom) (mask eta : ℕ → ℂ) :
    signedKernelMask d (fun q => mask q + eta q) =
      signedKernelMask d mask + signedKernelMask d eta := by
  simp only [signedKernelMask, mul_add, add_mul, Finset.sum_add_distrib]

theorem signedKernelMask_sub (d : MediumAtom) (mask eta : ℕ → ℂ) :
    signedKernelMask d (fun q => mask q - eta q) =
      signedKernelMask d mask - signedKernelMask d eta := by
  simp only [signedKernelMask, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- Exact complement on the SAME original factor carriers. -/
theorem signedError_eq_mask_add_complement (d : MediumAtom) (mask : ℕ → ℂ) :
    d.signedError = signedKernelMask d mask +
      signedKernelMask d (fun q => 1-mask q) := by
  have h := signedKernelMask_add d mask (fun q => 1-mask q)
  have hf : (fun q => mask q + (1-mask q)) = (fun _ : ℕ => (1 : ℂ)) := by
    funext q
    ring
  rw [hf, signedKernelMask_one] at h
  exact h

theorem signedError_norm_le_mask_add_complement (d : MediumAtom) (mask : ℕ → ℂ) :
    ‖d.signedError‖ ≤ ‖signedKernelMask d mask‖ +
      ‖signedKernelMask d (fun q => 1-mask q)‖ := by
  rw [signedError_eq_mask_add_complement d mask]
  exact norm_add_le _ _

theorem signedError_sub_mask_eq_complement (d : MediumAtom) (mask : ℕ → ℂ) :
    d.signedError - signedKernelMask d mask =
      signedKernelMask d (fun q => 1-mask q) := by
  rw [signedError_eq_mask_add_complement d mask]
  ring

/-- Only triangle inequalities are used; signs stay inside each block. -/
theorem signedKernelMask_norm_le_finite (d : MediumAtom) (mask : ℕ → ℂ) :
    ‖signedKernelMask d mask‖ ≤
      ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
        ∑ q3 ∈ factorCarrier d.Q3,
          ‖d.gamma1 q1‖ * ‖d.gamma2 q2‖ * ‖d.gamma3 q3‖ *
            ‖mask (q1*q2*q3)‖ * ‖d.discrepancy (q1*q2*q3)‖ := by
  unfold signedKernelMask
  calc
    _ ≤ ∑ q1 ∈ factorCarrier d.Q1,
        ‖∑ q2 ∈ factorCarrier d.Q2, ∑ q3 ∈ factorCarrier d.Q3,
          d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 * mask (q1*q2*q3) *
            d.discrepancy (q1*q2*q3)‖ := norm_sum_le _ _
    _ ≤ ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
        ‖∑ q3 ∈ factorCarrier d.Q3,
          d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 * mask (q1*q2*q3) *
            d.discrepancy (q1*q2*q3)‖ := by
      apply Finset.sum_le_sum
      intro q1 _hq1
      exact norm_sum_le _ _
    _ ≤ ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
        ∑ q3 ∈ factorCarrier d.Q3,
          ‖d.gamma1 q1‖ * ‖d.gamma2 q2‖ * ‖d.gamma3 q3‖ *
            ‖mask (q1*q2*q3)‖ * ‖d.discrepancy (q1*q2*q3)‖ := by
      apply Finset.sum_le_sum
      intro q1 _hq1
      apply Finset.sum_le_sum
      intro q2 _hq2
      simpa only [norm_mul] using norm_sum_le (factorCarrier d.Q3)
        (fun q3 => d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 * mask (q1*q2*q3) *
          d.discrepancy (q1*q2*q3))

/-- Exact difference of two masks followed by its finite error budget. -/
theorem signedKernelMask_sub_norm_le (d : MediumAtom) (mask eta : ℕ → ℂ) :
    ‖signedKernelMask d mask - signedKernelMask d eta‖ ≤
      ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
        ∑ q3 ∈ factorCarrier d.Q3,
          ‖d.gamma1 q1‖ * ‖d.gamma2 q2‖ * ‖d.gamma3 q3‖ *
            ‖mask (q1*q2*q3)-eta (q1*q2*q3)‖ *
              ‖d.discrepancy (q1*q2*q3)‖ := by
  rw [← signedKernelMask_sub]
  exact signedKernelMask_norm_le_finite d (fun q => mask q-eta q)

/-- Real masks are cast into the very same complex signed sum. -/
theorem signedError_eq_realMask_add_complement (d : MediumAtom) (mask : ℕ → ℝ) :
    d.signedError = signedKernelMask d (fun q => (mask q : ℂ)) +
      signedKernelMask d (fun q => ((1-mask q : ℝ) : ℂ)) := by
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
    signedError_eq_mask_add_complement d (fun q => (mask q : ℂ))

theorem signedKernelMask_indicator_eq_filter (d : MediumAtom) (M : Finset ℕ) :
    signedKernelMask d ((M : Set ℕ).indicator (fun _ => (1 : ℂ))) =
      ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
        ∑ q3 ∈ (factorCarrier d.Q3).filter (fun q3 => q1*q2*q3 ∈ M),
          d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 * d.discrepancy (q1*q2*q3) := by
  unfold signedKernelMask
  apply Finset.sum_congr rfl
  intro q1 _hq1
  apply Finset.sum_congr rfl
  intro q2 _hq2
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q3 _hq3
  by_cases hm : q1*q2*q3 ∈ M <;> simp [hm]

/-- An actual record update for masks on the first factor only. -/
def withGamma1Mask (d : MediumAtom) (mask : ℕ → ℂ) : MediumAtom :=
  { d with gamma1 := fun q => d.gamma1 q * mask q }

theorem withGamma1Mask_original_data (d : MediumAtom) (mask : ℕ → ℂ) :
    (withGamma1Mask d mask).residue = d.residue ∧
      (withGamma1Mask d mask).alpha = d.alpha ∧
      (withGamma1Mask d mask).beta = d.beta ∧
      (withGamma1Mask d mask).alphaCarrier = d.alphaCarrier ∧
      (withGamma1Mask d mask).betaCarrier = d.betaCarrier ∧
      (withGamma1Mask d mask).Q1 = d.Q1 ∧
      (withGamma1Mask d mask).Q2 = d.Q2 ∧
      (withGamma1Mask d mask).Q3 = d.Q3 ∧
      (withGamma1Mask d mask).scale = d.scale := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem withGamma1Mask_other_fields (d : MediumAtom) (mask : ℕ → ℂ) :
    (withGamma1Mask d mask).gamma2 = d.gamma2 ∧
      (withGamma1Mask d mask).gamma3 = d.gamma3 ∧
      (withGamma1Mask d mask).U = d.U ∧
      (withGamma1Mask d mask).V = d.V ∧
      (withGamma1Mask d mask).intervalLo = d.intervalLo ∧
      (withGamma1Mask d mask).intervalHi = d.intervalHi := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem withGamma1Mask_discrepancy (d : MediumAtom) (mask : ℕ → ℂ) (q : ℕ) :
    (withGamma1Mask d mask).discrepancy q = d.discrepancy q := by
  rfl

theorem withGamma1Mask_signedError_eq (d : MediumAtom) (mask : ℕ → ℂ) :
    (withGamma1Mask d mask).signedError =
      ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
        ∑ q3 ∈ factorCarrier d.Q3,
          d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 * mask q1 *
            d.discrepancy (q1*q2*q3) := by
  unfold MediumAtom.signedError
  apply Finset.sum_congr rfl
  intro q1 _hq1
  apply Finset.sum_congr rfl
  intro q2 _hq2
  apply Finset.sum_congr rfl
  intro q3 _hq3
  change (d.gamma1 q1 * mask q1) * d.gamma2 q2 * d.gamma3 q3 *
    d.discrepancy (q1*q2*q3) = _
  ring

theorem signedError_eq_gamma1Mask_add_complement (d : MediumAtom) (mask : ℕ → ℂ) :
    d.signedError = (withGamma1Mask d mask).signedError +
      (withGamma1Mask d (fun q => 1-mask q)).signedError := by
  rw [withGamma1Mask_signedError_eq, withGamma1Mask_signedError_eq]
  simp only [MediumAtom.signedError, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q1 _hq1
  apply Finset.sum_congr rfl
  intro q2 _hq2
  apply Finset.sum_congr rfl
  intro q3 _hq3
  ring

theorem withGamma1Mask_indicator_signedError (d : MediumAtom) (M : Finset ℕ) :
    (withGamma1Mask d ((M : Set ℕ).indicator (fun _ => (1 : ℂ)))).signedError =
      ∑ q1 ∈ (factorCarrier d.Q1).filter (fun q1 => q1 ∈ M),
        ∑ q2 ∈ factorCarrier d.Q2, ∑ q3 ∈ factorCarrier d.Q3,
          d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 * d.discrepancy (q1*q2*q3) := by
  rw [withGamma1Mask_signedError_eq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q1 _hq1
  by_cases hm : q1 ∈ M <;> simp [hm]

/-- The literal inner prime-product discrepancy, including both filters. -/
def primeProductKernel (k P N : ℕ)
    (W : (Fin k → Fin (P+1)) → ℝ) (q : ℕ) : ℝ :=
  ∑ t ∈ labelledPrimeTuples k P, W t *
    ((if Nat.ModEq q (labelledProduct t) N then (1 : ℝ) else 0) -
      (if Nat.Coprime (labelledProduct t) q then (1 : ℝ) else 0) /
        (Nat.totient q : ℝ))

theorem primeProductSignedError_eq_kernel (k P N : ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (W : (Fin k → Fin (P+1)) → ℝ) :
    primeProductSignedError k P N Q rho W =
      ∑ q ∈ Q, rho q * primeProductKernel k P N W q := by
  rfl

/-- The genuine rho update retains all labelled tuples and W verbatim. -/
theorem primeProductSignedError_masked_rho (k P N : ℕ) (Q : Finset ℕ)
    (rho mask : ℕ → ℝ) (W : (Fin k → Fin (P+1)) → ℝ) :
    primeProductSignedError k P N Q (fun q => rho q * mask q) W =
      ∑ q ∈ Q, rho q * mask q * primeProductKernel k P N W q := by
  rfl

theorem primeProductSignedError_mask_split (k P N : ℕ) (Q : Finset ℕ)
    (rho mask : ℕ → ℝ) (W : (Fin k → Fin (P+1)) → ℝ) :
    primeProductSignedError k P N Q rho W =
      primeProductSignedError k P N Q (fun q => rho q * mask q) W +
        primeProductSignedError k P N Q (fun q => rho q * (1-mask q)) W := by
  simp only [primeProductSignedError_eq_kernel, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  ring

theorem primeProductSignedError_abs_le_mask_blocks (k P N : ℕ) (Q : Finset ℕ)
    (rho mask : ℕ → ℝ) (W : (Fin k → Fin (P+1)) → ℝ) :
    |primeProductSignedError k P N Q rho W| ≤
      |primeProductSignedError k P N Q (fun q => rho q * mask q) W| +
        |primeProductSignedError k P N Q (fun q => rho q * (1-mask q)) W| := by
  rw [primeProductSignedError_mask_split k P N Q rho mask W]
  exact abs_add_le _ _

theorem primeProductSignedError_indicator_rho_eq_filter (k P N : ℕ)
    (Q M : Finset ℕ) (rho : ℕ → ℝ) (W : (Fin k → Fin (P+1)) → ℝ) :
    primeProductSignedError k P N Q ((M : Set ℕ).indicator rho) W =
      primeProductSignedError k P N (Q.filter (fun q => q ∈ M)) rho W := by
  simp only [primeProductSignedError_eq_kernel, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hm : q ∈ M <;> simp [hm]

/-- A finite replacement error with the full original signed kernel. -/
theorem primeProductSignedError_sub_abs_le_finite (k P N : ℕ) (Q : Finset ℕ)
    (rho eta : ℕ → ℝ) (W : (Fin k → Fin (P+1)) → ℝ) :
    |primeProductSignedError k P N Q rho W - primeProductSignedError k P N Q eta W| ≤
      ∑ q ∈ Q, |rho q-eta q| * |primeProductKernel k P N W q| := by
  have heq : primeProductSignedError k P N Q rho W -
      primeProductSignedError k P N Q eta W =
        ∑ q ∈ Q, (rho q-eta q) * primeProductKernel k P N W q := by
    simp only [primeProductSignedError_eq_kernel, sub_mul, Finset.sum_sub_distrib]
  rw [heq]
  simpa only [Real.norm_eq_abs, abs_mul] using
    norm_sum_le Q (fun q => (rho q-eta q) * primeProductKernel k P N W q)

/-- Same-source primitive splitting in the exact P4B consumer's kernel. -/
theorem finitePrimitive_mask_split (N : ℕ) (S Q : Finset ℕ)
    (weight rho mask : ℕ → ℝ) :
    (∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy S weight N q) =
      (∑ q ∈ Q, (rho q * mask q) * finitePrimitiveDiscrepancy S weight N q) +
        ∑ q ∈ Q, (rho q * (1-mask q)) * finitePrimitiveDiscrepancy S weight N q := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  ring

/-- The actual attached coefficient and carrier appear in both blocks.
This is a finite triangle bound, with no primitive estimate hypothesis. -/
theorem attachedUpperPrimitive_abs_le_mask_blocks (N : ℕ)
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (S : Finset ℕ) (weight mask : ℕ → ℝ) :
    |∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N q *
        finitePrimitiveDiscrepancy S weight N q| ≤
      |∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
        (attachedUpperCoefficient nu r epsilon retain cap N q * mask q) *
          finitePrimitiveDiscrepancy S weight N q| +
        |∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
          (attachedUpperCoefficient nu r epsilon retain cap N q * (1-mask q)) *
            finitePrimitiveDiscrepancy S weight N q| := by
  rw [finitePrimitive_mask_split N S
    (attachedUpperModuli nu r epsilon retain cap N) weight
    (attachedUpperCoefficient nu r epsilon retain cap N) mask]
  exact abs_add_le _ _

end
end ImbalancedChen.Part3.ActualSignedKernelMask_20261024z
