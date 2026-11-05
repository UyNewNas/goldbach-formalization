import ImbalancedChen.P3PhysicalOriginalWInsertion

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

The previous W/HB packet supplies a concrete geometric derivative L1 bound.
The manuscript's (F) Fourier cutoff must then be charged AFTER the complete
signed modulus sum. This file proves the FINITE, EXACT error transport for
any two weights on the SAME retained source, using the actual congruence
minus exact coprime mean kernel, not a fabricated averaged kernel.

The geometric approximation is a visible pointwise input, NOT a PP
discrepancy estimate and NOT a claim that Fourier (F) has been proved.
The Fourier construction and its 2*pi normalization remain open.
No shifted-divisor moment, arithmetic tail, or prime distribution lemma
is implemented here. There is no tau(0): b=T is split explicitly.
-/

namespace ImbalancedChen.P3FullSignedModulusTail
noncomputable section
open scoped Classical BigOperators
open P3PhysicalOriginalWInsertion

/-- The two NONNEGATIVE terms of the original PP kernel. This is a
majorant of the actual arithmetic test, not a new testing condition. -/
def kernelMass {g : ℕ} (T q : ℕ) (p : Fin g → ℕ) : ℝ :=
  (if (∏ j, p j) % q = T % q then 1 else 0) +
    (if Nat.Coprime (∏ j, p j) q then (Nat.totient q : ℝ)⁻¹ else 0)

theorem kernelMass_nonneg {g : ℕ} (T q : ℕ) (p : Fin g → ℕ) :
    0 ≤ kernelMass T q p := by
  unfold kernelMass
  apply add_nonneg
  · split_ifs <;> norm_num
  · split_ifs <;> positivity

/-- No use of phi(q) as a surrogate for an unrestricted count.
In applications q>0 and (q,T)=1; the finite statement also handles
the totalized values for q=0 without taking their reciprocals outside
the already defined kernel. -/
theorem abs_exactCoprimeTest_le {g : ℕ} (T q : ℕ) (p : Fin g → ℕ) :
    |exactCoprimeTest T q p| ≤ kernelMass T q p := by
  let c : ℝ := if (∏ j, p j) % q = T % q then 1 else 0
  let a : ℝ := if Nat.Coprime (∏ j, p j) q
    then (Nat.totient q : ℝ)⁻¹ else 0
  have hc : 0 ≤ c := by dsimp [c]; split_ifs <;> norm_num
  have ha : 0 ≤ a := by dsimp [a]; split_ifs <;> positivity
  change |c - a| ≤ c + a
  calc
    |c - a| = |c + -a| := by rw [sub_eq_add_neg]
    _ ≤ |c| + |-a| := abs_add _ _
    _ = c + a := by rw [abs_of_nonneg hc, abs_neg, abs_of_nonneg ha]

/-- The SAME rho is outside both the counting and coprime-mean terms.
The source is a previously admitted finite tuple source: this definition
does not license arbitrary arithmetic filters or a new mother word. -/
def signedSource {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι)
    (rho : ℕ → ℝ) (coefficient weight : ι → ℝ)
    (T : ℕ) (originalProducts : ι → Fin g → ℕ) : ℝ :=
  ∑ q ∈ Q, rho q * ∑ t ∈ source,
    coefficient t * weight t * exactCoprimeTest T q (originalProducts t)

/-- This is the MASS that pays a uniform weight approximation after
the FULL modulus sum. No sparse-fiber relative error is imposed. -/
def fullModulusMass {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι)
    (rho : ℕ → ℝ) (coefficient : ι → ℝ)
    (T : ℕ) (originalProducts : ι → Fin g → ℕ) : ℝ :=
  ∑ q ∈ Q, |rho q| * ∑ t ∈ source,
    |coefficient t| * kernelMass T q (originalProducts t)

theorem signedSource_sub {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι)
    (rho : ℕ → ℝ) (coefficient w v : ι → ℝ)
    (T : ℕ) (originalProducts : ι → Fin g → ℕ) :
    signedSource Q source rho coefficient w T originalProducts -
      signedSource Q source rho coefficient v T originalProducts =
    signedSource Q source rho coefficient (fun t => w t - v t) T originalProducts := by
  unfold signedSource
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Genuine finite signed error propagation. This is a lemma about
approximation of geometric weights, not an assumed distribution bound.
It is deliberately BEFORE any divisor-moment estimate. -/
theorem signedSource_approximation {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι)
    (rho : ℕ → ℝ) (coefficient w v : ι → ℝ)
    (T : ℕ) (originalProducts : ι → Fin g → ℕ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (happrox : ∀ t ∈ source, |w t - v t| ≤ eps) :
    |signedSource Q source rho coefficient w T originalProducts -
      signedSource Q source rho coefficient v T originalProducts| ≤
      eps * fullModulusMass Q source rho coefficient T originalProducts := by
  have hinner (q : ℕ) :
      |∑ t ∈ source, coefficient t * (w t - v t) *
          exactCoprimeTest T q (originalProducts t)| ≤
        eps * (∑ t ∈ source,
          |coefficient t| * kernelMass T q (originalProducts t)) := by
    calc
      _ ≤ ∑ t ∈ source,
          |coefficient t * (w t - v t) *
            exactCoprimeTest T q (originalProducts t)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ source,
          eps * (|coefficient t| * kernelMass T q (originalProducts t)) := by
          apply Finset.sum_le_sum
          intro t ht
          calc
            _ = |coefficient t| * |w t - v t| *
                  |exactCoprimeTest T q (originalProducts t)| := by
                    rw [abs_mul, abs_mul]
            _ ≤ |coefficient t| * eps *
                  |exactCoprimeTest T q (originalProducts t)| := by
                    apply mul_le_mul_of_nonneg_right
                    · exact mul_le_mul_of_nonneg_left (happrox t ht) (abs_nonneg _)
                    · exact abs_nonneg _
            _ ≤ |coefficient t| * eps *
                  kernelMass T q (originalProducts t) := by
                    exact mul_le_mul_of_nonneg_left
                      (abs_exactCoprimeTest_le T q (originalProducts t))
                      (mul_nonneg (abs_nonneg _) heps)
            _ = eps * (|coefficient t| *
                  kernelMass T q (originalProducts t)) := by ring
      _ = eps * (∑ t ∈ source,
          |coefficient t| * kernelMass T q (originalProducts t)) := by
          rw [Finset.mul_sum]
  rw [signedSource_sub]
  unfold signedSource
  calc
    _ ≤ ∑ q ∈ Q, |rho q * (∑ t ∈ source,
        coefficient t * (w t - v t) *
          exactCoprimeTest T q (originalProducts t))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Q, |rho q| * (eps * (∑ t ∈ source,
          |coefficient t| * kernelMass T q (originalProducts t))) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hinner q) (abs_nonneg _)
    _ = eps * fullModulusMass Q source rho coefficient T originalProducts := by
          unfold fullModulusMass
          calc
            _ = ∑ q ∈ Q, eps * (|rho q| *
                (∑ t ∈ source,
                  |coefficient t| * kernelMass T q (originalProducts t))) := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  ring
            _ = _ := by rw [Finset.mul_sum]

/-- A split of finite SOURCES, not of admissibility or residue tests.
The exact complete product T is isolated before any shifted-divisor
bound: no expression involving tau(0) is formed. -/
theorem sum_exact_and_off {ι : Type*}
    (source : Finset ι) (product : ι → ℕ) (T : ℕ)
    (f : ι → ℝ) :
    (∑ t ∈ source, f t) =
      (∑ t ∈ source.filter (fun t => product t = T), f t) +
      (∑ t ∈ source.filter (fun t => product t ≠ T), f t) := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : product t = T <;> simp [h]

/-- The full mass is EXACTLY the two disjoint pieces. The arithmetic
estimates of the off-diagonal and exact-product pieces remain to do;
this identity does NOT silently give either of their estimates. -/
theorem fullModulusMass_split {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι)
    (rho : ℕ → ℝ) (coefficient : ι → ℝ)
    (T : ℕ) (originalProducts : ι → Fin g → ℕ) :
    fullModulusMass Q source rho coefficient T originalProducts =
      (∑ q ∈ Q, |rho q| * ∑ t ∈
        source.filter (fun t => (∏ j, originalProducts t j) = T),
        |coefficient t| * kernelMass T q (originalProducts t)) +
      (∑ q ∈ Q, |rho q| * ∑ t ∈
        source.filter (fun t => (∏ j, originalProducts t j) ≠ T),
        |coefficient t| * kernelMass T q (originalProducts t)) := by
  unfold fullModulusMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add]
  congr 1
  exact sum_exact_and_off source (fun t => ∏ j, originalProducts t j) T
    (fun t => |coefficient t| * kernelMass T q (originalProducts t))

/-- On an exact-product source, every congruence test is identically one;
the mean is STILL the exact coprime mean. This term is not thrown into
the shifted-divisor moment where the shift would be zero. -/
theorem exact_product_kernel {g : ℕ}
    (T q : ℕ) (p : Fin g → ℕ)
    (hp : (∏ j, p j) = T) (hcop : Nat.Coprime T q) :
    exactCoprimeTest T q p = 1 - (Nat.totient q : ℝ)⁻¹ := by
  simp [exactCoprimeTest, hp, hcop]

/-- The two tests remain bound to the ORIGINAL all-slot product after HB.
This is a direct transport of the previously written exact identity,
not a new arithmetic distribution assertion. -/
theorem kernel_after_original_HB {d g : ℕ}
    (T q : ℕ) (group : Fin d → Fin g) (n : Fin d → ℕ) :
    exactCoprimeTest T q
        (fun j => ∏ i : Fin d, if group i = j then n i else 1) =
      ((if (∏ i, n i) % q = T % q then 1 else 0) -
        (if Nat.Coprime (∏ i, n i) q
          then (Nat.totient q : ℝ)⁻¹ else 0)) :=
  exactCoprimeTest_after_HB T q group n

end
end ImbalancedChen.P3FullSignedModulusTail
