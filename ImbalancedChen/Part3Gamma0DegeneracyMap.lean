import ImbalancedChen.Part3Gamma0ActualCusps
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.
The elementary oldform degeneracy map at positive integers N,d: conjugate
Gamma0(Nd) by diag(sqrt d,1/sqrt d), obtaining an integral Gamma0(N)
matrix. Consequently precomposition by the real scaling preserves the
literal upper-half-plane invariance condition. This contains no norm,
orthogonality, or packet assertion.
-/

namespace ImbalancedChen.Part3.Gamma0DegeneracyMapSourceOnly
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open Gamma0ActualCuspsSourceOnly

/-- The real determinant-one scaling matrix for z ↦ d*z. -/
def degeneracyDiagonal (d : ℕ) (hd : 0 < d) : SL(2, ℝ) :=
  ⟨!![Real.sqrt (d : ℝ), 0; 0, 1 / Real.sqrt (d : ℝ)], by
    have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hs : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.2 hdr).ne'
    simp [Matrix.det_fin_two_of, hs]⟩

private def castSL (g : SL(2, ℤ)) : SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g

/-- The c-entry division is integral because Nd divides the source c-entry.
The displayed matrix is explicitly [[a,d*b],[c/d,e]]. -/
theorem exists_gamma0_degeneracy_matrix (N d : ℕ) (hN : 0 < N)
    (hd : 0 < d) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N * d)) :
    ∃ γ' : SL(2, ℤ),
      γ' ∈ CongruenceSubgroup.Gamma0 N ∧
      γ' 0 0 = γ 0 0 ∧
      γ' 0 1 = (d : ℤ) * γ 0 1 ∧
      (d : ℤ) * γ' 1 0 = γ 1 0 ∧
      γ' 1 1 = γ 1 1 ∧
      castSL γ' =
        degeneracyDiagonal d hd * castSL γ * (degeneracyDiagonal d hd)⁻¹ := by
  have hdiv : ((N * d : ℕ) : ℤ) ∣ γ 1 0 :=
    (gamma0_mem_iff_level_dvd_c (N * d) γ).mp hγ
  obtain ⟨k, hk⟩ := hdiv
  have hc : γ 1 0 = (N : ℤ) * (d : ℤ) * k := by
    simpa only [Nat.cast_mul, mul_assoc] using hk
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  let γ' : SL(2, ℤ) :=
    ⟨!![γ 0 0, (d : ℤ) * γ 0 1;
        (N : ℤ) * k, γ 1 1], by
      rw [Matrix.det_fin_two_of]
      rw [hc] at hdet
      nlinarith [hdet]⟩
  have hmem : γ' ∈ CongruenceSubgroup.Gamma0 N := by
    rw [gamma0_mem_iff_level_dvd_c]
    change (N : ℤ) ∣ (N : ℤ) * k
    exact ⟨k, rfl⟩
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.2 hdr).ne'
  have hsqr : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt hdr.le
  have hreal : castSL γ' =
      degeneracyDiagonal d hd * castSL γ *
        (degeneracyDiagonal d hd)⁻¹ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [castSL, γ', degeneracyDiagonal, SL2_inv_expl,
        Matrix.mul_fin_two, coe_mul, hc] <;>
      field_simp [hs] <;>
      nlinarith [hsqr]
  refine ⟨γ', hmem, ?_, ?_, ?_, ?_, hreal⟩
  · rfl
  · rfl
  · change (d : ℤ) * ((N : ℤ) * k) = γ 1 0
    rw [hc]
    ring
  · rfl

private lemma castSL_smul (g : SL(2, ℤ)) (z : ℍ) :
    castSL g • z = g • z := by
  rfl

/-- The diagonal action is literally multiplication of the complex
coordinate by the positive integer d. -/
theorem degeneracyDiagonal_smul_coe (d : ℕ) (hd : 0 < d) (z : ℍ) :
    ((degeneracyDiagonal d hd • z : ℍ) : ℂ) = (d : ℂ) * (z : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hs : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.2 hdr).ne'
  have hsqr : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt hdr.le
  have hsC : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hs
  have hsqrC : (Real.sqrt (d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast hsqr
  simp [degeneracyDiagonal] <;>
    rw [← hsqrC] <;>
    field_simp [hsC] <;>
    ring

/-- If f is actually Gamma0(N)-invariant, its scaled function f(d*z)
is Gamma0(Nd)-invariant via the explicit integral matrix above. -/
theorem scaled_function_gamma0_invariant (N d : ℕ)
    (hN : 0 < N) (hd : 0 < d) (f : ℍ → ℂ)
    (hf : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (g • z) = f z) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * d) →
      ∀ z : ℍ,
        f (degeneracyDiagonal d hd • (γ • z)) =
          f (degeneracyDiagonal d hd • z) := by
  intro γ hγ z
  obtain ⟨γ', hmem, _, _, _, _, hreal⟩ :=
    exists_gamma0_degeneracy_matrix N d hN hd γ hγ
  have hcomm : degeneracyDiagonal d hd * castSL γ =
      castSL γ' * degeneracyDiagonal d hd := by
    rw [hreal]
    group
  calc
    f (degeneracyDiagonal d hd • (γ • z)) =
        f ((degeneracyDiagonal d hd * castSL γ) • z) := by
      rw [← castSL_smul γ z, mul_smul]
    _ = f ((castSL γ' * degeneracyDiagonal d hd) • z) := by
      rw [hcomm]
    _ = f (γ' • (degeneracyDiagonal d hd • z)) := by
      rw [mul_smul, castSL_smul]
    _ = f (degeneracyDiagonal d hd • z) := hf γ' hmem _

end
end ImbalancedChen.Part3.Gamma0DegeneracyMapSourceOnly
