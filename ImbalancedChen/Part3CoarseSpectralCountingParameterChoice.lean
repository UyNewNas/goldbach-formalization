import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact scalar parameter choice for the quantitative finite-feature
argument. Geometric and Fourier constants are fixed BEFORE the spectral
cutoff. The proof chooses a genuine natural Fourier radius, proves the
half-norm error budget, and proves a quadratic mode-count budget. This
is not a Weyl theorem: no analytic approximation/rank premise is hidden
here, and the actual geometric/Fourier inequalities remain separate.
-/
namespace ImbalancedChen.Part3.CoarseSpectralCountingParameterChoice20261026b
noncomputable section

theorem exists_quadratic_mode_count_parameters (A B Y₀ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hY₀ : 1 ≤ Y₀) :
    ∃ D : ℝ, 0 < D ∧ ∀ Λ : ℝ, 0 ≤ Λ →
      ∃ Y : ℝ, Y₀ ≤ Y ∧ ∃ M : ℕ, 0 < M ∧
        A*(Y*Real.sqrt (1+Λ)+Y^2)/(M : ℝ) +
          B*Real.sqrt (1+Λ)/Y ≤ 1/2 ∧
        (2*(M : ℝ)+1)^2 ≤ D*(1+Λ)^2 := by
  let K : ℝ := Y₀+4*B+1
  have hK : 0 < K := by dsimp [K]; linarith
  have hKY : Y₀ ≤ K := by dsimp [K]; linarith
  let E : ℝ := 4*A*(K+K^2)+1
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨(2*E+5)^2, sq_pos_of_pos (by linarith), ?_⟩
  intro Λ hΛ
  let L : ℝ := 1+Λ
  let s : ℝ := Real.sqrt L
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := by linarith
  have hs : 0 < s := Real.sqrt_pos.2 hLpos
  have hs₁ : 1 ≤ s := by
    dsimp [s]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have hss : s^2 = L := Real.sq_sqrt hLpos.le
  let Y : ℝ := K*s
  have hY : Y₀ ≤ Y := hKY.trans (by
    dsimp [Y]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs₁ hK.le)
  let M : ℕ := Nat.ceil (E*L)+1
  have hM : 0 < M := Nat.zero_lt_succ _
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMlo : E*L ≤ (M : ℝ) := by
    have h := Nat.le_ceil (E*L)
    dsimp [M]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hMhi : (M : ℝ) ≤ (E+2)*L := by
    have h := Nat.ceil_lt_add_one (mul_nonneg hE.le hLpos.le)
    dsimp [M]
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hcoreId : A*(Y*s+Y^2) = A*(K+K^2)*L := by
    calc
      _ = A*(K+K^2)*s^2 := by dsimp [Y]; ring
      _ = _ := by rw [hss]
  have hcore : A*(Y*s+Y^2)/(M : ℝ) ≤ 1/4 := by
    apply (div_le_iff₀ hMreal).mpr
    rw [hcoreId]
    dsimp [E] at hMlo
    nlinarith
  have htailId : B*s/Y = B/K := by
    dsimp [Y]
    field_simp [hK.ne', hs.ne']
    <;> ring
  have htail : B*s/Y ≤ 1/4 := by
    rw [htailId]
    apply (div_le_iff₀ hK).mpr
    dsimp [K]
    linarith
  have hmode : 2*(M : ℝ)+1 ≤ (2*E+5)*L := by nlinarith
  have hmodeSq : (2*(M : ℝ)+1)^2 ≤ (2*E+5)^2*L^2 := by
    calc
      _ ≤ ((2*E+5)*L)^2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr hmode
      _ = _ := mul_pow _ _ _
  refine ⟨Y, hY, M, hM, ?_, ?_⟩
  · change A*(Y*s+Y^2)/(M : ℝ)+B*s/Y ≤ 1/2
    linarith
  · exact hmodeSq

end
end ImbalancedChen.Part3.CoarseSpectralCountingParameterChoice20261026b
