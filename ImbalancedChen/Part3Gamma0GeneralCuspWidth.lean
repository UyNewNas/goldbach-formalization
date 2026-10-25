import ImbalancedChen.Part3Gamma0ActualCusps
import Mathlib.Data.Int.GCD

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual Gamma0 integer cusp periods for ANY integral determinant-one
matrix gamma=[[a,b],[c,d]]. The lower-left conjugated translation entry
is -c^2*k, and the exact positive primitive period is
N/gcd(N,natAbs(c)^2). General stabilizers are classified modulo the
central sign. Infinity and the real cusp1 matrix are actual specializations.
No identification of different cusps, spectral measure, or Fourier dt
normalization is inferred from this elementary geometric supplier.
-/

namespace ImbalancedChen.Part3.Gamma0GeneralCuspWidth20261025a
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups ModularGroup UpperHalfPlane
open Gamma0ActualCuspsSourceOnly

/-- The square in the natural gcd is the absolute integral c-entry
square; this is exactly c^2, with no choice of rational cusp surrogate. -/
def cuspWidth (N : ℕ) (gamma : SL(2, ℤ)) : ℕ :=
  N / Nat.gcd N ((gamma 1 0).natAbs ^ 2)

theorem cuspWidth_pos (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ)) :
    0 < cuspWidth N gamma :=
  Nat.div_gcd_pos_of_pos_left _ hN

theorem conjugated_translation_c (gamma : SL(2, ℤ)) (k : ℤ) :
    (gamma * ModularGroup.T ^ k * gamma⁻¹) 1 0 = -((gamma 1 0) ^ 2 * k) := by
  simp [SL2_inv_expl, ModularGroup.coe_T_zpow, coe_mul, Matrix.mul_fin_two] <;> ring

/-- Exact actual congruence-subgroup membership, retaining the sign and
the square arising from the full integral matrix conjugation. -/
theorem conjugated_translation_mem_iff_level_dvd (N : ℕ) (gamma : SL(2, ℤ)) (k : ℤ) :
    gamma * ModularGroup.T ^ k * gamma⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (N : ℤ) ∣ (gamma 1 0) ^ 2 * k := by
  rw [gamma0_mem_iff_level_dvd_c, conjugated_translation_c]
  simp only [dvd_neg]

/-- The gcd removes precisely the common divisor of N and c^2.
Integer signs of c and k are handled by natAbs divisibility, not assumed. -/
theorem level_dvd_square_mul_iff_width_dvd (N : ℕ) (hN : 0 < N)
    (gamma : SL(2, ℤ)) (k : ℤ) :
    (N : ℤ) ∣ (gamma 1 0) ^ 2 * k ↔ (cuspWidth N gamma : ℤ) ∣ k := by
  rw [← Int.natAbs_dvd_natAbs, ← Int.natAbs_dvd_natAbs]
  simp only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow, cuspWidth]
  calc
    N ∣ (gamma 1 0).natAbs ^ 2 * k.natAbs ↔
        N ∣ Nat.gcd N ((gamma 1 0).natAbs ^ 2) * k.natAbs :=
      Nat.dvd_gcd_mul_iff_dvd_mul.symm
    _ ↔ N / Nat.gcd N ((gamma 1 0).natAbs ^ 2) ∣ k.natAbs :=
      (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left N ((gamma 1 0).natAbs ^ 2))
        (Nat.gcd_pos_of_pos_left _ hN)).symm

theorem conjugated_translation_mem_iff_width_dvd (N : ℕ) (hN : 0 < N)
    (gamma : SL(2, ℤ)) (k : ℤ) :
    gamma * ModularGroup.T ^ k * gamma⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (cuspWidth N gamma : ℤ) ∣ k := by
  rw [conjugated_translation_mem_iff_level_dvd,
    level_dvd_square_mul_iff_width_dvd N hN gamma k]

theorem conjugated_translation_mem_iff_multiple (N : ℕ) (hN : 0 < N)
    (gamma : SL(2, ℤ)) (k : ℤ) :
    gamma * ModularGroup.T ^ k * gamma⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      ∃ j : ℤ, k = (cuspWidth N gamma : ℤ) * j := by
  rw [conjugated_translation_mem_iff_width_dvd N hN gamma k]
  rfl

theorem width_multiple_mem_gamma0 (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ)) (k : ℤ) :
    gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * k) * gamma⁻¹ ∈
      CongruenceSubgroup.Gamma0 N := by
  exact (conjugated_translation_mem_iff_width_dvd N hN gamma _).mpr ⟨k, rfl⟩

/-- The formula is the LEAST positive integer stabilizer period. -/
theorem cuspWidth_minimal (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ))
    (k : ℕ) (hk : 0 < k)
    (hmem : gamma * ModularGroup.T ^ (k : ℤ) * gamma⁻¹ ∈ CongruenceSubgroup.Gamma0 N) :
    cuspWidth N gamma ≤ k := by
  have hdiv := (conjugated_translation_mem_iff_width_dvd N hN gamma (k : ℤ)).mp hmem
  exact Nat.le_of_dvd hk (Int.natCast_dvd_natCast.mp hdiv)

/-- The actual cusp gamma(infinity) stabilizer condition after conjugation. -/
def FixesIntegralCusp (gamma g : SL(2, ℤ)) : Prop := (gamma⁻¹ * g * gamma) 1 0 = 0

/-- The conjugated c-entry condition is EXACTLY fixing the actual
projective cusp gamma(infinity), for the genuine matrix action. -/
theorem fixesIntegralCusp_iff_actual_action (gamma g : SL(2, ℤ)) :
    FixesIntegralCusp gamma g ↔
      mapGL ℝ g • (mapGL ℝ gamma • (∞ : OnePoint ℝ)) =
        mapGL ℝ gamma • (∞ : OnePoint ℝ) := by
  have hconj : mapGL ℝ (gamma⁻¹ * g * gamma) • (∞ : OnePoint ℝ) = ∞ ↔
      (gamma⁻¹ * g * gamma) 1 0 = 0 := by
    simp [smul_infty_eq_self_iff, mapGL_coe_matrix]
  rw [FixesIntegralCusp, ← hconj]
  simp only [map_mul, map_inv, mul_smul]
  constructor
  · intro h
    have hh := congrArg (fun x : OnePoint ℝ => mapGL ℝ gamma • x) h
    simpa only [smul_inv_smul] using hh
  · intro h
    have hh := congrArg (fun x : OnePoint ℝ => (mapGL ℝ gamma)⁻¹ • x) h
    simpa only [inv_smul_smul] using hh

private theorem upperTriangular_signed_translation (h : SL(2, ℤ)) (hc : h 1 0 = 0) :
    ∃ j : ℤ, h = ModularGroup.T ^ j ∨ h = -(ModularGroup.T ^ j) := by
  have had := h.det_coe
  replace had : h 0 0 * h 1 1 = 1 := by
    rw [Matrix.det_fin_two, hc] at had
    lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · refine ⟨h 0 1, Or.inl ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, ModularGroup.coe_T_zpow,
        show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · refine ⟨-(h 0 1), Or.inr ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, ModularGroup.coe_T_zpow,
        show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]

/-- Every genuine Gamma0 stabilizer at this integral cusp is a multiple
of its computed width, up to the projectively trivial central sign. -/
theorem gamma0_cusp_stabilizer_classification (N : ℕ) (hN : 0 < N)
    (gamma : SL(2, ℤ)) (g : CongruenceSubgroup.Gamma0 N)
    (hg : FixesIntegralCusp gamma (g : SL(2, ℤ))) :
    ∃ k : ℤ, (g : SL(2, ℤ)) =
        gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * k) * gamma⁻¹ ∨
      (g : SL(2, ℤ)) =
        -(gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * k) * gamma⁻¹) := by
  let h : SL(2, ℤ) := gamma⁻¹ * (g : SL(2, ℤ)) * gamma
  obtain ⟨j, hj⟩ := upperTriangular_signed_translation h hg
  have hrecover : (g : SL(2, ℤ)) = gamma * h * gamma⁻¹ := by
    dsimp [h]
    group
  have hcdiv : (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 :=
    (gamma0_mem_iff_level_dvd_c N (g : SL(2, ℤ))).mp g.property
  rcases hj with hpos | hneg
  · have heq : (g : SL(2, ℤ)) = gamma * ModularGroup.T ^ j * gamma⁻¹ := by
      simpa only [hpos] using hrecover
    have hjmem : gamma * ModularGroup.T ^ j * gamma⁻¹ ∈ CongruenceSubgroup.Gamma0 N :=
      heq ▸ g.property
    obtain ⟨k, hk⟩ := (conjugated_translation_mem_iff_multiple N hN gamma j).mp hjmem
    exact ⟨k, Or.inl (by simpa only [hk] using heq)⟩
  · have heq : (g : SL(2, ℤ)) = -(gamma * ModularGroup.T ^ j * gamma⁻¹) := by
      rw [hneg] at hrecover
      simpa only [mul_neg, neg_mul] using hrecover
    have hjdiv : (N : ℤ) ∣ (gamma 1 0) ^ 2 * j := by
      simpa [heq, conjugated_translation_c] using hcdiv
    obtain ⟨k, hk⟩ := (level_dvd_square_mul_iff_width_dvd N hN gamma j).mp hjdiv
    exact ⟨k, Or.inr (by simpa only [hk] using heq)⟩

theorem cuspWidth_infinity (N : ℕ) (hN : 0 < N) : cuspWidth N (1 : SL(2, ℤ)) = 1 := by
  simp [cuspWidth, Nat.ne_of_gt hN]

theorem cuspWidth_cuspOne (N : ℕ) : cuspWidth N cuspOneMatrix = N := by
  simp [cuspWidth, cuspOneMatrix]

/-- The old cusp1 period-N statement is a specialization of the full
matrix theorem, rather than an assumption about a newly named cusp. -/
theorem cuspOne_specialization (N : ℕ) (hN : 0 < N) (k : ℤ) :
    cuspOneMatrix * ModularGroup.T ^ k * cuspOneMatrix⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (N : ℤ) ∣ k := by
  simpa only [cuspWidth_cuspOne] using conjugated_translation_mem_iff_width_dvd N hN cuspOneMatrix k

end
end ImbalancedChen.Part3.Gamma0GeneralCuspWidth20261025a
