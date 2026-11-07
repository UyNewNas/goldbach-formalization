import ImbalancedChen.Part3PrimaryNuEulerSubpower

/-!
SOURCEONLY / UNCOMPILED / OPEN30. One corollary of exact ae722340.
The proposed parent import is an assembly contract, not installed status.
No parent is copied or edited. C is selected before kappa, with only a
fixed upper budget kappa0. This includes kappa=0 and retains |rho|^(7/32).
-/

namespace ImbalancedChen.Part3.PrimaryNuUniformKappaSourceOnly
noncomputable section
open Classical Finset
open ActualCompletedSquarePushforwardSourceOnly
open FixedRhoPrimarySignedFiniteSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualM2FinitePoissonAdapterSourceOnly
open PrimaryNuEulerSubpowerSourceOnly
open scoped BigOperators

/-- Uniform throughout 0<=kappa<=kappa0. The SAME C pays both the raw
primary sum and the literal original ABL cost after the count's 1/nu.
No strict positivity of kappa or signed rho is assumed. -/
theorem actual_primaryKeys_uniform_kappa_subpower
    (kappa0 : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ kappa : ℝ, 0 ≤ kappa → kappa ≤ kappa0 →
      ∀ (B : ℕ) (sigma c0 : ℝ) (e : MediumAtom),
      0 < c0 → MediumAdmissible B sigma kappa c0 e →
      ∀ (negative : Bool) (U : Finset Source),
      ((∑ nu ∈ primaryKeys (signedResidue negative e.residue) U,
        (nu : ℝ)^(7 / 32 - 1 : ℝ)) ≤ C * e.scale^eps) ∧
      ((∑ nu ∈ primaryKeys (signedResidue negative e.residue) U,
        (((signedResidue negative e.residue).natAbs : ℝ) * (nu : ℝ))^(7 / 32 : ℝ) /
          (nu : ℝ)) ≤ (e.residue.natAbs : ℝ)^(7 / 32 : ℝ) * (C * e.scale^eps)) := by
  let K : ℝ := 1 + max kappa0 0
  have hKpos : 0 < K := by
    dsimp only [K]
    linarith [le_max_right kappa0 0]
  let delta : ℝ := eps / K
  have hdelta : 0 < delta := div_pos heps hKpos
  have hKdelta : K * delta = eps := by
    dsimp only [delta]
    field_simp [hKpos.ne']
  obtain ⟨C, hC, hbound⟩ := finite_supported_sum_subpower hdelta
  refine ⟨C, hC, ?_⟩
  intro kappa _hkappa hkappa0 B sigma c0 e hc0 he negative U
  have hrho := actual_signedResidue_ne_zero hc0 he negative
  have hs := hbound (signedResidue negative e.residue) hrho
    (primaryKeys (signedResidue negative e.residue) U)
    (fun nu hnu p hp hpn => primaryKeys_prime_support hnu hp hpn)
  rw [signedResidue_natAbs] at hs
  have hx : 1 ≤ e.scale := by
    change 1 ≤ e.U * e.V
    simpa only [one_mul] using
      mul_le_mul he.1 he.2.1 zero_le_one (zero_le_one.trans he.1)
  have hkK : 1 + kappa ≤ K := by
    simpa only [K, add_comm] using
      add_le_add_left (hkappa0.trans (le_max_left kappa0 0)) 1
  obtain ⟨_, _, _, _, _, _, _, hres, _⟩ := he
  have haK : (e.residue.natAbs : ℝ) ≤ e.scale^K :=
    hres.trans (Real.rpow_le_rpow_of_exponent_le hx hkK)
  have hraw : (∑ nu ∈ primaryKeys (signedResidue negative e.residue) U,
      (nu : ℝ)^(7 / 32 - 1 : ℝ)) ≤ C * e.scale^eps := by
    calc
      _ ≤ C * (e.residue.natAbs : ℝ)^delta := hs
      _ ≤ C * (e.scale^K)^delta := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) haK hdelta.le) hC.le
      _ = _ := by rw [← Real.rpow_mul (zero_le_one.trans hx), hKdelta]
  refine ⟨hraw, ?_⟩
  rw [primaryKeys_ABL_cost_eq, signedResidue_natAbs]
  exact mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end
end ImbalancedChen.Part3.PrimaryNuUniformKappaSourceOnly
