import ImbalancedChen.P2GammaRetainedPhysicalRows
import ImbalancedChen.P4BPositiveUpperLowRankClass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Reuse J's complete, sign-selected small-Rosser attachment and rough-rank
support, now on Q's occupied retained complete-product scale.  This is
the Q-chart conversion, not a new proof of J's HB-chart theorem.  The
actual integer rankRho is unchanged; no ell_aux is substituted into it.
Only the actual upper rough-modulus-rank <= 2 branch is covered here.
-/

namespace ImbalancedChen.P2GammaRetainedLowRankLevel
noncomputable section
open P2GammaSmoothLogGrid P2GammaRetainedCompleteScale
open P2GammaRetainedPhysicalRows P4BPositiveUpperLowRankClass
open P5OriginalU5CausalFinite (pairSupport)

/-- A deterministic local enumeration cap for the existing conductor
theorem. Its 1/20 below-half gap is proved, not a caller premise. -/
def localModulusCap (x : ℝ) : ℕ := Nat.floor (x^(9/20 : ℝ))

theorem localModulusCap_below_half {x : ℝ} (hx : 0 ≤ x) :
    (localModulusCap x : ℝ) ≤ x^((1 : ℝ)/2-1/20) := by
  simpa only [localModulusCap, show (1 : ℝ)/2-1/20 = 9/20 by norm_num] using
    Nat.floor_le (Real.rpow_nonneg hx (9/20 : ℝ))

/-- Both the beta factor and the original upper cutoff 19/96 are inside
the same rankRho. Complete local x is supplied by actual occupancy.
The fixed caps on kappa0 and epsilon are pre-N parameter choices. -/
theorem occupied_actual_rank_two_postloss
    {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ} (hN : 2 ≤ N)
    (ht : t ∈ pairSupport N) {kappa0 δ nu epsilon : ℝ}
    (hk0 : 0 ≤ kappa0) (hk : kappa0 ≤ 1/100)
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2)
    (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1)
    (heps : 0 ≤ epsilon) (hepsSmall : epsilon ≤ 1/1000)
    {j l : ℕ}
    (ho : Occupied N t c cs (2*(N : ℝ)^(1-kappa0)) δ j l)
    (retain : List ℕ → Bool) (cap : ℕ) {q : ℕ}
    (hq : rankRho retain N cap ((N : ℝ)^(nu*epsilon^2))
      ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) 2 q ≠ 0) :
    let x := lower δ j*lower δ l
    0 < q ∧ Squarefree q ∧ q.Coprime N ∧
      |rankRho retain N cap ((N : ℝ)^(nu*epsilon^2))
        ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) 2 q| ≤ 1 ∧
      (q : ℝ) < x^(9/20 : ℝ) ∧ q ≤ localModulusCap x := by
  have hk1 : kappa0 < 1 := by linarith
  have hbeta : 0 < 1-kappa0 := by linarith
  obtain ⟨hlower,hupper,htarget⟩ :=
    occupied_trim_complete_scale hN ht hk1 hδ hwidth ho
  let x := lower δ j*lower δ l
  have hxpos : 0 < x := mul_pos (lower_pos δ j) (lower_pos δ l)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hx1 : 1 ≤ x :=
    (Real.one_le_rpow hNreal hbeta.le).trans hlower
  have hsource := attached_rank_two_support (fun _ => retain) (fun _ => cap)
    (mul_nonneg hnu (by norm_num : (0 : ℝ) ≤ 19/96)) (by omega : 1 ≤ N) hq
  have hqN := (original_upper_rank_two_below_half
    (fun _ => retain) (fun _ => cap) hnu hnu1 heps
      (by linarith : epsilon < 5/48) (by omega : 1 < N) hq).1
  have hexp : (1/(1-kappa0))*(19/48+epsilon) ≤ (9/20 : ℝ) := by
    have hnum : 19/48+epsilon ≤ (9/20)*(1-kappa0) := by nlinarith
    have hdiv := (div_le_iff₀ hbeta).mpr hnum
    simpa only [one_div,div_eq_mul_inv,mul_comm] using hdiv
  have hqx : (q : ℝ) < x^(9/20 : ℝ) := by
    calc
      (q : ℝ) < (N : ℝ)^(19/48+epsilon) := hqN
      _ ≤ (x^(1/(1-kappa0)))^(19/48+epsilon) :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) htarget (by linarith)
      _ = x^((1/(1-kappa0))*(19/48+epsilon)) :=
        (Real.rpow_mul hxpos.le _ _).symm
      _ ≤ x^(9/20 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hexp
  exact ⟨hsource.1,hsource.2.1,hsource.2.2.1,
    rankRho_abs_le_one _ _ _ _ _ _ _ _,hqx,Nat.le_floor hqx.le⟩

end
end ImbalancedChen.P2GammaRetainedLowRankLevel
