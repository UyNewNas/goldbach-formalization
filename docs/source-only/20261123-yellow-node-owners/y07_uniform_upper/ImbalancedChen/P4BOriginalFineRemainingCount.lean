import ImbalancedChen.P4BOriginalFineAttachedUpper
import ImbalancedChen.P4BOriginalShortMediumCount

/-! On the compiled Fine coefficient, put the original normalized mass
and density into the printed constant. The surviving medium row is exactly
the two-group chart/HB bank from the short-medium count. -/
namespace ImbalancedChen.P4BOriginalFineRemainingCount

noncomputable section
open Filter Topology
open P4BOriginalFineAttachedUpper (Selection compiledDensity meshWidth)
open P4BOriginalCollisionWords (Params)
open P4BOriginalFiniteSmoothCount (mass Q)
open P4BOriginalHighRankScheduledCount (outerWidth)
open P4BOriginalShortMediumAtlas (remainingAtlas)
open P4BOriginalShortMediumFibreIntegral (WordRange)
open P4BOuterRampRoughness (baseline)

private theorem mass_times_density {N : ℕ} (hN : 2 ≤ N) {M D J d : ℝ} (hM : 0 ≤ M)
    (hApprox : |M / ((N : ℝ) / Real.log (N : ℝ)) - J| < d)
    (hD : D ≤ currentK * (singularSeries N / Real.log (N : ℝ))) :
    M * D ≤ (currentK * (J + d)) * singularNormalization N := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  have hm : M ≤ (J + d) * ((N : ℝ) / Real.log (N : ℝ)) :=
    (div_le_iff₀ hscale).mp (by linarith only [(abs_lt.mp hApprox).2])
  have hK : 0 ≤ currentK := by norm_num [currentK]
  calc
    M * D ≤ M * (currentK * (singularSeries N / Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hD hM
    _ ≤ ((J + d) * ((N : ℝ) / Real.log (N : ℝ))) *
          (currentK * (singularSeries N / Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hm (mul_nonneg hK (densityScale_pos hN).le)
    _ = _ := by rw [← sourceMassScale_mul_densityScale N]; ring

variable {m r n q : ℕ} {e : ℚ} {a nu v etaPP betaMax zeta : ℝ} {ft : ℝ → ℝ}

/-- On this fixed Fine witness the old `RealB` receiver's single explicit
remainder suffices for any tolerance. It includes all surviving short-head
words, long heads and untouched live medium fibres. -/
theorem eventually_count_with_remaining (s : Selection m r n e q a nu v etaPP betaMax zeta ft)
    (K : ℕ) (hK : 2 ≤ K) (he : 0 ≤ e) (he1 : (e : ℝ) ≤ 1 / 2048) (hq : 0 < q)
    (hnu : 0 < nu) (hcut : nu * v = 19 / 96) {b kappa kap0 : ℝ}
    (hb : (1 / 2 : ℝ) < b) (hb1 : b < 1) (hz : 0 < zeta) (hz0 : zeta ≤ 1 / 20000)
    (hk : 0 < kappa) (hkz : kappa ≤ zeta / 200000) (ht : kap0 < kappa / (4 * (1 + kappa)))
    (hkap : 0 < kap0) (ht1 : kap0 < 1) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      let P : Params := ⟨m, r, n, e, q, a, nu * s.beta ^ 2, s.k, N, nu * s.beta⟩
      (RealB b N : ℝ) ≤ (currentK * Real.log (1 / b) + tolerance) * singularNormalization N +
        (remainingAtlas P b kap0 (outerWidth N) kap0 zeta K 3).re := by
  intro tolerance htolerance
  have hKpos : 0 < currentK + 1 := by norm_num [currentK]
  let d := tolerance / (currentK + 1)
  have hd : 0 < d := div_pos htolerance hKpos
  have hspend : (currentK + 1) * d = tolerance := by
    dsimp only [d]
    field_simp [hKpos.ne']
  have homega : nu * s.beta ^ 2 ≤ 19 / 96 := by
    rw [← hcut]
    exact mul_le_mul_of_nonneg_left s.square_lt.le hnu.le
  have hgate : 19 / 96 < baseline b kap0 :=
    P4BOriginalFiniteSmoothSchedule.original_product_gap hb hk ht
  have hbound := P4BOriginalShortMediumCount.eventually_RealB_le_remaining K hK nu s.beta
    (meshWidth m e q a s.k) d hnu s.pos (s.lt_eighth.le.trans (by norm_num)) homega hd
    hz hz0 hk hkz ht ht1 hkap hb hb1 hgate
  filter_upwards [hbound, s.compiled_K, eventually_ge_atTop (2 : ℕ)] with N hc hD hN
  intro hEven
  let P : Params := ⟨m, r, n, e, q, a, nu * s.beta ^ 2, s.k, N, nu * s.beta⟩
  let Y := (remainingAtlas P b kap0 (outerWidth N) kap0 zeta K 3).re
  let J := Real.log (1 / b)
  let M := mass b kap0 (outerWidth N) N
  let D := compiledDensity m r n e q a nu s.beta s.k N
  obtain ⟨hm, happrox, hfinite⟩ := hc hEven
  have hW : WordRange P (nu * s.beta ^ 2) (meshWidth m e q a s.k) zeta := by
    refine ⟨rfl, rfl, he, he1, hq, s.mesh_extra, (mul_pos hnu s.pos).le, ?_⟩
    change 2 * (nu * s.beta) ≤ zeta / 16
    linarith only [s.small_extra]
  have hcount : (RealB b N : ℝ) ≤ M * D + Y + d * singularNormalization N :=
    hfinite m r n e q a s.k hW
  have hmain : M * D ≤ (currentK * (J + d)) * singularNormalization N :=
    mass_times_density hN hm happrox (hD hEven)
  calc
    (RealB b N : ℝ) ≤ (currentK * (J + d)) * singularNormalization N + Y +
        d * singularNormalization N :=
      hcount.trans (add_le_add_right (add_le_add_right hmain _) _)
    _ = (currentK * J + (currentK + 1) * d) * singularNormalization N + Y := by ring
    _ = _ := by rw [hspend]

/-- The literal `hUpper` follows from the remaining reconstructed signed
row on this schedule. The premise is only its upper real part, at the same
policy and grid. The whole-row complex norm is also a sufficient payment. -/
theorem upper_of_remaining (s : Selection m r n e q a nu v etaPP betaMax zeta ft)
    (K : ℕ) (hK : 2 ≤ K) (he : 0 ≤ e) (he1 : (e : ℝ) ≤ 1 / 2048) (hq : 0 < q)
    (hnu : 0 < nu) (hcut : nu * v = 19 / 96) {b kappa kap0 : ℝ}
    (hb : (1 / 2 : ℝ) < b) (hb1 : b < 1) (hz : 0 < zeta) (hz0 : zeta ≤ 1 / 20000)
    (hk : 0 < kappa) (hkz : kappa ≤ zeta / 200000) (ht : kap0 < kappa / (4 * (1 + kappa)))
    (hkap : 0 < kap0) (ht1 : kap0 < 1)
    (hRemaining : ∀ t : ℝ, 0 < t → ∀ᶠ N : ℕ in atTop, Even N →
      let P : Params := ⟨m, r, n, e, q, a, nu * s.beta ^ 2, s.k, N, nu * s.beta⟩
      (remainingAtlas P b kap0 (outerWidth N) kap0 zeta K 3).re ≤ t * singularNormalization N) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤ (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  intro tolerance htolerance
  filter_upwards [eventually_count_with_remaining s K hK he he1 hq hnu hcut hb hb1 hz hz0 hk hkz
    ht hkap ht1 (tolerance / 2) (half_pos htolerance),
    hRemaining (tolerance / 2) (half_pos htolerance)] with N hCount hRest
  intro hEven
  exact ((hCount hEven).trans (add_le_add_left (hRest hEven) _)).trans_eq (by ring)

end
end ImbalancedChen.P4BOriginalFineRemainingCount
