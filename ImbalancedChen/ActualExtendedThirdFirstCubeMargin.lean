import ImbalancedChen.ActualExtendedThirdDyadicCoverage

/-!
# The actual robust cap pays its own first cube

The manuscript's first-stop wall is `ux <= rho - 4e`. Its baseline entry
already suffices to prove the first-cube license, before proving convergence
of the robust envelope. For `0 < e <= 1/384` and mesh width at most `e/2`,
every point in every actual retained closed ordered portion has
`lambda >= 3x + e > 3x`.

The cell infimum here is the actual physical infimum, including portions
meeting an ordering wall. Neither a numerical certificate endpoint nor an
assumed closeness of Gamma to the ideal envelope is used. The final theorem
converts this exponent license to the literal prime cube inequality. Other
factorization branch licenses and the same-policy arithmetic mean remain
separate obligations.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology
open VariableEnvelope
open scoped Classical

/-- A quantitative version of the two actual affine first-stop margins. -/
theorem actualExtendedThird_v_firstCube_margin {e x : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (hx : x ≤ thirdPrefixRho - 4 * e) :
    (9 / 2 : ℝ) * e ≤ v x - 3 * x := by
  by_cases hxmu : x ≤ mu
  · rw [v_eq_A hxmu]
    dsimp [A, mu] at *
    linarith
  · rw [extended_v_margin_above_mu (le_of_not_ge hxmu)]
    dsimp [extendedFirstStop, thirdPrefixRho] at *
    linarith

/-- A common mesh pays the variation of the baseline throughout the true
closed ordered portion; no pointwise approximation hypothesis is supplied. -/
theorem actualExtendedThirdPhysicalGamma_firstCube_margin {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 ≤ e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (hj : j ∈ actualExtendedThirdRetainedCells e m)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    3 * t 0 + 3 * e ≤ actualExtendedThirdPhysicalGamma e m j := by
  have hstop := (mem_actualExtendedThirdRetainedCells.mp hj).2
  apply le_trans ?_ (actualExtendedThirdPhysicalGamma_ge_baseline e m j)
  apply le_csInf ((show (actualExtendedThirdPhysicalCell m j).Nonempty from ⟨t, ht⟩).image _)
  rintro _ ⟨s, hs, rfl⟩
  change 3 * t 0 + 3 * e ≤ v (s 0)
  have hsstop : s 0 ≤ thirdPrefixRho - 4 * e := (hs.1 0 (mem_univ _)).2.trans hstop
  have hmargin := actualExtendedThird_v_firstCube_margin he0 he hsstop
  have hslo := (hs.1 0 (mem_univ _)).1
  have hthi := (ht.1 0 (mem_univ _)).2
  have hwidth := actualExtendedThirdDyadicHi_eq_lo_add_step m j 0
  linarith

/-- Both entries of the actual buffered minimum retain the same positive
first-cube surplus. This is a license for this physical cell's actual cap. -/
theorem actualExtendedThirdPhysicalLevel_firstCube_margin {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 ≤ e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (hj : j ∈ actualExtendedThirdRetainedCells e m)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    3 * t 0 + e ≤ actualExtendedThirdPhysicalLevel e m j := by
  have hstop := (mem_actualExtendedThirdRetainedCells.mp hj).2
  have hx : t 0 ≤ thirdPrefixRho - 4 * e := (ht.1 0 (mem_univ _)).2.trans hstop
  have hgamma := actualExtendedThirdPhysicalGamma_firstCube_margin he0 he hmesh hj ht
  unfold actualExtendedThirdPhysicalLevel thirdPrefixBufferedCap
  apply le_min
  · dsimp [thirdPrefixTheta, thirdPrefixRho] at *
    linarith
  · linarith

theorem actualExtendedThirdPhysicalLevel_firstCube_strict {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (hj : j ∈ actualExtendedThirdRetainedCells e m)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    3 * t 0 < actualExtendedThirdPhysicalLevel e m j := by
  linarith [actualExtendedThirdPhysicalLevel_firstCube_margin he0.le he hmesh hj ht]

/-- The grid threshold is chosen before every cell and point. -/
theorem actualExtendedThirdPhysicalLevel_uniform_firstCube_margin {e : ℝ}
    (he0 : 0 < e) (he : e ≤ 1 / 384) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ j ∈ actualExtendedThirdRetainedCells e m,
        ∀ t ∈ actualExtendedThirdPhysicalCell m j,
          3 * t 0 + e ≤ actualExtendedThirdPhysicalLevel e m j := by
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    (tendsto_actualExtendedThirdDyadicStep.eventually
      (gt_mem_nhds (show 0 < e / 2 by linarith)))
  exact ⟨m₀, fun m hm j hj t ht =>
    actualExtendedThirdPhysicalLevel_firstCube_margin he0.le he (hm₀ m hm).le hj ht⟩

/-- The already proved real-power supplier turns the actual cap's exponent
surplus into its literal integer-prefix first-cube test. -/
theorem actualExtendedThirdPhysicalLevel_prime_firstCube {e N : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (p : ℕ) (hN : 1 < N)
    (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (hj : j ∈ actualExtendedThirdRetainedCells e m)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hp : (p : ℝ) ≤ N ^ (t 0)) :
    (p : ℝ) ^ 3 < N ^ (actualExtendedThirdPhysicalLevel e m j) :=
  first_cube_lt_level_of_exponent p hN hp
    (actualExtendedThirdPhysicalLevel_firstCube_strict he0 he hmesh hj ht)

end

end ImbalancedChen
