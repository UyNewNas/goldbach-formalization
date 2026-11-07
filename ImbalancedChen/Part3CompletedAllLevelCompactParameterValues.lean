import ImbalancedChen.Part3CompletedParameterDiskHeightValues
import ImbalancedChen.Part3AllLevelContinuedMaass
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
Uniform compact parameter/height bounds for the literal completed level-N
oldform. Finite-list induction retains every actual Euler coefficient and
every positive integral dilation. Division uses the actual regular Euler
denominator. Actual parameter holomorphy then extends the circle bound to
a full disk, with the correctly regularized central value included.
-/
namespace ImbalancedChen.Part3.CompletedAllLevelCompactParameterValues20261026b
noncomputable section
open Set Complex Metric
open scoped Topology UpperHalfPlane
open ImbalancedChen.Part3.CompletedCompactParameterHeightValues20261026b
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a

private def completedList (L : List (ℕ+ × ℂ)) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  (L.map (fun t => t.2 * completedActualEisenstein s (pnatDilate t.1 z))).sum

private theorem completedList_raise (p : PrimeIndex) (L : List (ℕ+ × ℂ))
    (s : ℂ) (z : UpperHalfPlane) :
    completedList (L.map (fun t => (primePNat p * t.1, t.2))) s z =
      completedList L s (pnatDilate (primePNat p) z) := by
  induction L with
  | nil => simp [completedList]
  | cons t L ih =>
      simp only [completedList, List.map_cons, List.sum_cons, pnatDilate_mul] at ih ⊢
      rw [ih]

private theorem completedList_scale (a : ℂ) (L : List (ℕ+ × ℂ))
    (s : ℂ) (z : UpperHalfPlane) :
    completedList (L.map (fun t => (t.1, a * t.2))) s z = a * completedList L s z := by
  induction L with
  | nil => simp [completedList]
  | cons t L ih =>
      simp only [completedList, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

private theorem completedList_cons (p : PrimeIndex) (L : List PrimeIndex)
    (s : ℂ) (z : UpperHalfPlane) :
    completedList (oldformTerms (p :: L) s) s z =
      if p.1 ∣ primeProduct L then
        completedList (oldformTerms L s) s (pnatDilate (primePNat p) z)
      else completedList (oldformTerms L s) s (pnatDilate (primePNat p) z) -
        (p.1 : ℂ) ^ (-s) * completedList (oldformTerms L s) s z := by
  unfold oldformTerms
  split_ifs
  · exact completedList_raise p _ s z
  · rw [show completedList
        ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2)) ++
          (oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) s z =
        completedList ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2))) s z +
          completedList ((oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) s z by
        simp only [completedList, List.map_append, List.sum_append]]
    rw [completedList_raise, completedList_scale]
    ring

private theorem completedList_compact_bound (K : Set ℂ) (hK : IsCompact K)
    (hregular : ∀ s ∈ K, s ≠ 0 ∧ s ≠ 1 ∧ s ≠ 1 / 2) (L : List PrimeIndex) :
    ∀ {a b : ℝ}, 0 < a → a ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ z : UpperHalfPlane, z.im ∈ Icc a b →
        ‖completedList (oldformTerms L s) s z‖ ≤ C := by
  induction L with
  | nil =>
      intro a b ha hab
      obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
      let M := Nat.ceil B
      have hM : ∀ s ∈ K, |s.re| ≤ (M : ℝ) := fun s hs =>
        (Complex.abs_re_le_norm s).trans ((hB s hs).trans (Nat.le_ceil B))
      obtain ⟨C, hC, hb⟩ := exists_completedFourier_compact_height_bound K hK M hM ha hab hregular
      refine ⟨C, hC, ?_⟩
      intro s hs z hz
      simpa [completedList, oldformTerms, pnatDilate_one, completedActualEisenstein] using
        hb s hs z.im hz z.re
  | cons p L ih =>
      intro a b ha hab
      have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
      obtain ⟨C, hC, hbC⟩ := ih (mul_pos hp ha) (mul_le_mul_of_nonneg_left hab hp.le)
      obtain ⟨D, hD, hbD⟩ := ih ha hab
      have hpow : Continuous (fun s : ℂ => (p.1 : ℂ) ^ (-s)) :=
        continuous_neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr p.2.ne_zero))
      obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hpow.continuousOn
      refine ⟨C + max B 0 * D + 1, by positivity, ?_⟩
      intro s hs z hz
      have hraised : (pnatDilate (primePNat p) z).im ∈ Icc ((p.1 : ℝ) * a) ((p.1 : ℝ) * b) := by
        rw [pnatDilate_prime, dilate_im]
        exact ⟨mul_le_mul_of_nonneg_left hz.1 hp.le, mul_le_mul_of_nonneg_left hz.2 hp.le⟩
      rw [completedList_cons]
      split_ifs
      · exact (hbC s hs _ hraised).trans (by
          have hn : 0 ≤ max B 0 * D := mul_nonneg (le_max_right B 0) hD.le
          linarith)
      · calc
          ‖completedList (oldformTerms L s) s (pnatDilate (primePNat p) z) -
              (p.1 : ℂ) ^ (-s) * completedList (oldformTerms L s) s z‖ ≤
            ‖completedList (oldformTerms L s) s (pnatDilate (primePNat p) z)‖ +
              ‖(p.1 : ℂ) ^ (-s)‖ * ‖completedList (oldformTerms L s) s z‖ := by
                exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])
          _ ≤ C + max B 0 * D := add_le_add (hbC s hs _ hraised)
            (mul_le_mul ((hB s hs).trans (le_max_left B 0)) (hbD s hs z hz)
              (norm_nonneg _) (le_max_right B 0))
          _ ≤ C + max B 0 * D + 1 := by linarith

/-- The actual exceptional set gives an open regular domain. -/
theorem completedRegularDomain_isOpen (N : ℕ) : IsOpen (completedRegularDomain N) := by
  have hn : Continuous (oldformNormalization (canonicalPrimeList N)) :=
    continuous_iff_continuousAt.mpr (fun s =>
      (oldformNormalization_analyticAt (canonicalPrimeList N) s).continuousAt)
  change IsOpen (({0} : Set ℂ)ᶜ ∩ (({1} : Set ℂ)ᶜ ∩
    oldformNormalization (canonicalPrimeList N) ⁻¹' ({0} : Set ℂ)ᶜ))
  exact isClosed_singleton.isOpen_compl.inter
    (isClosed_singleton.isOpen_compl.inter (isClosed_singleton.isOpen_compl.preimage hn))
/-- Every genuine regular parameter, including one half, admits an actual
closed regular disk whose boundary avoids the removable central point. -/
theorem exists_regular_parameter_disk (N : ℕ) (u : ℂ)
    (hu : u ∈ completedRegularDomain N) :
    ∃ R : ℝ, 0 < R ∧ closedBall u R ⊆ completedRegularDomain N ∧
      ∀ v ∈ sphere u R, v ≠ 1 / 2 := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (completedRegularDomain_isOpen N) u hu
  have hclosed : ∀ R : ℝ, R ≤ ε / 2 → closedBall u R ⊆ completedRegularDomain N := by
    intro R hR v hv
    apply hsub
    apply mem_ball.mpr
    exact (mem_closedBall.mp hv).trans_lt (by linarith)
  by_cases hhalf : u = 1 / 2
  · refine ⟨ε / 2, half_pos hε, hclosed _ le_rfl, ?_⟩
    intro v hv he
    rw [hhalf, he] at hv
    have hv' := mem_sphere.mp hv
    simp only [dist_self] at hv'
    linarith
  · have hd : 0 < dist u (1 / 2 : ℂ) := dist_pos.mpr hhalf
    let R := min (ε / 2) (dist u (1 / 2 : ℂ) / 2)
    have hR : 0 < R := lt_min (half_pos hε) (half_pos hd)
    refine ⟨R, hR, hclosed R (min_le_left _ _), ?_⟩
    intro v hv he
    have hv' := mem_sphere.mp hv
    rw [he, dist_comm] at hv'
    have hr := min_le_right (ε / 2) (dist u (1 / 2 : ℂ) / 2)
    change R ≤ dist u (1 / 2 : ℂ) / 2 at hr
    linarith
/-- The actual all-level Euler denominator remains explicit and is bounded
away from zero on the compact regular parameter set by continuity. -/
theorem exists_completedLevel_compact_height_bound (N : ℕ) (K : Set ℂ)
    (hK : IsCompact K) (hregular : K ⊆ completedRegularDomain N)
    (hhalf : ∀ s ∈ K, s ≠ 1 / 2) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ z : UpperHalfPlane, z.im ∈ Icc a b →
      ‖completedLevelOldform N s z‖ ≤ C := by
  obtain ⟨C, hC, hbC⟩ := completedList_compact_bound K hK
    (fun s hs => ⟨(hregular hs).1, (hregular hs).2.1, hhalf s hs⟩)
    (canonicalPrimeList N) ha hab
  have hd : ContinuousOn (fun s => (oldformNormalization (canonicalPrimeList N) s)⁻¹) K := by
    intro s hs
    exact ((oldformNormalization_analyticAt (canonicalPrimeList N) s).continuousAt.inv₀
      (hregular hs).2.2).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hd
  refine ⟨C * max B 0 + 1, by positivity, ?_⟩
  intro s hs z hz
  calc
    ‖completedLevelOldform N s z‖ =
        ‖completedList (oldformTerms (canonicalPrimeList N) s) s z‖ *
          ‖(oldformNormalization (canonicalPrimeList N) s)⁻¹‖ := by
      simp only [completedLevelOldform, completedOldformNumerator, completedList, div_eq_mul_inv, norm_mul]
    _ ≤ C * max B 0 := mul_le_mul (hbC s hs z hz)
      ((hB s hs).trans (le_max_left B 0)) (norm_nonneg _) hC.le
    _ ≤ C * max B 0 + 1 := by linarith

/-- A disk bound for the ORIGINAL native level-N completed field. No
parameter derivative bound, integral identity or central raw formula is
assumed. -/
theorem exists_completedLevel_disk_height_bound (N : ℕ) (u : ℂ) {R a b : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hab : a ≤ b)
    (hregular : closedBall u R ⊆ completedRegularDomain N)
    (hcircle : ∀ s ∈ sphere u R, s ≠ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ closedBall u R, ∀ z : UpperHalfPlane,
      z.im ∈ Icc a b → ‖completedLevelOldform N s z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_completedLevel_compact_height_bound N (sphere u R)
    (isCompact_sphere u R) (sphere_subset_closedBall.trans hregular) hcircle ha hab
  refine ⟨C, hC, ?_⟩
  intro s hs z hz
  have hd : DifferentiableOn ℂ (fun w => completedLevelOldform N w z) (completedRegularDomain N) :=
    (completedLevelOldform_analyticOnNhd N z).differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hd.diffContOnCl_ball hregular)
  · intro w hw
    rw [frontier_ball u hR.ne'] at hw
    exact hb w hw z hz
  · rwa [closure_ball u hR.ne']

end
end ImbalancedChen.Part3.CompletedAllLevelCompactParameterValues20261026b



