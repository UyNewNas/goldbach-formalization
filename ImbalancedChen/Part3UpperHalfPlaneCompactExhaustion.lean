import ImbalancedChen.Part3Gamma0CompletedGradientRestriction

/-!
# Explicit compact exhaustion of the actual upper half-plane

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual sets |re z|<=n and 1/(n+1)<=im z<=n+1 are compact,
measurable, monotone and cover H. Compactness uses a genuine positive
closed rectangle embedded in the complex plane; the lower height bound
keeps the entire rectangle inside H. Together with the proved restriction
coherence, the actual completed local gradients on this exhaustion agree
on every smaller compact set. No global L2 or regularity claim is made.
-/

namespace ImbalancedChen.Part3.UpperHalfPlaneCompactExhaustion20261025a
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
open ImbalancedChen.Part3.Gamma0CompactCoreGradient20261025a
open ImbalancedChen.Part3.Gamma0EnergyCompactGradientExtension20261025a
open ImbalancedChen.Part3.Gamma0CompletedGradientRestriction20261025a

def hyperbolicCompactExhaustion (n : ℕ) : Set UpperHalfPlane :=
  {z | z.re ∈ Icc (-(n : ℝ)) (n : ℝ) ∧
    z.im ∈ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)}

theorem mem_hyperbolicCompactExhaustion_iff (n : ℕ) (z : UpperHalfPlane) :
    z ∈ hyperbolicCompactExhaustion n ↔
      |z.re| ≤ (n : ℝ) ∧ 1 / ((n : ℝ) + 1) ≤ z.im ∧ z.im ≤ (n : ℝ) + 1 := by
  change (- (n : ℝ) ≤ z.re ∧ z.re ≤ (n : ℝ)) ∧
      (1 / ((n : ℝ) + 1) ≤ z.im ∧ z.im ≤ (n : ℝ) + 1) ↔ _
  rw [← abs_le]

theorem hyperbolicCompactExhaustion_isCompact (n : ℕ) :
    IsCompact (hyperbolicCompactExhaustion n) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  have heq : ((↑) : UpperHalfPlane → ℂ) '' hyperbolicCompactExhaustion n =
      (fun p : ℝ × ℝ => (⟨p.1,p.2⟩ : ℂ)) ''
        (Icc (-(n : ℝ)) (n : ℝ) ×ˢ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨(z.re,z.im),hz,?_⟩
      ext <;> rfl
    · rintro ⟨p,hp,rfl⟩
      have hlower : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr (by positivity)
      have hpheight : 0 < p.2 := hlower.trans_le hp.2.1
      exact ⟨⟨⟨p.1,p.2⟩,hpheight⟩,hp,rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

theorem hyperbolicCompactExhaustion_measurableSet (n : ℕ) :
    MeasurableSet (hyperbolicCompactExhaustion n) :=
  (hyperbolicCompactExhaustion_isCompact n).measurableSet

theorem hyperbolicCompactExhaustion_mono : Monotone hyperbolicCompactExhaustion := by
  intro m n hmn z hz
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hlow : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (add_le_add_right hmnR 1)
  exact ⟨⟨(neg_le_neg hmnR).trans hz.1.1,hz.1.2.trans hmnR⟩,
    ⟨hlow.trans hz.2.1,hz.2.2.trans (add_le_add_right hmnR 1)⟩⟩

theorem exists_mem_hyperbolicCompactExhaustion (z : UpperHalfPlane) :
    ∃ n : ℕ, z ∈ hyperbolicCompactExhaustion n := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max |z.re| (max z.im (1 / z.im)))
  have hx : |z.re| < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hy : z.im < (n : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hinv : 1 / z.im < (n : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hn
  have hprod : 1 < (n : ℝ) * z.im := (div_lt_iff₀ z.im_pos).mp hinv
  apply (mem_hyperbolicCompactExhaustion_iff n z).mpr
  refine ⟨hx.le,?_,by linarith⟩
  apply (div_le_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).mpr
  nlinarith [z.im_pos]

theorem iUnion_hyperbolicCompactExhaustion :
    (⋃ n : ℕ, hyperbolicCompactExhaustion n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact Set.mem_iUnion.mpr (exists_mem_hyperbolicCompactExhaustion z)

/-- Genuine coherence of the actual energy-completion gradient vectors
on this explicit countable compact exhaustion. -/
theorem completedGradient_exhaustion_coherent (N : ℕ) [NeZero N] {m n : ℕ} (hmn : m ≤ n)
    (e : EnergyCompletion N) :
    completedCompactGradient N (hyperbolicCompactExhaustion_isCompact m) e =
      compactGradientRestriction (hyperbolicCompactExhaustion_mono hmn)
        (completedCompactGradient N (hyperbolicCompactExhaustion_isCompact n) e) :=
  completedCompactGradient_restriction_apply N (hyperbolicCompactExhaustion_isCompact m)
    (hyperbolicCompactExhaustion_isCompact n) (hyperbolicCompactExhaustion_mono hmn) e

end
end ImbalancedChen.Part3.UpperHalfPlaneCompactExhaustion20261025a
