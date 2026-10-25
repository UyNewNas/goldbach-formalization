import ImbalancedChen.ActualPrimeBoxOwnCubeResidual

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The compact quotient residual estimate is uniform in the physical level
as well as the prime tuple. Consequently any fixed bounded variable level
can replace a constant cap in the ARITHMETIC residual approximation. The
level need not be continuous: row walls do not affect this uniform error.

This proves convergence of the arithmetic replacement ERROR only. Weak
convergence of the variable gated profile, null control of actual row
walls, and the small-last-prime tail remain separate obligations.
-/

namespace ImbalancedChen.P1VariableOwnCubeResidualUniformity

noncomputable section
open Filter Topology Set MeasureTheory
open scoped Classical BigOperators

/-- One threshold controls every level in a compact interval and every
tuple in the positive cube, including both sides of its own-cube test. -/
theorem exists_actualPrimeTupleOwnCubeMinus_uniform_levels_threshold
    (k : ℕ) (a b lower upper : ℝ) (ha : 0 < a)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
        ∀ lambda ∈ Icc lower upper,
          |actualPrimeTupleOwnCubeMinus N cap lambda p -
            (if primeTupleOwnCubeForm (actualPrimeTupleLog N p) < lambda then
              primeTupleMinusProfile lambda (actualPrimeTupleLog N p) else 0)| < eta := by
  let C : Set (ℝ × (Fin (k + 1) → ℝ)) :=
    (Icc lower upper ×ˢ Set.univ.pi (fun _ => Icc a b)) ∩
      {q | primeTupleOwnCubeForm q.2 ≤ q.1}
  let F : (ℝ × (Fin (k + 1) → ℝ)) → ℝ × ℝ :=
    fun q => (q.1 - ∑ i, q.2 i, q.2 (Fin.last k))
  let T : Set (ℝ × ℝ) := F '' C
  have hform : Continuous (fun q : ℝ × (Fin (k + 1) → ℝ) =>
      primeTupleOwnCubeForm q.2) := by
    unfold primeTupleOwnCubeForm
    fun_prop
  have hC : IsCompact C :=
    (isCompact_Icc.prod (isCompact_univ_pi (fun _ => isCompact_Icc))).inter_right
      (isClosed_le hform continuous_fst)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hT : IsCompact T := hC.image hF
  have hparam : ∀ q ∈ T, 0 < q.2 ∧ 2 * q.2 ≤ q.1 := by
    rintro q ⟨⟨lambda, t⟩, ht, rfl⟩
    refine ⟨ha.trans_le (ht.1.2 _ (Set.mem_univ _)).1, ?_⟩
    have hh := ht.2
    change (∑ i, t i) + 2 * t (Fin.last k) ≤ lambda at hh
    dsimp [F]
    linarith
  obtain ⟨N₀, hN₀, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_quotient_compact_normalized_threshold
      T hT hparam eta heta
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap p hp lambda hlambda
  have hN1 : 1 < N := by omega
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have hdict := actualPrimeTupleOwnCube_iff hN1 p hpos lambda
  by_cases hg : primeTupleOwnCubeForm (actualPrimeTupleLog N p) < lambda
  · have hx := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
    have ht : (lambda, actualPrimeTupleLog N p) ∈ C :=
      ⟨⟨hlambda, fun i _ =>
        ⟨(mem_logPrimeBox.mp hx i).1, (mem_logPrimeBox.mp hx i).2.le⟩⟩, hg.le⟩
    have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
      exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
    have hy : (0 : ℝ) < p (Fin.last k) := by exact_mod_cast hpos (Fin.last k)
    have hparams : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
        (p (Fin.last k) : ℝ) lambda = F (lambda, actualPrimeTupleLog N p) := by
      change (lambda - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ),
          actualPrimeTupleLog N p (Fin.last k)) =
        (lambda - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p (Fin.last k))
      rw [actualPrimeTupleLog_sum_prod p hpos]
    have hh := hbound N hN hEven _ _ lambda hP hy
      (by rw [hparams]; exact Set.mem_image_of_mem F ht) cap
      ((hpi (Fin.last k)).2.2.2.le.trans hcap)
    rw [actualPrimeTupleOwnCubeMinus, if_pos (hdict.mpr hg), if_pos hg,
      primeTupleMinusProfile_of_ownCube
        (ha.trans_le (ht.1.2 _ (Set.mem_univ _)).1) hg.le]
    simpa only [hparams, F] using hh
  · simp only [actualPrimeTupleOwnCubeMinus, if_neg (mt hdict.mp hg), if_neg hg,
      sub_self, abs_zero]
    exact heta

/-- A fixed bounded profile is evaluated at each tuple's exact log point. -/
def actualPrimeBoxVariableOwnCubeMinusSum (k N cap : ℕ) (a b : ℝ)
    (profile : (Fin (k + 1) → ℝ) → ℝ) (R : Set (Fin (k + 1) → ℝ)) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ R then
        actualPrimeTupleOwnCubeMinus N cap (profile (actualPrimeTupleLog N p)) p else 0)

/-- No continuity of the profile or regularity of R is assumed. Uniform
compact quotient control and bounded actual prime mass prove this error
estimate; the strict gate is the same in both summands. -/
theorem tendsto_actualPrimeBoxVariableOwnCubeMinus_error
    (k : ℕ) (a b lower upper : ℝ) (ha : 0 < a) (hab : a < b)
    (profile : (Fin (k + 1) → ℝ) → ℝ)
    (hprofile : ∀ t ∈ logPrimeBox (fun _ => a) (fun _ => b),
      profile t ∈ Icc lower upper)
    (R : Set (Fin (k + 1) → ℝ)) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualPrimeBoxVariableOwnCubeMinusSum k N (cap N) a b profile R -
        actualPrimeBoxTestSum N (fun _ : Fin (k + 1) => a) (fun _ => b)
          (fun t => if t ∈ R then
            (if primeTupleOwnCubeForm t < profile t then
              primeTupleMinusProfile (profile t) t else 0) else 0))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let l : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}
  let T (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b)
  let w (_N : ℕ) (p : Fin (k + 1) → ℕ) := ∏ i, 1 / ((p i : ℝ) - 1)
  let f (N : ℕ) (p : Fin (k + 1) → ℕ) :=
    if actualPrimeTupleLog N p ∈ R then
      actualPrimeTupleOwnCubeMinus N (cap N) (profile (actualPrimeTupleLog N p)) p else 0
  let g (N : ℕ) (p : Fin (k + 1) → ℕ) :=
    if actualPrimeTupleLog N p ∈ R then
      (if primeTupleOwnCubeForm (actualPrimeTupleLog N p) < profile (actualPrimeTupleLog N p)
        then primeTupleMinusProfile (profile (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p)
        else 0) else 0
  have hmasslimit := (tendsto_actualPrimeBoxMass (fun _ : Fin (k + 1) => a)
    (fun _ => b) (fun _ => ha) (fun _ => hab)).mono_left (show l ≤ atTop from inf_le_left)
  obtain ⟨M, hM, hmass⟩ := exists_eventually_bounded_mass_of_tendsto hmasslimit
  have hw : ∀ᶠ N in l, ∀ p ∈ T N, 0 ≤ w N p :=
    Filter.Eventually.of_forall (fun _ _ hp => actualPrimeBoxWeight_nonneg hp)
  have hfg : ∀ eta > 0, ∀ᶠ N in l, ∀ p ∈ T N, |f N p - g N p| < eta := by
    intro eta heta
    obtain ⟨N₀, hN₀, hbound⟩ :=
      exists_actualPrimeTupleOwnCubeMinus_uniform_levels_threshold
        k a b lower upper ha eta heta
    have hNat : ∀ᶠ N in l, N₀ ≤ N :=
      (eventually_ge_atTop N₀).filter_mono inf_le_left
    have hEven : ∀ᶠ N in l, 0 < N ∧ Even N :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [hNat, hEven, hcap] with N hN hE hc p hp
    have hN1 : 1 < N := by omega
    have hx := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
    dsimp [f, g]
    by_cases hR : actualPrimeTupleLog N p ∈ R
    · simpa only [if_pos hR] using
        hbound N hN hE.2 (cap N) hc p hp (profile (actualPrimeTupleLog N p))
          (hprofile _ hx)
    · simpa only [if_neg hR, sub_self, abs_zero] using heta
  exact tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w f g M hM hw hmass hfg

end
end ImbalancedChen.P1VariableOwnCubeResidualUniformity
