import ImbalancedChen.ActualPrimeBoxTestFunctions
import ImbalancedChen.ActualRosserInitialResidualSaving
import ImbalancedChen.MovingWeightTransport

/-!
# An actual residual-density saving integrated over a prime cube

The sum uses the literal target-linked prime tuple carrier, its positive
reciprocal-prime mass, the actual last coordinate as cutoff, and the real
quotient level `N^lambda / (prod p)`. The ordinary residual densities are
the same coefficients whose compact limits have already been proved.
Those limits supply the uniform summand error here; no distribution,
uniform-error or integral-limit premise is assumed.

The cube has no ordering or parent-admission filter. Repeated coordinates
are allowed. This theorem therefore does not identify a complete eighth
frontier, an own-cube gate, or a certified manuscript saving domain.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open scoped BigOperators

/-- The exact rational saving profile before its prime-prefix mass. -/
def primeBoxInitialSavingProfile {d : ℕ} (lambdaOld lambdaNew : ℝ)
    (t : Fin d → ℝ) : ℝ :=
  4 * (lambdaNew - lambdaOld) /
    ((lambdaOld - ∑ i, t i) * (lambdaNew - ∑ i, t i))

/-- The actual normalized difference at the tuple's own product and last
prime. The enumeration cap for the residual sieve is explicit. -/
def actualPrimeTupleInitialSaving {k : ℕ} (N cap : ℕ)
    (lambdaOld lambdaNew : ℝ) (p : Fin (k + 1) → ℕ) : ℝ :=
  (actualSmallRosserPlusDensity N cap (p (Fin.last k) : ℝ)
      ((N : ℝ) ^ lambdaOld / (∏ i, p i : ℕ)) -
    actualSmallRosserPlusDensity N cap (p (Fin.last k) : ℝ)
      ((N : ℝ) ^ lambdaNew / (∏ i, p i : ℕ))) *
        Real.log (N : ℝ) / singularSeries N

/-- A genuine arithmetic sum, with no asymptotic profile in its definition. -/
def actualPrimeBoxInitialSavingSum (k N cap : ℕ) (a b lambdaOld lambdaNew : ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
    (∏ i, 1 / ((p i : ℝ) - 1)) * actualPrimeTupleInitialSaving N cap lambdaOld lambdaNew p

/-- All logarithmic coordinates together recover the actual tuple product;
no distinctness or ordering is needed for this identity. -/
theorem actualPrimeTupleLog_sum_prod {d N : ℕ} (p : Fin d → ℕ)
    (hp : ∀ i, 0 < p i) :
    (∑ i, actualPrimeTupleLog N p i) =
      Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ) := by
  unfold actualPrimeTupleLog
  rw [← Finset.sum_div]
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin d)), (p i : ℝ) ≠ 0 := by
    intro i _
    exact_mod_cast (hp i).ne'
  rw [← Real.log_prod hne, ← Nat.cast_prod]

private theorem initialSaving_cube_parameters {k : ℕ} {a b lambdaOld lambdaNew : ℝ}
    (ha : 0 < a) (hold : ((k : ℝ) + 2) * b < lambdaOld)
    (hnew : lambdaNew ≤ ((k : ℝ) + 4) * a)
    {t : Fin (k + 1) → ℝ}
    (ht : t ∈ Set.univ.pi (fun _ : Fin (k + 1) => Set.Icc a b))
    {lambda : ℝ} (hl : lambdaOld ≤ lambda) (hu : lambda ≤ lambdaNew) :
    0 < t (Fin.last k) ∧ t (Fin.last k) < lambda - ∑ i, t i ∧
      lambda - ∑ i, t i ≤ 3 * t (Fin.last k) := by
  have hlo : ((k : ℝ) + 1) * a ≤ ∑ i, t i := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin (k + 1) => a) (g := t)
      (fun i _ => (ht i (Set.mem_univ _)).1)
    simpa using hh
  have hhi : (∑ i, t i) ≤ ((k : ℝ) + 1) * b := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (f := t) (g := fun _ : Fin (k + 1) => b)
      (fun i _ => (ht i (Set.mem_univ _)).2)
    simpa using hh
  have htlast := ht (Fin.last k) (Set.mem_univ _)
  exact ⟨ha.trans_le htlast.1, by nlinarith [htlast.2], by nlinarith [htlast.1]⟩

/-- The stated finite cube inequalities keep both denominators strictly
positive on its compact closure, so the rational profile is continuous. -/
theorem continuousOn_primeBoxInitialSavingProfile {k : ℕ}
    {a b lambdaOld lambdaNew : ℝ} (ha : 0 < a)
    (horder : lambdaOld < lambdaNew)
    (hold : ((k : ℝ) + 2) * b < lambdaOld)
    (hnew : lambdaNew ≤ ((k : ℝ) + 4) * a) :
    ContinuousOn (primeBoxInitialSavingProfile lambdaOld lambdaNew)
      (Set.univ.pi (fun _ : Fin (k + 1) => Set.Icc a b)) := by
  have hs : Continuous (fun t : Fin (k + 1) → ℝ => ∑ i, t i) := by fun_prop
  unfold primeBoxInitialSavingProfile
  apply continuousOn_const.div
    ((continuousOn_const.sub hs.continuousOn).mul (continuousOn_const.sub hs.continuousOn))
  intro t ht
  have ho := initialSaving_cube_parameters ha hold hnew ht le_rfl horder.le
  have hn := initialSaving_cube_parameters ha hold hnew ht horder.le le_rfl
  exact mul_ne_zero (ho.1.trans ho.2.1).ne' (hn.1.trans hn.2.1).ne'

/-- The same proved ordinary-density threshold applies to every actual
tuple in the cube and every covering residual enumeration cap. -/
theorem exists_actualPrimeBoxInitialSaving_uniform_threshold
    (k : ℕ) (a b lambdaOld lambdaNew : ℝ) (ha : 0 < a)
    (horder : lambdaOld < lambdaNew)
    (hold : ((k : ℝ) + 2) * b < lambdaOld)
    (hnew : lambdaNew ≤ ((k : ℝ) + 4) * a)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
        |actualPrimeTupleInitialSaving N cap lambdaOld lambdaNew p -
          primeBoxInitialSavingProfile lambdaOld lambdaNew (actualPrimeTupleLog N p)| < eta := by
  let C : Set (Fin (k + 1) → ℝ) := Set.univ.pi (fun _ => Set.Icc a b)
  let F : ℝ → (Fin (k + 1) → ℝ) → ℝ × ℝ :=
    fun lambda t => (lambda - ∑ i, t i, t (Fin.last k))
  let T : Set (ℝ × ℝ) := F lambdaOld '' C ∪ F lambdaNew '' C
  have hC : IsCompact C := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hF (lambda : ℝ) : Continuous (F lambda) := by dsimp [F]; fun_prop
  have hT : IsCompact T := (hC.image (hF lambdaOld)).union (hC.image (hF lambdaNew))
  have hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2 := by
    intro p hp
    rcases hp with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact initialSaving_cube_parameters ha hold hnew ht le_rfl horder.le
    · exact initialSaving_cube_parameters ha hold hnew ht horder.le le_rfl
  obtain ⟨N₀, hN₀, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold T hT hparam eta heta
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap p hp
  have hN1 : 1 < N := by omega
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have ht : actualPrimeTupleLog N p ∈ C := by
    have hh := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
    exact fun i _ => ⟨(mem_logPrimeBox.mp hh i).1, (mem_logPrimeBox.mp hh i).2.le⟩
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hy : (0 : ℝ) < p (Fin.last k) := by exact_mod_cast hpos (Fin.last k)
  have hdict (lambda : ℝ) :
      actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p (Fin.last k) : ℝ) lambda =
        F lambda (actualPrimeTupleLog N p) := by
    change (lambda - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ),
        actualPrimeTupleLog N p (Fin.last k)) =
      (lambda - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p (Fin.last k))
    rw [actualPrimeTupleLog_sum_prod p hpos]
  have ho : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
      (p (Fin.last k) : ℝ) lambdaOld ∈ T := by
    rw [hdict]
    exact Or.inl ⟨_, ht, rfl⟩
  have hn : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
      (p (Fin.last k) : ℝ) lambdaNew ∈ T := by
    rw [hdict]
    exact Or.inr ⟨_, ht, rfl⟩
  have hh := hbound N hN hEven _ _ lambdaOld lambdaNew hP hy ho hn cap
    ((hpi (Fin.last k)).2.2.2.le.trans hcap)
  simpa only [actualPrimeTupleInitialSaving, primeBoxInitialSavingProfile,
    actualPrimeTupleLog_sum_prod p hpos] using hh

/-- Actual normalized residual savings converge to the genuine weighted
Lebesgue integral. The target is positive and even; the cap sequence may
be arbitrary provided it eventually covers `N^b`. There is no ordering
filter on the prime cube and no ancestor-admission premise. -/
theorem tendsto_actualPrimeBoxInitialSavingSum_cube
    (k : ℕ) (a b lambdaOld lambdaNew : ℝ) (ha : 0 < a) (hab : a < b)
    (horder : lambdaOld < lambdaNew)
    (hold : ((k : ℝ) + 2) * b < lambdaOld)
    (hnew : lambdaNew ≤ ((k : ℝ) + 4) * a)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualPrimeBoxInitialSavingSum k N (cap N) a b lambdaOld lambdaNew)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∫ t in logPrimeBox (fun _ : Fin (k + 1) => a) (fun _ => b),
        primeBoxInitialSavingProfile lambdaOld lambdaNew t * ∏ i, 1 / t i)) := by
  let l : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}
  let T (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b)
  let w (_N : ℕ) (p : Fin (k + 1) → ℕ) := ∏ i, 1 / ((p i : ℝ) - 1)
  let f (N : ℕ) (p : Fin (k + 1) → ℕ) :=
    actualPrimeTupleInitialSaving N (cap N) lambdaOld lambdaNew p
  let g (N : ℕ) (p : Fin (k + 1) → ℕ) :=
    primeBoxInitialSavingProfile lambdaOld lambdaNew (actualPrimeTupleLog N p)
  have hmasslimit := (tendsto_actualPrimeBoxMass (fun _ : Fin (k + 1) => a)
    (fun _ => b) (fun _ => ha) (fun _ => hab)).mono_left (show l ≤ atTop from inf_le_left)
  obtain ⟨M, hM, hmass⟩ := exists_eventually_bounded_mass_of_tendsto hmasslimit
  have hw : ∀ᶠ N in l, ∀ p ∈ T N, 0 ≤ w N p :=
    Filter.Eventually.of_forall (fun _ _ hp => actualPrimeBoxWeight_nonneg hp)
  have hfg : ∀ eta > 0, ∀ᶠ N in l, ∀ p ∈ T N, |f N p - g N p| < eta := by
    intro eta heta
    obtain ⟨N₀, _hN₀, hbound⟩ := exists_actualPrimeBoxInitialSaving_uniform_threshold
      k a b lambdaOld lambdaNew ha horder hold hnew eta heta
    have hNat : ∀ᶠ N in l, N₀ ≤ N :=
      (eventually_ge_atTop N₀).filter_mono inf_le_left
    have hEven : ∀ᶠ N in l, 0 < N ∧ Even N :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [hNat, hEven, hcap] with N hN hE hc
    exact hbound N hN hE.2 (cap N) hc
  have herror := tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w f g M hM hw hmass hfg
  have hfixed := (tendsto_actualPrimeBoxTestSum_cube ha hab
    (primeBoxInitialSavingProfile lambdaOld lambdaNew)
    (continuousOn_primeBoxInitialSavingProfile ha horder hold hnew)).mono_left
      (show l ≤ atTop from inf_le_left)
  have hh := herror.add hfixed
  simpa only [T, w, f, g, actualPrimeBoxTestSum, actualPrimeBoxInitialSavingSum,
    sub_add_cancel, zero_add] using hh

end

end ImbalancedChen
