import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral

/-!
# A common-cube integral for actual continuously varying minimum caps

The two continuous cap functions may cross inside the cube. The arithmetic
sum uses their literal minimum at the actual logarithmic prime tuple. One
legal compact parameter set is constructed for all three quotient levels;
the actual residual-density threshold and the existing prime-box transport
then prove convergence to the integral of the pointwise minimum of the two
rational saving profiles. No target limit or numerical saving is assumed.

The last two theorems retain the same integrand on every owned half-open
mesh cell, and give directed cell enclosures weighted by the exact product
of logarithms. They never commute integral with minimum.

This is a common-cube supplier. Binding the original 22 adopted policy
cells and proving their directed profile bounds remain separate work.
This source is intentionally standalone and does not require installing
the sibling source-only P2CausalMinSaving module first.
-/

namespace ImbalancedChen.P2MinSavingCellIntegral

noncomputable section

open Filter Topology Set MeasureTheory
open scoped Classical BigOperators

def cubeClosure (d : ℕ) (a b : ℝ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc a b)

def minSavingProfile {d : ℕ} (old : ℝ) (left right : (Fin d → ℝ) → ℝ)
    (t : Fin d → ℝ) : ℝ :=
  min (primeBoxInitialSavingProfile old (left t) t)
    (primeBoxInitialSavingProfile old (right t) t)

def actualVariableMinSavingSum (k N cap : ℕ) (a b old : ℝ)
    (left right : (Fin (k + 1) → ℝ) → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      actualPrimeTupleInitialSaving N cap old
        (min (left (actualPrimeTupleLog N p)) (right (actualPrimeTupleLog N p))) p

private theorem cube_parameters {k : ℕ} {a b old lambda : ℝ}
    (ha : 0 < a) (hold : ((k : ℝ) + 2) * b < old)
    (hlower : old ≤ lambda) (hupper : lambda ≤ ((k : ℝ) + 4) * a)
    {t : Fin (k + 1) → ℝ} (ht : t ∈ cubeClosure (k + 1) a b) :
    0 < t (Fin.last k) ∧ t (Fin.last k) < lambda - ∑ i, t i ∧
      lambda - ∑ i, t i ≤ 3 * t (Fin.last k) := by
  have hlo : ((k : ℝ) + 1) * a ≤ ∑ i, t i := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin (k + 1) => a) (g := t)
      (fun i _ => (ht i (Set.mem_univ _)).1)
    simpa using h
  have hhi : (∑ i, t i) ≤ ((k : ℝ) + 1) * b := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (f := t) (g := fun _ : Fin (k + 1) => b)
      (fun i _ => (ht i (Set.mem_univ _)).2)
    simpa using h
  have hlast := ht (Fin.last k) (Set.mem_univ _)
  exact ⟨ha.trans_le hlast.1, by nlinarith [hlast.2], by nlinarith [hlast.1]⟩

private theorem profile_eq_inverse {d : ℕ} (old new : ℝ) (t : Fin d → ℝ)
    (ho : 0 < old - ∑ i, t i) (hn : 0 < new - ∑ i, t i) :
    primeBoxInitialSavingProfile old new t =
      4 / (old - ∑ i, t i) - 4 / (new - ∑ i, t i) := by
  unfold primeBoxInitialSavingProfile
  field_simp [ho.ne', hn.ne'] <;> ring

private theorem profile_mono {d : ℕ} (old x y : ℝ) (t : Fin d → ℝ)
    (ho : 0 < old - ∑ i, t i) (hx : 0 < x - ∑ i, t i) (hxy : x ≤ y) :
    primeBoxInitialSavingProfile old x t ≤ primeBoxInitialSavingProfile old y t := by
  have hy : 0 < y - ∑ i, t i := hx.trans_le (sub_le_sub_right hxy _)
  have hi := one_div_le_one_div_of_le hx (sub_le_sub_right hxy (∑ i, t i))
  have h4 : 4 / (y - ∑ i, t i) ≤ 4 / (x - ∑ i, t i) := by
    convert mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
  rw [profile_eq_inverse old x t ho hx, profile_eq_inverse old y t ho hy]
  exact sub_le_sub_left h4 _

theorem profile_at_min {d : ℕ} (old : ℝ) (left right : (Fin d → ℝ) → ℝ)
    (t : Fin d → ℝ) (ho : 0 < old - ∑ i, t i)
    (hl : 0 < left t - ∑ i, t i) (hr : 0 < right t - ∑ i, t i) :
    primeBoxInitialSavingProfile old (min (left t) (right t)) t =
      minSavingProfile old left right t := by
  unfold minSavingProfile
  rcases le_total (left t) (right t) with h | h
  · rw [min_eq_left h, min_eq_left (profile_mono old _ _ t ho hl h)]
  · rw [min_eq_right h, min_eq_right (profile_mono old _ _ t ho hr h)]

private theorem continuousOn_variable_profile {k : ℕ} {a b old : ℝ}
    (ha : 0 < a) (hold : ((k : ℝ) + 2) * b < old)
    (cap : (Fin (k + 1) → ℝ) → ℝ)
    (hcont : ContinuousOn cap (cubeClosure (k + 1) a b))
    (hlegal : ∀ t ∈ cubeClosure (k + 1) a b,
      old ≤ cap t ∧ cap t ≤ ((k : ℝ) + 4) * a) :
    ContinuousOn (fun t => primeBoxInitialSavingProfile old (cap t) t)
      (cubeClosure (k + 1) a b) := by
  have hs : Continuous (fun t : Fin (k + 1) → ℝ => ∑ i, t i) := by fun_prop
  unfold primeBoxInitialSavingProfile
  apply (continuousOn_const.mul (hcont.sub continuousOn_const)).div
    ((continuousOn_const.sub hs.continuousOn).mul (hcont.sub hs.continuousOn))
  intro t ht
  have h := hlegal t ht
  have ho := cube_parameters ha hold le_rfl (h.1.trans h.2) ht
  have hn := cube_parameters ha hold h.1 h.2 ht
  exact mul_ne_zero (ho.1.trans ho.2.1).ne' (hn.1.trans hn.2.1).ne'

theorem continuousOn_minSavingProfile {k : ℕ} {a b old : ℝ}
    (ha : 0 < a) (hold : ((k : ℝ) + 2) * b < old)
    (left right : (Fin (k + 1) → ℝ) → ℝ)
    (hl : ContinuousOn left (cubeClosure (k + 1) a b))
    (hr : ContinuousOn right (cubeClosure (k + 1) a b))
    (hleft : ∀ t ∈ cubeClosure (k + 1) a b,
      old ≤ left t ∧ left t ≤ ((k : ℝ) + 4) * a)
    (hright : ∀ t ∈ cubeClosure (k + 1) a b,
      old ≤ right t ∧ right t ≤ ((k : ℝ) + 4) * a) :
    ContinuousOn (minSavingProfile old left right) (cubeClosure (k + 1) a b) := by
  exact continuous_min.comp_continuousOn
    ((continuousOn_variable_profile ha hold left hl hleft).prodMk
      (continuousOn_variable_profile ha hold right hr hright))

/-- A single compact legal set contains both crossing cap graphs and the
original parent graph. Its legality is derived from the cube inequalities. -/
theorem exists_common_legal_compact {k : ℕ} {a b old : ℝ}
    (ha : 0 < a) (hold : ((k : ℝ) + 2) * b < old)
    (left right : (Fin (k + 1) → ℝ) → ℝ)
    (hl : ContinuousOn left (cubeClosure (k + 1) a b))
    (hr : ContinuousOn right (cubeClosure (k + 1) a b))
    (hleft : ∀ t ∈ cubeClosure (k + 1) a b,
      old ≤ left t ∧ left t ≤ ((k : ℝ) + 4) * a)
    (hright : ∀ t ∈ cubeClosure (k + 1) a b,
      old ≤ right t ∧ right t ≤ ((k : ℝ) + 4) * a) :
    ∃ T : Set (ℝ × ℝ), IsCompact T ∧
      (∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2) ∧
      ∀ t ∈ cubeClosure (k + 1) a b,
        (old - ∑ i, t i, t (Fin.last k)) ∈ T ∧
          (min (left t) (right t) - ∑ i, t i, t (Fin.last k)) ∈ T := by
  let C := cubeClosure (k + 1) a b
  let F (cap : (Fin (k + 1) → ℝ) → ℝ) (t : Fin (k + 1) → ℝ) :=
    (cap t - ∑ i, t i, t (Fin.last k))
  let T := (F (fun _ => old) '' C ∪ F left '' C) ∪ F right '' C
  have hC : IsCompact C := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hs : Continuous (fun t : Fin (k + 1) → ℝ => ∑ i, t i) := by fun_prop
  have hF (cap : (Fin (k + 1) → ℝ) → ℝ) (hc : ContinuousOn cap C) :
      ContinuousOn (F cap) C :=
    (hc.sub hs.continuousOn).prodMk (continuous_apply (Fin.last k)).continuousOn
  have hT : IsCompact T :=
    ((hC.image_of_continuousOn (hF _ continuousOn_const)).union
      (hC.image_of_continuousOn (hF left hl))).union
        (hC.image_of_continuousOn (hF right hr))
  refine ⟨T, hT, ?_, ?_⟩
  · intro p hp
    rcases hp with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · exact cube_parameters ha hold le_rfl ((hleft t ht).1.trans (hleft t ht).2) ht
    · exact cube_parameters ha hold (hleft t ht).1 (hleft t ht).2 ht
    · exact cube_parameters ha hold (hright t ht).1 (hright t ht).2 ht
  · intro t ht
    refine ⟨Or.inl (Or.inl ⟨t, ht, rfl⟩), ?_⟩
    rcases le_total (left t) (right t) with h | h
    · exact Or.inl (Or.inr ⟨t, ht, by simp only [F, min_eq_left h]⟩)
    · exact Or.inr ⟨t, ht, by simp only [F, min_eq_right h]⟩

/-- Uniform error for the literal arithmetic summand with crossing caps. -/
theorem exists_actualVariableMinSaving_uniform_threshold
    (k : ℕ) (a b old : ℝ) (ha : 0 < a)
    (hold : ((k : ℝ) + 2) * b < old)
    (left right : (Fin (k + 1) → ℝ) → ℝ)
    (hl : ContinuousOn left (cubeClosure (k + 1) a b))
    (hr : ContinuousOn right (cubeClosure (k + 1) a b))
    (hleft : ∀ t ∈ cubeClosure (k + 1) a b,
      old ≤ left t ∧ left t ≤ ((k : ℝ) + 4) * a)
    (hright : ∀ t ∈ cubeClosure (k + 1) a b,
      old ≤ right t ∧ right t ≤ ((k : ℝ) + 4) * a)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
        |actualPrimeTupleInitialSaving N cap old
            (min (left (actualPrimeTupleLog N p)) (right (actualPrimeTupleLog N p))) p -
          minSavingProfile old left right (actualPrimeTupleLog N p)| < eta := by
  obtain ⟨T, hT, hparam, hmem⟩ :=
    exists_common_legal_compact ha hold left right hl hr hleft hright
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold T hT hparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap p hp
  have hN1 : 1 < N := by omega
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have ht : actualPrimeTupleLog N p ∈ cubeClosure (k + 1) a b := by
    have h := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
    exact fun i _ => ⟨(mem_logPrimeBox.mp h i).1, (mem_logPrimeBox.mp h i).2.le⟩
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hy : (0 : ℝ) < p (Fin.last k) := by exact_mod_cast hpos (Fin.last k)
  have hdict (lambda : ℝ) :
      actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p (Fin.last k) : ℝ) lambda =
        (lambda - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p (Fin.last k)) := by
    simp only [actualRosserQuotientParameters, actualPrimeTupleLog_sum_prod p hpos]
    rfl
  have hm := hmem _ ht
  have hOld : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
      (p (Fin.last k) : ℝ) old ∈ T := by
    rw [hdict]
    exact hm.1
  have hNew : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
      (p (Fin.last k) : ℝ)
      (min (left (actualPrimeTupleLog N p)) (right (actualPrimeTupleLog N p))) ∈ T := by
    rw [hdict]
    exact hm.2
  have hh := hbound N hN hEven _ _ old
    (min (left (actualPrimeTupleLog N p)) (right (actualPrimeTupleLog N p))) hP hy
    hOld hNew cap
    ((hpi (Fin.last k)).2.2.2.le.trans hcap)
  have ho := cube_parameters ha hold le_rfl ((hleft _ ht).1.trans (hleft _ ht).2) ht
  have hL := cube_parameters ha hold (hleft _ ht).1 (hleft _ ht).2 ht
  have hR := cube_parameters ha hold (hright _ ht).1 (hright _ ht).2 ht
  have heq := profile_at_min old left right (actualPrimeTupleLog N p)
    (ho.1.trans ho.2.1) (hL.1.trans hL.2.1) (hR.1.trans hR.2.1)
  rw [← heq]
  simpa only [actualPrimeTupleInitialSaving, primeBoxInitialSavingProfile,
    actualPrimeTupleLog_sum_prod p hpos] using hh

/-- The arithmetic limit has the integral of the minimum on the same cube.
The minimum cap is evaluated at each actual tuple, so its choice may vary
inside a mesh cell and as the actual prime tuple varies. -/
theorem tendsto_actualVariableMinSavingSum_cube
    (k : ℕ) (a b old : ℝ) (ha : 0 < a) (hab : a < b)
    (hold : ((k : ℝ) + 2) * b < old)
    (left right : (Fin (k + 1) → ℝ) → ℝ)
    (hl : ContinuousOn left (cubeClosure (k + 1) a b))
    (hr : ContinuousOn right (cubeClosure (k + 1) a b))
    (hleft : ∀ t ∈ cubeClosure (k + 1) a b,
      old ≤ left t ∧ left t ≤ ((k : ℝ) + 4) * a)
    (hright : ∀ t ∈ cubeClosure (k + 1) a b,
      old ≤ right t ∧ right t ≤ ((k : ℝ) + 4) * a)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N => actualVariableMinSavingSum k N (cap N) a b old left right)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∫ t in logPrimeBox (fun _ : Fin (k + 1) => a) (fun _ => b),
        minSavingProfile old left right t * ∏ i, 1 / t i)) := by
  let l : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}
  let T N := actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b)
  let w (_N : ℕ) (p : Fin (k + 1) → ℕ) := ∏ i, 1 / ((p i : ℝ) - 1)
  let f N (p : Fin (k + 1) → ℕ) := actualPrimeTupleInitialSaving N (cap N) old
    (min (left (actualPrimeTupleLog N p)) (right (actualPrimeTupleLog N p))) p
  let g N (p : Fin (k + 1) → ℕ) := minSavingProfile old left right (actualPrimeTupleLog N p)
  have hmasslimit := (tendsto_actualPrimeBoxMass (fun _ : Fin (k + 1) => a)
    (fun _ => b) (fun _ => ha) (fun _ => hab)).mono_left (show l ≤ atTop from inf_le_left)
  obtain ⟨M, hM, hmass⟩ := exists_eventually_bounded_mass_of_tendsto hmasslimit
  have hw : ∀ᶠ N in l, ∀ p ∈ T N, 0 ≤ w N p :=
    Filter.Eventually.of_forall (fun _ _ hp => actualPrimeBoxWeight_nonneg hp)
  have hfg : ∀ eta > 0, ∀ᶠ N in l, ∀ p ∈ T N, |f N p - g N p| < eta := by
    intro eta heta
    obtain ⟨N0, _, hbound⟩ := exists_actualVariableMinSaving_uniform_threshold
      k a b old ha hold left right hl hr hleft hright eta heta
    have hNat : ∀ᶠ N in l, N0 ≤ N := (eventually_ge_atTop N0).filter_mono inf_le_left
    have hEven : ∀ᶠ N in l, 0 < N ∧ Even N :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [hNat, hEven, hcap] with N hN hE hc
    exact hbound N hN hE.2 (cap N) hc
  have herror := tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w f g M hM hw hmass hfg
  have hfixed := (tendsto_actualPrimeBoxTestSum_cube ha hab
    (minSavingProfile old left right)
    (continuousOn_minSavingProfile ha hold left right hl hr hleft hright)).mono_left
      (show l ≤ atTop from inf_le_left)
  simpa only [T, w, f, g, actualPrimeBoxTestSum, actualVariableMinSavingSum,
    sub_add_cancel, zero_add] using herror.add hfixed

/-- Literal partition of the same minimum integrand, with Ico ownership.
No separate left/right integrals occur in this identity. -/
theorem integral_minSavingProfile_mesh {d : ℕ} {a b old : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ)
    (left right : (Fin d → ℝ) → ℝ)
    (hc : ContinuousOn (minSavingProfile old left right) (cubeClosure d a b)) :
    (∫ t in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
      minSavingProfile old left right t * ∏ i, 1 / t i) =
      ∑ j : Fin d → Fin (m + 1), ∫ t in logPrimeMeshCell a b m j,
        minSavingProfile old left right t * ∏ i, 1 / t i := by
  have hi := integrableOn_logPrimeBox_test_cube ha (minSavingProfile old left right) hc
  calc
    _ = ∫ t in ⋃ j : Fin d → Fin (m + 1), logPrimeMeshCell a b m j,
        minSavingProfile old left right t * ∏ i, 1 / t i := by
      rw [logPrimeMeshCells_union hab m]
    _ = _ := integral_iUnion_fintype (measurableSet_logPrimeMeshCell a b m)
      (fun j r hjr => logPrimeMeshCell_pairwiseDisjoint hab.le m
        (Set.mem_univ j) (Set.mem_univ r) hjr)
      (fun j => hi.mono_set (logPrimeMeshCell_subset_box hab m j))

/-- Directed enclosure of the integral of the pointwise minimum. A lower
cell bound must hold for both profiles; an upper cell bound needs either
one. The exact logarithmic cell mass keeps the original common domain. -/
theorem integral_minSavingProfile_cell_enclosure {d : ℕ} {a b old : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ)
    (left right : (Fin d → ℝ) → ℝ)
    (hc : ContinuousOn (minSavingProfile old left right) (cubeClosure d a b))
    (lower upper : (Fin d → Fin (m + 1)) → ℝ)
    (hlo : ∀ j t, t ∈ logPrimeMeshCell a b m j →
      lower j ≤ primeBoxInitialSavingProfile old (left t) t ∧
        lower j ≤ primeBoxInitialSavingProfile old (right t) t)
    (hhi : ∀ j t, t ∈ logPrimeMeshCell a b m j →
      primeBoxInitialSavingProfile old (left t) t ≤ upper j ∨
        primeBoxInitialSavingProfile old (right t) t ≤ upper j) :
    (∑ j : Fin d → Fin (m + 1), lower j *
      ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i)) ≤
      (∫ t in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
        minSavingProfile old left right t * ∏ i, 1 / t i) ∧
    (∫ t in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
      minSavingProfile old left right t * ∏ i, 1 / t i) ≤
      ∑ j : Fin d → Fin (m + 1), upper j *
        ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i) := by
  have hi := integrableOn_logPrimeBox_test_cube ha (minSavingProfile old left right) hc
  have hcell (j : Fin d → Fin (m + 1)) :
      lower j * ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i) ≤
        (∫ t in logPrimeMeshCell a b m j, minSavingProfile old left right t * ∏ i, 1 / t i) ∧
      (∫ t in logPrimeMeshCell a b m j, minSavingProfile old left right t * ∏ i, 1 / t i) ≤
        upper j * ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i) := by
    have hpos (i : Fin d) : 0 < logPrimeMeshLo a b m j i :=
      ha.trans_le (logPrimeMeshLoHi_bounds hab m j i).1
    have horder (i : Fin d) : logPrimeMeshLo a b m j i ≤ logPrimeMeshHi a b m j i :=
      (logPrimeMeshLoHi_bounds hab m j i).2.1.le
    have hInt := hi.mono_set (logPrimeMeshCell_subset_box hab m j)
    have hIntL := integrableOn_logPrimeBox_const_mul_one_div (lower j) _ _ hpos
    have hIntU := integrableOn_logPrimeBox_const_mul_one_div (upper j) _ _ hpos
    have hw : ∀ t ∈ logPrimeMeshCell a b m j, 0 ≤ ∏ i, 1 / t i := by
      intro t ht
      apply Finset.prod_nonneg
      intro i _
      exact one_div_nonneg.mpr ((hpos i).le.trans ((mem_logPrimeMeshCell.mp ht i).1))
    have hL := integral_mono_ae hIntL hInt (by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeMeshCell a b m j)] with t ht
      exact mul_le_mul_of_nonneg_right (le_min (hlo j t ht).1 (hlo j t ht).2) (hw t ht))
    have hU := integral_mono_ae hInt hIntU (by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeMeshCell a b m j)] with t ht
      have hm : minSavingProfile old left right t ≤ upper j := by
        rcases hhi j t ht with h | h
        · exact (min_le_left _ _).trans h
        · exact (min_le_right _ _).trans h
      exact mul_le_mul_of_nonneg_right hm (hw t ht))
    rw [integral_logPrimeBox_const_mul_one_div (lower j) _ _ hpos horder] at hL
    rw [integral_logPrimeBox_const_mul_one_div (upper j) _ _ hpos horder] at hU
    exact ⟨hL, hU⟩
  rw [integral_minSavingProfile_mesh ha hab m left right hc]
  exact ⟨Finset.sum_le_sum (fun j _ => (hcell j).1),
    Finset.sum_le_sum (fun j _ => (hcell j).2)⟩

/-- Uniform continuity supplies a finite directed enclosure without any
assumed cell saving bounds. Each sample is the pointwise minimum at that
cell's common lower corner; the same epsilon is paid against its exact
logarithmic mass on both sides. -/
theorem exists_minSavingProfile_mesh_enclosure {d : ℕ} {a b old : ℝ}
    (ha : 0 < a) (hab : a < b)
    (left right : (Fin d → ℝ) → ℝ)
    (hc : ContinuousOn (minSavingProfile old left right) (cubeClosure d a b))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m : ℕ,
      (∑ j : Fin d → Fin (m + 1),
        (minSavingProfile old left right (logPrimeMeshLo a b m j) - epsilon) *
          ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i)) ≤
        (∫ t in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
          minSavingProfile old left right t * ∏ i, 1 / t i) ∧
      (∫ t in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
        minSavingProfile old left right t * ∏ i, 1 / t i) ≤
        ∑ j : Fin d → Fin (m + 1),
          (minSavingProfile old left right (logPrimeMeshLo a b m j) + epsilon) *
            ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i) := by
  obtain ⟨m, hm⟩ := exists_logPrimeMesh_test_oscillation hab
    (minSavingProfile old left right) hc hepsilon
  refine ⟨m, ?_⟩
  apply integral_minSavingProfile_cell_enclosure ha hab m left right hc
    (fun j => minSavingProfile old left right (logPrimeMeshLo a b m j) - epsilon)
    (fun j => minSavingProfile old left right (logPrimeMeshLo a b m j) + epsilon)
  · intro j t ht
    have h := abs_le.mp (hm j t ht)
    have hlo : minSavingProfile old left right (logPrimeMeshLo a b m j) - epsilon ≤
        minSavingProfile old left right t := by linarith
    exact ⟨hlo.trans (min_le_left _ _), hlo.trans (min_le_right _ _)⟩
  · intro j t ht
    have h := abs_le.mp (hm j t ht)
    have hhi : minSavingProfile old left right t ≤
        minSavingProfile old left right (logPrimeMeshLo a b m j) + epsilon := by linarith
    rcases le_total (primeBoxInitialSavingProfile old (left t) t)
      (primeBoxInitialSavingProfile old (right t) t) with hlr | hrl
    · exact Or.inl (by simpa only [minSavingProfile, min_eq_left hlr] using hhi)
    · exact Or.inr (by simpa only [minSavingProfile, min_eq_right hrl] using hhi)

end

end ImbalancedChen.P2MinSavingCellIntegral
