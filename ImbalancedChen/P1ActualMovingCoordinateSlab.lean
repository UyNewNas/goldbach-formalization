import ImbalancedChen.P1ActualMovingPrimeIntervalEnvelope
import ImbalancedChen.P1ActualMovingAffineWallMass

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Closed one-coordinate slabs in the original target-deleted prime box.
The moving slab is clamped to [a,b]. Its half-open interval is bounded by
the genuine endpoint-uniform Euler estimate. Its closed upper prime atom
is separately retained and paid by 1/(N^a-1). The center is unrestricted:
the final bound is 2*eta/a + b*K/(a^2*log N) + 1/(N^a-1).
Thus any nonnegative shrinking width eta(N)->0 gives a uniform-in-center
arithmetic mass tending to zero. No continuity or center limit is assumed.
-/

namespace ImbalancedChen.P1ActualMovingCoordinateSlab

noncomputable section
open scoped Classical BigOperators Topology
open Filter P1ActualMovingPrimeIntervalEnvelope P1ActualMovingAffineWallMass
open P1OriginalFourthMovingPrimeIntervalBound

def bandTuples (N : ℕ) (a b lo hi : ℝ) : Finset (Fin 1 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ : Fin 1 => a) (fun _ => b)).filter
    (fun p => lo ≤ actualPrimeTupleLog N p 0 ∧ actualPrimeTupleLog N p 0 ≤ hi)

def bandMass (N : ℕ) (a b lo hi : ℝ) : ℝ :=
  ∑ p ∈ bandTuples N a b lo hi, tupleWeight p

def slabTuples (N : ℕ) (a b center eta : ℝ) : Finset (Fin 1 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ : Fin 1 => a) (fun _ => b)).filter
    (fun p => |actualPrimeTupleLog N p 0-center| ≤ eta)

def slabMass (N : ℕ) (a b center eta : ℝ) : ℝ :=
  ∑ p ∈ slabTuples N a b center eta, tupleWeight p

def envelope (K a b eta : ℝ) (N : ℕ) : ℝ :=
  2*eta/a + b*K/(a^2*Real.log (N : ℝ)) + 1/((N : ℝ)^a-1)

theorem slabMass_nonneg (N : ℕ) (a b center eta : ℝ) :
    0 ≤ slabMass N a b center eta := by
  apply Finset.sum_nonneg
  intro p hp
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- The closed upper face is an actual prime wall, not a null-set deletion. -/
theorem bandMass_le_halfOpen_add_atom (N : ℕ) (hN : 1 < N) (a b lo hi : ℝ)
    (hA : 1 < (N : ℝ)^a) :
    bandMass N a b lo hi ≤ actualPrimeReciprocalMass N lo hi + 1/((N : ℝ)^a-1) := by
  let A := actualPrimeBoxTuples N (fun _ : Fin 1 => lo) (fun _ => hi)
  let W := wallTuples N (fun _ : Fin 1 => a) (fun _ => b) (fun _ => 1) hi
  have hsub : bandTuples N a b lo hi ⊆ A ∪ W := by
    intro p hp
    obtain ⟨hpbox,hlo,hhi⟩ := Finset.mem_filter.mp hp
    have hpLog := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).1 hpbox
    by_cases hstrict : actualPrimeTupleLog N p 0 < hi
    · apply Finset.mem_union.mpr
      left
      apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).2
      refine ⟨hpLog.1,mem_logPrimeBox.mpr ?_⟩
      intro i
      have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact ⟨hlo,hstrict⟩
    · have heq : actualPrimeTupleLog N p 0 = hi := le_antisymm hhi (le_of_not_gt hstrict)
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨hpbox,?_⟩
      simpa only [affineValue,Fin.sum_univ_one,one_mul] using heq
  have hnonneg (p : Fin 1 → ℕ) (hp : p ∈ A ∪ W) : 0 ≤ tupleWeight p := by
    rcases Finset.mem_union.mp hp with hpa | hpw
    · exact actualPrimeBoxWeight_nonneg hpa
    · exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hpw).1
  have hsubsum : bandMass N a b lo hi ≤ ∑ p ∈ A ∪ W, tupleWeight p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hnot
    exact hnonneg p hp
  have hinter : 0 ≤ ∑ p ∈ A ∩ W, tupleWeight p := by
    apply Finset.sum_nonneg
    intro p hp
    exact actualPrimeBoxWeight_nonneg (Finset.mem_inter.mp hp).1
  have hunion : (∑ p ∈ A ∪ W, tupleWeight p) + (∑ p ∈ A ∩ W, tupleWeight p) =
      (∑ p ∈ A, tupleWeight p) + (∑ p ∈ W, tupleWeight p) := Finset.sum_union_inter
  have hAeq : (∑ p ∈ A, tupleWeight p) = actualPrimeReciprocalMass N lo hi := by
    change actualPrimeBoxMass N (fun _ : Fin 1 => lo) (fun _ => hi) = _
    rw [actualPrimeBoxMass_eq_prod]
    simp
  have hWeq : (∑ p ∈ W, tupleWeight p) =
      wallMass N (fun _ : Fin 1 => a) (fun _ => b) (fun _ => 1) hi := rfl
  have hW := wallMass_le (a := fun _ : Fin 1 => a) (b := fun _ => b)
    (v := fun _ => 1) hN (0 : Fin 1) (by norm_num) hA hi
  have hW' : (∑ p ∈ W, tupleWeight p) ≤ 1/((N : ℝ)^a-1) := by
    rw [hWeq]
    simpa using hW
  linarith

theorem bandMass_eq_zero_of_gt (N : ℕ) (a b lo hi : ℝ) (h : hi < lo) :
    bandMass N a b lo hi = 0 := by
  have hempty : bandTuples N a b lo hi = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro p hp
    have ht := (Finset.mem_filter.mp hp).2
    exact (not_le.mpr h) (ht.1.trans ht.2)
  simp only [bandMass,hempty,Finset.sum_empty]

theorem slabMass_le_clamped_band (N : ℕ) (hN : 1 < N) (a b center eta : ℝ) :
    slabMass N a b center eta ≤
      bandMass N a b (max a (center-eta)) (min b (center+eta)) := by
  have hsub : slabTuples N a b center eta ⊆
      bandTuples N a b (max a (center-eta)) (min b (center+eta)) := by
    intro p hp
    obtain ⟨hpbox,hslab⟩ := Finset.mem_filter.mp hp
    have hlog := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).1 hpbox
    have hbox := mem_logPrimeBox.mp hlog.2 (0 : Fin 1)
    have habs := abs_le.mp hslab
    apply Finset.mem_filter.mpr
    refine ⟨hpbox,max_le hbox.1 (by linarith),le_min hbox.2.le (by linarith)⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro p hp hnot
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- Endpoint-uniform estimate, including the retained closed prime atom. -/
theorem slabMass_le_envelope (K : ℝ) (hKpos : 0 ≤ K) (hK : IntervalBound K)
    (N : ℕ) (hN : 1 < N) (a b center eta : ℝ) (ha : 0 < a) (hab : a < b)
    (heta : 0 ≤ eta) (hA : 3 ≤ (N : ℝ)^a) :
    slabMass N a b center eta ≤ envelope K a b eta N := by
  let lo := max a (center-eta)
  let hi := min b (center+eta)
  have hAprime : 1 < (N : ℝ)^a := by linarith
  have hclamp := slabMass_le_clamped_band N hN a b center eta
  by_cases ho : lo ≤ hi
  · have hband := bandMass_le_halfOpen_add_atom N hN a b lo hi hAprime
    have hinterval := actual_mass_le_exponent_terms K hKpos hK N hN
      a b lo hi ha (le_max_left _ _) ho (min_le_left _ _) hA
    have hwidth : hi-lo ≤ 2*eta := by
      have h1 : center-eta ≤ lo := le_max_right _ _
      have h2 : hi ≤ center+eta := min_le_right _ _
      linarith
    have hmain := div_le_div_of_nonneg_right hwidth ha.le
    dsimp only [envelope]
    exact hclamp.trans (hband.trans (by linarith))
  · have hzero := bandMass_eq_zero_of_gt N a b lo hi (lt_of_not_ge ho)
    have hnonneg : 0 ≤ envelope K a b eta N := by
      have hn : (1 : ℝ) < N := by exact_mod_cast hN
      have hlog := (Real.log_pos hn).le
      have hb : 0 < b := ha.trans hab
      have hden : 0 < (N : ℝ)^a-1 := sub_pos.mpr hAprime
      unfold envelope
      positivity
    exact hclamp.trans (by rw [hzero]; exact hnonneg)

theorem exists_uniform_slab_envelope :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ), 1 < N →
      ∀ a b center eta : ℝ, 0 < a → a < b → 0 ≤ eta → 3 ≤ (N : ℝ)^a →
        slabMass N a b center eta ≤ envelope K a b eta N := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_reciprocal_interval_bound
  refine ⟨K,hK,?_⟩
  intro N hN a b center eta ha hab heta hA
  exact slabMass_le_envelope K (by linarith) hbound N hN a b center eta ha hab heta hA

theorem tendsto_envelope_zero (K a b : ℝ) (ha : 0 < a) (hab : a < b)
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => envelope K a b (eta N) N) atTop (𝓝 0) := by
  have hmain : Tendsto (fun N : ℕ => 2*eta N/a) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div] using (heta.const_mul 2).div_const a
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogInv := tendsto_inv_atTop_zero.comp hlog
  have herror : Tendsto (fun N : ℕ => b*K/(a^2*Real.log (N : ℝ))) atTop (𝓝 0) := by
    convert hlogInv.const_mul (b*K/a^2) using 1
    · funext N
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · simp
  have hatom : Tendsto (fun N : ℕ => 1/((N : ℝ)^a-1)) atTop (𝓝 0) := by
    simpa using tendsto_wallEnvelope_zero (fun _ : Fin 1 => a) (fun _ => b)
      (fun _ => ha) (fun _ => hab) (0 : Fin 1)
  simpa only [envelope,zero_add] using (hmain.add herror).add hatom

/-- The arithmetic threshold is uniform in every moving real center. -/
theorem exists_shrinkingSlab_uniform_threshold (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (eta : ℕ → ℝ) (heta0 : ∀ N, 0 ≤ eta N) (heta : Tendsto eta atTop (𝓝 0))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, M ≤ N → ∀ center : ℝ, slabMass N a b center (eta N) < eps := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_slab_envelope
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 3 ≤ (N : ℝ)^a ∧ envelope K a b (eta N) N < eps := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),hp.eventually (eventually_ge_atTop (3 : ℝ)),
      (tendsto_envelope_zero K a b ha hab eta heta).eventually (gt_mem_nhds heps)]
      with N hN hA hE
    exact ⟨hN,hA,hE⟩
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  refine ⟨max 2 M,le_max_left _ _,?_⟩
  intro N hN center
  obtain ⟨hN2,hA,hE⟩ := hM N ((le_max_right _ _).trans hN)
  exact (hbound N (by omega) a b center (eta N) ha hab (heta0 N) hA).trans_lt hE

theorem tendsto_slabMass_arbitrary_center (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (eta center : ℕ → ℝ) (heta0 : ∀ N, 0 ≤ eta N) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => slabMass N a b (center N) (eta N)) atTop (𝓝 0) := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_slab_envelope
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_envelope_zero K a b ha hab eta heta)
  · exact Filter.Eventually.of_forall (fun N => slabMass_nonneg N a b (center N) (eta N))
  · filter_upwards [eventually_ge_atTop (2 : ℕ),hp.eventually (eventually_ge_atTop (3 : ℝ))]
      with N hN hA
    exact hbound N (by omega) a b (center N) (eta N) ha hab (heta0 N) hA

end
end ImbalancedChen.P1ActualMovingCoordinateSlab
