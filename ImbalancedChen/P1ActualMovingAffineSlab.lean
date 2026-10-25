import ImbalancedChen.P1ActualMovingCoordinateSlab

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Actual finite prime-coordinate disintegration of a moving affine slab.
On each removeNth fiber, its nonzero coefficient v_j turns the slab into
a scalar prime interval of radius eta/abs(v_j), with an unrestricted center
depending on the remaining primes. The scalar endpoint-uniform bound is
therefore applicable before summing the fibers. Both the target deletion
and every original prime-box endpoint survive this disintegration.

The resulting envelope is the scalar closed-slab envelope times the true
remaining-coordinate box mass. It tends to zero for any nonnegative
eta(N)->0 and arbitrary center(N), with no center limit or prime-mean input.
-/

namespace ImbalancedChen.P1ActualMovingAffineSlab

noncomputable section
open scoped Classical BigOperators Topology
open Filter P1ActualMovingAffineWallMass P1ActualMovingPrimeIntervalEnvelope
open P1ActualMovingCoordinateSlab P1OriginalFourthMovingPrimeIntervalBound

def affineSlabTuples {d : ℕ} (N : ℕ) (a b v : Fin d → ℝ) (c eta : ℝ) :
    Finset (Fin d → ℕ) :=
  (actualPrimeBoxTuples N a b).filter
    (fun p => |affineValue v (actualPrimeTupleLog N p)-c| ≤ eta)

def affineSlabMass {d : ℕ} (N : ℕ) (a b v : Fin d → ℝ) (c eta : ℝ) : ℝ :=
  ∑ p ∈ affineSlabTuples N a b v c eta, tupleWeight p

def focus {k : ℕ} (j : Fin (k+1)) (p : Fin (k+1) → ℕ) : Fin 1 → ℕ := fun _ => p j

def tailValue {k : ℕ} (N : ℕ) (v : Fin (k+1) → ℝ) (j : Fin (k+1)) (q : Fin k → ℕ) : ℝ :=
  ∑ i, v (j.succAbove i)*actualPrimeTupleLog N q i

def fiberCenter {k : ℕ} (N : ℕ) (v : Fin (k+1) → ℝ) (j : Fin (k+1))
    (q : Fin k → ℕ) (c : ℝ) : ℝ := (c-tailValue N v j q)/(v j)

theorem affineSlabMass_nonneg {d : ℕ} (N : ℕ) (a b v : Fin d → ℝ) (c eta : ℝ) :
    0 ≤ affineSlabMass N a b v c eta := by
  apply Finset.sum_nonneg
  intro p hp
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

theorem affine_split_of_removeNth {k : ℕ} (N : ℕ) (v : Fin (k+1) → ℝ)
    (j : Fin (k+1)) (p : Fin (k+1) → ℕ) (q : Fin k → ℕ) (hp : j.removeNth p = q) :
    affineValue v (actualPrimeTupleLog N p) =
      v j*actualPrimeTupleLog N p j + tailValue N v j q := by
  have hsplit := Fin.add_sum_removeNth j (fun i => v i*actualPrimeTupleLog N p i)
  have hrest :
      (∑ i : Fin k, v (j.succAbove i)*actualPrimeTupleLog N p (j.succAbove i)) =
      tailValue N v j q := by
    apply Finset.sum_congr rfl
    intro i hi
    have he := congrFun hp i
    change p (j.succAbove i) = q i at he
    simp only [actualPrimeTupleLog,he]
  exact hsplit.symm.trans (by rw [hrest])

theorem abs_affine_center (v t R c : ℝ) (hv : v ≠ 0) :
    |v*t+R-c| = |v|*|t-(c-R)/v| := by
  rw [← abs_mul]
  congr 1
  field_simp [hv]
  ring

theorem fiber_slab_focus_mem {k N : ℕ} {a b v : Fin (k+1) → ℝ}
    (j : Fin (k+1)) (hv : v j ≠ 0) (q : Fin k → ℕ) (c eta : ℝ)
    {p : Fin (k+1) → ℕ} (hp : p ∈ affineSlabTuples N a b v c eta)
    (hdrop : j.removeNth p = q) :
    focus j p ∈ slabTuples N (a j) (b j) (fiberCenter N v j q c) (eta/|v j|) := by
  obtain ⟨hpbox,hslab⟩ := Finset.mem_filter.mp hp
  have hfocus : focus j p ∈ actualPrimeBoxTuples N (fun _ : Fin 1 => a j) (fun _ => b j) := by
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    exact mem_actualPrimeBoxTuples_iff.mp hpbox j
  rw [affine_split_of_removeNth N v j p q hdrop,abs_affine_center _ _ _ _ hv] at hslab
  apply Finset.mem_filter.mpr
  refine ⟨hfocus,?_⟩
  apply (div_le_iff₀ (abs_pos.mpr hv)).2
  simpa only [focus,actualPrimeTupleLog,fiberCenter,mul_comm] using hslab

/-- The scalar prime coordinate enumerates each member of a fixed fiber
once; no multiplicity or completion-count premise is supplied. -/
theorem focus_injOn_fiber {k : ℕ} (S : Finset (Fin (k+1) → ℕ))
    (j : Fin (k+1)) (q : Fin k → ℕ) :
    Set.InjOn (focus j) (S.filter (fun p => j.removeNth p = q)) := by
  intro p hp r hr heq
  have hpq := (Finset.mem_filter.mp hp).2
  have hrq := (Finset.mem_filter.mp hr).2
  have hj := congrFun heq (0 : Fin 1)
  change p j = r j at hj
  calc
    p = j.insertNth (p j) (j.removeNth p) := (Fin.insertNth_self_removeNth j p).symm
    _ = j.insertNth (r j) (j.removeNth r) := by rw [hj,hpq,hrq]
    _ = r := Fin.insertNth_self_removeNth j r

theorem fiber_weight_factor {k : ℕ} (S : Finset (Fin (k+1) → ℕ))
    (j : Fin (k+1)) (q : Fin k → ℕ) :
    (∑ p ∈ S.filter (fun p => j.removeNth p = q), tupleWeight p) =
      tupleWeight q*(∑ p ∈ S.filter (fun p => j.removeNth p = q), tupleWeight (focus j p)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [tupleWeight_removeNth j p,(Finset.mem_filter.mp hp).2]
  simp only [tupleWeight,focus,Fin.prod_univ_one]
  ring

/-- Quantitative center-uniform slab bound after true finite disintegration. -/
theorem affineSlabMass_le_envelope (K : ℝ) (hKpos : 0 ≤ K) (hK : IntervalBound K)
    {k : ℕ} (N : ℕ) (hN : 1 < N) (a b v : Fin (k+1) → ℝ)
    (j : Fin (k+1)) (hv : v j ≠ 0) (ha : 0 < a j) (hab : a j < b j)
    (c eta : ℝ) (heta : 0 ≤ eta) (hA : 3 ≤ (N : ℝ)^(a j)) :
    affineSlabMass N a b v c eta ≤
      envelope K (a j) (b j) (eta/|v j|) N *
        actualPrimeBoxMass N (j.removeNth a) (j.removeNth b) := by
  let S := affineSlabTuples N a b v c eta
  let T := actualPrimeBoxTuples N (j.removeNth a) (j.removeNth b)
  let E := envelope K (a j) (b j) (eta/|v j|) N
  have hmap : ∀ p ∈ S, j.removeNth p ∈ T := by
    intro p hp
    exact removeNth_mem_box j (Finset.mem_filter.mp hp).1
  have hfiber (q : Fin k → ℕ) (hq : q ∈ T) :
      (∑ p ∈ S.filter (fun p => j.removeNth p = q), tupleWeight p) ≤ E*tupleWeight q := by
    let U := S.filter (fun p => j.removeNth p = q)
    have hwq : 0 ≤ tupleWeight q := actualPrimeBoxWeight_nonneg hq
    have hsub : U.image (focus j) ⊆
        slabTuples N (a j) (b j) (fiberCenter N v j q c) (eta/|v j|) := by
      intro z hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hpS,hpq⟩ := Finset.mem_filter.mp hp
      exact fiber_slab_focus_mem j hv q c eta hpS hpq
    have hsum : (∑ p ∈ U, tupleWeight (focus j p)) ≤
        slabMass N (a j) (b j) (fiberCenter N v j q c) (eta/|v j|) := by
      calc
        _ = ∑ z ∈ U.image (focus j), tupleWeight z :=
          (Finset.sum_image (focus_injOn_fiber S j q)).symm
        _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro z hz hnot
          exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hz).1
    have hscalar := slabMass_le_envelope K hKpos hK N hN (a j) (b j)
      (fiberCenter N v j q c) (eta/|v j|) ha hab
      (div_nonneg heta (abs_nonneg _)) hA
    rw [fiber_weight_factor S j q]
    exact (mul_le_mul_of_nonneg_left hsum hwq).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hscalar hwq)
  have hpartition := Finset.sum_fiberwise_of_maps_to (s := S) (t := T)
    (g := j.removeNth) hmap tupleWeight
  calc
    affineSlabMass N a b v c eta =
        ∑ q ∈ T, ∑ p ∈ S.filter (fun p => j.removeNth p = q), tupleWeight p := hpartition.symm
    _ ≤ ∑ q ∈ T, E*tupleWeight q := Finset.sum_le_sum hfiber
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem tendsto_affineSlab_envelope_zero {k : ℕ} (K : ℝ)
    (a b v : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (j : Fin (k+1)) (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => envelope K (a j) (b j) (eta N/|v j|) N *
      actualPrimeBoxMass N (j.removeNth a) (j.removeNth b)) atTop (𝓝 0) := by
  have hwidth : Tendsto (fun N => eta N/|v j|) atTop (𝓝 0) := by
    simpa only [zero_div] using heta.div_const |v j|
  have hscalar := tendsto_envelope_zero K (a j) (b j) (ha j) (hab j) _ hwidth
  have hremaining := tendsto_actualPrimeBoxMass (j.removeNth a) (j.removeNth b)
    (fun i => ha (j.succAbove i)) (fun i => hab (j.succAbove i))
  simpa only [zero_mul] using hscalar.mul hremaining

/-- A single threshold is uniform in the center after any shrinking width
schedule is chosen. There is no restriction on how that center moves. -/
theorem exists_affineSlab_uniform_threshold {k : ℕ}
    (a b v : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (j : Fin (k+1)) (hv : v j ≠ 0) (eta : ℕ → ℝ)
    (heta0 : ∀ N, 0 ≤ eta N) (heta : Tendsto eta atTop (𝓝 0))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, M ≤ N → ∀ c : ℝ, affineSlabMass N a b v c (eta N) < eps := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_reciprocal_interval_bound
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(a j)) atTop atTop :=
    (tendsto_rpow_atTop (ha j)).comp tendsto_natCast_atTop_atTop
  have hE := (tendsto_affineSlab_envelope_zero K a b v ha hab j eta heta).eventually
    (gt_mem_nhds heps)
  have hevent : ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 3 ≤ (N : ℝ)^(a j) ∧
      envelope K (a j) (b j) (eta N/|v j|) N *
        actualPrimeBoxMass N (j.removeNth a) (j.removeNth b) < eps := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),hp.eventually (eventually_ge_atTop (3 : ℝ)),hE]
      with N hN hA hmass
    exact ⟨hN,hA,hmass⟩
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  refine ⟨max 2 M,le_max_left _ _,?_⟩
  intro N hN c
  obtain ⟨hN2,hA,hE⟩ := hM N ((le_max_right _ _).trans hN)
  exact (affineSlabMass_le_envelope K (by linarith) hbound N (by omega)
    a b v j hv (ha j) (hab j) c (eta N) (heta0 N) hA).trans_lt hE

theorem tendsto_affineSlab_arbitrary_center {k : ℕ}
    (a b v : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (j : Fin (k+1)) (hv : v j ≠ 0) (eta center : ℕ → ℝ)
    (heta0 : ∀ N, 0 ≤ eta N) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => affineSlabMass N a b v (center N) (eta N)) atTop (𝓝 0) := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_reciprocal_interval_bound
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(a j)) atTop atTop :=
    (tendsto_rpow_atTop (ha j)).comp tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_affineSlab_envelope_zero K a b v ha hab j eta heta)
  · exact Filter.Eventually.of_forall (fun N => affineSlabMass_nonneg N a b v (center N) (eta N))
  · filter_upwards [eventually_ge_atTop (2 : ℕ),hp.eventually (eventually_ge_atTop (3 : ℝ))]
      with N hN hA
    exact affineSlabMass_le_envelope K (by linarith) hbound N (by omega)
      a b v j hv (ha j) (hab j) (center N) (eta N) (heta0 N) hA

def linearSlabMass {d : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : (Fin d → ℝ) →L[ℝ] ℝ) (c eta : ℝ) : ℝ :=
  ∑ p ∈ (actualPrimeBoxTuples N a b).filter
    (fun p => |L (actualPrimeTupleLog N p)-c| ≤ eta), tupleWeight p

theorem linearSlabMass_eq {d : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : (Fin d → ℝ) →L[ℝ] ℝ) (c eta : ℝ) :
    linearSlabMass N a b L c eta = affineSlabMass N a b (linearCoefficients L) c eta := by
  simp only [linearSlabMass,affineSlabMass,affineSlabTuples,linear_apply_eq_affineValue]

theorem tendsto_linearSlab_arbitrary_center {k : ℕ}
    (a b : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : (Fin (k+1) → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) (eta center : ℕ → ℝ)
    (heta0 : ∀ N, 0 ≤ eta N) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => linearSlabMass N a b L (center N) (eta N)) atTop (𝓝 0) := by
  obtain ⟨j,hj⟩ := exists_nonzero_coordinate (linearCoefficients_ne_zero hL)
  simpa only [linearSlabMass_eq] using
    tendsto_affineSlab_arbitrary_center a b (linearCoefficients L) ha hab
      j hj eta center heta0 heta

end
end ImbalancedChen.P1ActualMovingAffineSlab
