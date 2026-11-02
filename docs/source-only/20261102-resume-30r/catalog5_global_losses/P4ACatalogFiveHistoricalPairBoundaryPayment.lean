import ImbalancedChen.P4ACatalogFiveActualPairDecomposition
import ImbalancedChen.P4ACatalogFivePrimeIntegral
import ImbalancedChen.P1ActualUpperNearOneBound
import ImbalancedChen.AffinePrimeWallReserve

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The full historical rank-two endpoint source, with its original firstStop,
is compared to M's compact arithmetic source by an ABSOLUTE arithmetic
wall payment. Both actual upper residuals are uniformly bounded up to
s = 1, using the existing literal endpoint supplier. No sign is assumed
for their finite difference. The four actual catalog-five walls include
their prime atoms. The resulting pre-N approximation concerns the endpoint
comparison source in Q's exact identity; its coarse/omitted sums are still
separate terms of that identity.
-/

namespace ImbalancedChen.P4ACatalogFiveHistoricalPairBoundaryPayment
noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P4ACatalogFiveActualPairDecomposition
open P4AOriginalSecondPhysicalIntegral P4AOriginalSecondResidualSupplier
open P4ACatalogFivePrimeIntegral
open Certificates.AboveMuSecondCoarse

def pairWeight (p : Fin 2 → ℕ) : ℝ := ∏ i, 1 / ((p i : ℝ)-1)

def pairSaving (N : ℕ) (p : Fin 2 → ℕ) : ℝ :=
  actualPrimeTupleInitialSaving N N
    (endpointEnvelope (actualPrimeTupleLog N p 0))
    (endpointEnvelope (actualPrimeTupleLog N p 1)) p

def normalizedHistoricalEndpoint (d : OriginalData) (N : ℕ) : ℝ :=
  endpointSource d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ)-1)) (fun _ _ => 1)
    (roughPrimeUniverse N N 0 ((N : ℝ)^rho)) * Real.log (N : ℝ) / singularSeries N

def discardedPairs (d : OriginalData) (delta : ℝ) (N : ℕ) : Finset (Fin 2 → ℕ) :=
  (historicalPairs d N N ((N : ℝ)^rho)).filter (fun p =>
    actualPrimeTupleLog N p ∈ sourceRegion ∧ actualPrimeTupleLog N p ∉ trimRegion delta)

def discardedAbsoluteMass (d : OriginalData) (delta : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ discardedPairs d delta N, pairWeight p * |pairSaving N p|

/-- Uniform bound on the entire original source, including approach to
its diagonal/top corner. The proof bounds the two literal residuals,
not their limiting rational difference. -/
theorem exists_full_source_pairSaving_bound :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => (3/16:ℝ)) (fun _ => rho),
        actualPrimeTupleLog N p ∈ sourceRegion → |pairSaving N p| ≤ B := by
  obtain ⟨M,hM,N0,hN0,hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_endpoint_normalized_bound
      (3/16:ℝ) (by norm_num)
  refine ⟨2*M,by positivity,N0,hN0,?_⟩
  intro N hN hEven p hp hsource
  have hN1 : 1 < N := by omega
  have hNr : (1:ℝ) < N := by exact_mod_cast hN1
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have hP : (0:ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  obtain ⟨hx,hy⟩ := (mem_sourceRegion _).mp hsource
  obtain ⟨_,hro,hron,_⟩ := original_residual_window
    ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩ hy.2
  have hsum : Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ) =
      actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 := by
    rw [← actualPrimeTupleLog_sum_prod p hpos,Fin.sum_univ_two]
  have hlevel (lam : ℝ) :
      (N : ℝ)^(lam-actualPrimeTupleLog N p 0-actualPrimeTupleLog N p 1) =
        (N : ℝ)^lam / (∏ i, p i : ℕ) := by
    rw [← residual_rpow_level_div (N : ℝ) (∏ i, p i : ℕ) lam hNr hP,hsum]
    congr 1 <;> ring
  have hcut : (N : ℝ)^(3/16:ℝ) ≤ (p 1 : ℝ) := (hpi 1).2.2.1
  have hcap : (p 1 : ℝ) ≤ N := by
    apply (hpi 1).2.2.2.le.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le
      (by norm_num [rho] : rho ≤ 1)
  have hlegal (lam : ℝ)
      (hl : actualPrimeTupleLog N p 1 ≤
        lam-actualPrimeTupleLog N p 0-actualPrimeTupleLog N p 1) :
      (p 1 : ℝ) ≤ (N : ℝ)^lam / (∏ i, p i : ℕ) := by
    rw [← hlevel]
    rw [← actualPrimeTupleLog_rpow hN1 p hpos 1]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le hl
  have ho := hbound N hN hEven N (p 1 : ℝ)
    ((N : ℝ)^endpointEnvelope (actualPrimeTupleLog N p 0) / (∏ i, p i : ℕ))
    hcut (hlegal _ hro.le) hcap
  have hn := hbound N hN hEven N (p 1 : ℝ)
    ((N : ℝ)^endpointEnvelope (actualPrimeTupleLog N p 1) / (∏ i, p i : ℕ))
    hcut (hlegal _ (hro.le.trans hron)) hcap
  unfold pairSaving actualPrimeTupleInitialSaving
  simp only [sub_mul,sub_div]
  exact (abs_sub _ _).trans (by linarith)

/-- All untrimmed source points lie in the same fixed arithmetic box.
The actual firstStop remains in historicalPairs. -/
theorem historical_source_pair_mem_box (d : OriginalData) (N : ℕ) (hN : 1 < N)
    (p : Fin 2 → ℕ) (hp : p ∈ historicalPairs d N N ((N : ℝ)^rho))
    (hs : actualPrimeTupleLog N p ∈ sourceRegion) :
    p ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => (3/16:ℝ)) (fun _ => rho) := by
  have hm := (mem_firstExitAdmittedTuples_iff_of_decreasing 2
    (P5OriginalCommonRefinedConstructor.old3 d (N : ℝ))
    (roughPrimeUniverse N N 0 ((N : ℝ)^rho))
    (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hp
  apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
  refine ⟨?_,sourceRegion_subset_cube hs⟩
  intro i
  have hi := mem_roughPrimeUniverse.mp (hm.2.1 i)
  exact ⟨hi.2.1,hi.2.2.1⟩

/-- Literal four-wall support of the discarded region. It includes the
closed strips, and makes no assertion that their arithmetic atoms vanish. -/
theorem source_not_trim_in_wall {delta : ℝ} (hd : 0 < delta)
    {t : Fin 2 → ℝ} (hs : t ∈ sourceRegion) (ht : t ∉ trimRegion delta) :
    t ∈ primeAffineWallStrip trimForms (trimBounds 0) delta := by
  obtain ⟨hx,hy⟩ := (mem_sourceRegion t).mp hs
  change ¬(mu+delta ≤ t 0 ∧ t 0 ≤ rho-delta ∧
    lowerBoundary (t 0)+delta ≤ t 1 ∧ t 1 ≤ t 0-delta) at ht
  push_neg at ht
  rcases ht with h | h | h | h
  · refine ⟨0,?_⟩
    norm_num [trimForms,trimBounds]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · refine ⟨1,?_⟩
    norm_num [trimForms,trimBounds]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · refine ⟨2,?_⟩
    norm_num [trimForms,trimBounds]
    unfold lowerBoundary at h hy
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · refine ⟨3,?_⟩
    norm_num [trimForms,trimBounds]
    exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Exact signed complement. Q's compact carrier theorem is reused as is. -/
theorem historical_endpoint_eq_trim_add_complement
    (d : OriginalData) (delta : ℝ) (hd : 0 < delta) (he : 0 ≤ (d.e : ℝ))
    (hclear : 4*(d.e:ℝ)+P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta)
    (N : ℕ) (hN : 1 < N) :
    normalizedHistoricalEndpoint d N = trimmedArithmeticSaving delta N +
      ∑ p ∈ discardedPairs d delta N, pairWeight p * pairSaving N p := by
  rw [normalizedHistoricalEndpoint,
    normalized_endpointSource_eq_catalog_summands_on_actual_pairs d N N hN]
  rw [← historical_trimmed_sum_eq_catalog_arithmetic d delta hd he hclear N hN]
  unfold discardedPairs pairWeight pairSaving
  rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hsub : actualPrimeTupleLog N p ∈ trimRegion delta →
      actualPrimeTupleLog N p ∈ sourceRegion := trimRegion_subset_sourceRegion hd
  change (if actualPrimeTupleLog N p ∈ sourceRegion then _ else 0) = _
  by_cases hs : actualPrimeTupleLog N p ∈ sourceRegion
  · by_cases ht : actualPrimeTupleLog N p ∈ trimRegion delta <;> simp [hs,ht,trimRegion]
  · have ht : actualPrimeTupleLog N p ∉ trimRegion delta := fun ht => hs (hsub ht)
    simp [hs,ht,trimRegion]

/-- A genuine arbitrary-precision payment, uniform in the actual old
history d. Width first, then N0; all smaller positive trims are allowed. -/
theorem exists_uniform_discarded_pair_payment (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ d : OriginalData,
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        discardedAbsoluteMass d delta N < epsilon := by
  obtain ⟨B,hB,Nb,hNb,hbound⟩ := exists_full_source_pairSaving_bound
  obtain ⟨delta0,hd0,Ns,hNs,hstrip⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    (by norm_num : (0:ℝ)<3/16) (by norm_num [rho] : (3/16:ℝ)<rho)
    trimForms (trimBounds 0) trimForms_ne_zero (epsilon/B) (div_pos heps hB)
  refine ⟨delta0,hd0,max Nb Ns,hNb.trans (le_max_left _ _),?_⟩
  intro N hN hEven d delta hd hdd
  have hN1 : 1 < N := by omega
  have hsubset : discardedPairs d delta N ⊆
      (actualPrimeBoxTuples N (fun _ : Fin 2 => (3/16:ℝ)) (fun _ => rho)).filter
        (fun p => actualPrimeTupleLog N p ∈ primeAffineWallStrip trimForms (trimBounds 0) delta0) := by
    intro p hp
    obtain ⟨hh,hs,ht⟩ := Finset.mem_filter.mp hp
    obtain ⟨j,hj⟩ := source_not_trim_in_wall hd hs ht
    exact Finset.mem_filter.mpr
      ⟨historical_source_pair_mem_box d N hN1 p hh hs,j,hj.trans hdd⟩
  have hmass : (∑ p ∈ discardedPairs d delta N, pairWeight p) ≤
      actualPrimeAffineWallStripMass N (fun _ : Fin 2 => (3/16:ℝ)) (fun _ => rho)
        trimForms (trimBounds 0) delta0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1
  calc
    discardedAbsoluteMass d delta N ≤
        ∑ p ∈ discardedPairs d delta N, pairWeight p * B := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_filter.mp hp
      have hb := historical_source_pair_mem_box d N hN1 p hh.1 hh.2.1
      exact mul_le_mul_of_nonneg_left
        (hbound N ((le_max_left _ _).trans hN) hEven p hb hh.2.1)
        (actualPrimeBoxWeight_nonneg hb)
    _ = (∑ p ∈ discardedPairs d delta N, pairWeight p) * B := by rw [Finset.sum_mul]
    _ ≤ actualPrimeAffineWallStripMass N (fun _ : Fin 2 => (3/16:ℝ)) (fun _ => rho)
        trimForms (trimBounds 0) delta0 * B := mul_le_mul_of_nonneg_right hmass hB.le
    _ < epsilon := (lt_div_iff₀ hB).mp (hstrip N ((le_max_right _ _).trans hN))

theorem abs_historical_endpoint_sub_trim_le
    (d : OriginalData) (delta : ℝ) (hd : 0 < delta) (he : 0 ≤ (d.e : ℝ))
    (hclear : 4*(d.e:ℝ)+P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta)
    (N : ℕ) (hN : 1 < N) :
    |normalizedHistoricalEndpoint d N-trimmedArithmeticSaving delta N| ≤
      discardedAbsoluteMass d delta N := by
  rw [historical_endpoint_eq_trim_add_complement d delta hd he hclear N hN,
    add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hh := Finset.mem_filter.mp hp
  have hbox := historical_source_pair_mem_box d N hN p hh.1 hh.2.1
  simp only [abs_mul,abs_of_nonneg (actualPrimeBoxWeight_nonneg hbox),le_refl]

/-- The complete untrimmed historical ENDPOINT source reaches the original
integral. The actual coarse/omitted discrepancy sums have not been folded
into this statement. No assumption erases firstStop or asserts a sign. -/
theorem exists_historical_endpoint_approx_integral (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ d : OriginalData, 0 ≤ (d.e : ℝ) →
        4*(d.e:ℝ)+P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
      ∀ N : ℕ, N0 ≤ N → Even N →
        |normalizedHistoricalEndpoint d N-physicalSaving| < epsilon := by
  have he3 : 0 < epsilon/3 := by positivity
  obtain ⟨delta0,hd0,Nw,hNw,hwall⟩ := exists_uniform_discarded_pair_payment (epsilon/3) he3
  obtain ⟨n,hnw,hni⟩ := ((width_tendsto.eventually (gt_mem_nhds hd0)).and
    (Metric.tendsto_nhds.mp tendsto_trimIntegral (epsilon/3) he3)).exists
  let delta := width n
  have hd : 0 < delta := width_pos n
  have hdi : |trimIntegral delta-physicalSaving| < epsilon/3 := by
    simpa only [Real.dist_eq] using hni
  have hev : ∀ᶠ N : ℕ in atTop, 0 < N ∧ Even N →
      |trimmedArithmeticSaving delta N-trimIntegral delta| < epsilon/3 := by
    simpa only [eventually_inf_principal,mem_setOf_eq,Real.dist_eq] using
      Metric.tendsto_nhds.mp (tendsto_trimmedArithmeticSaving delta hd) (epsilon/3) he3
  obtain ⟨Ni,hNi⟩ := eventually_atTop.mp hev
  refine ⟨delta,hd,max Nw Ni,hNw.trans (le_max_left _ _),?_⟩
  intro d he hclear N hN hEven
  have hN1 : 1 < N := by omega
  have hw := (abs_historical_endpoint_sub_trim_le d delta hd he hclear N hN1).trans_lt
    (hwall N ((le_max_left _ _).trans hN) hEven d delta hd hnw.le)
  have hi := hNi N ((le_max_right _ _).trans hN) ⟨by omega,hEven⟩
  have htri := abs_sub_le (normalizedHistoricalEndpoint d N)
    (trimmedArithmeticSaving delta N) physicalSaving
  have htri' := abs_sub_le (trimmedArithmeticSaving delta N) (trimIntegral delta) physicalSaving
  linarith

theorem exists_historical_endpoint_catalog5_lower (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ d : OriginalData, 0 ≤ (d.e : ℝ) →
        4*(d.e:ℝ)+P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
      ∀ N : ℕ, N0 ≤ N → Even N →
        (640339/15210735000:ℝ)-epsilon < normalizedHistoricalEndpoint d N := by
  obtain ⟨delta,hd,N0,hN0,hbound⟩ := exists_historical_endpoint_approx_integral epsilon heps
  refine ⟨delta,hd,N0,hN0,?_⟩
  intro d he hclear N hN hEven
  have hh := (abs_lt.mp (hbound d he hclear N hN hEven)).1
  linarith [original_physical_saving_ge_catalog_five]

end
end ImbalancedChen.P4ACatalogFiveHistoricalPairBoundaryPayment
