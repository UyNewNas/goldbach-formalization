import ImbalancedChen.P4AOriginalSecondPhysicalIntegral
import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original catalog 5 after J's physical/chart dictionary.  The integrand below
uses the actual continuous upper Rosser factor, independently of the rational
kernel.  Its original residual window, normalization, gates and whole integral
are proved.  Fixed compact interiors also receive a common threshold for the
same literal target-linked upper Rosser densities and their prime-pair caller.
No rational endpoint, convergence estimate or source-window licence is assumed.

This is an endpoint ordinary-residual supplier.  Identifying that residual with
the common causal tree still requires rank-three restoration, preservation of
below-mu witnesses and the old disabled-small-third tail.  None is asserted here.
-/

namespace ImbalancedChen.P4AOriginalSecondResidualSupplier

noncomputable section
open Set MeasureTheory Filter Topology
open MathlibNt.SieveTheory
open scoped Interval BigOperators Classical
open Certificates.AboveMuSecondCoarse
open P4AOriginalSecondPhysicalIntegral
open P4AAll22OriginalKLedger20261024zSourceOnly

/-- The upper factor in precisely the manuscript's normalized convention. -/
def upperBar (s : ℝ) : ℝ :=
  suzukiContinuousUpperFactor s / (2 * Real.exp Real.eulerMascheroniConstant)

/-- The original even-prefix profile, with its two actual ordinary residuals. -/
def sourceProfileKernel (x y : ℝ) : ℝ :=
  4 * (upperBar ((endpointEnvelope x - x - y) / y) -
    upperBar ((endpointEnvelope y - x - y) / y)) / (x * y^2)

def sourceProfileSaving : ℝ :=
  ∫ x in mu..rho, ∫ y in lowerBoundary x..x, sourceProfileKernel x y

/-- The pre-harmonic rational difference; no prime-coordinate mass is included. -/
def residualSaving (x y : ℝ) : ℝ :=
  4 * (endpointEnvelope y - endpointEnvelope x) /
    ((endpointEnvelope x - x - y) * (endpointEnvelope y - x - y))

theorem endpointEnvelope_le_Lambda (t : ℝ) :
    endpointEnvelope t ≤ (153 / 256 : ℝ) := by
  by_cases ht : t ≤ mu
  · have h := min_le_left ((1+t)/2) (57/64-3*t/2)
    dsimp [endpointEnvelope, mu] at *
    linarith
  · have h := min_le_right ((1+t)/2) (57/64-3*t/2)
    dsimp [endpointEnvelope, mu] at *
    linarith

theorem endpointEnvelope_on_closed_strip {x : ℝ} (hx : x ∈ Icc mu rho) :
    endpointEnvelope x = 57 / 64 - 3 * x / 2 := by
  apply min_eq_right
  dsimp [mu] at hx
  linarith [hx.1]

theorem original_closed_caps {x y : ℝ} (hx : x ∈ Icc mu rho)
    (hy : y ∈ Icc (lowerBoundary x) x) :
    3*x ≤ endpointEnvelope x ∧ endpointEnvelope x ≤ endpointEnvelope y := by
  rw [endpointEnvelope_on_closed_strip hx]
  constructor
  · dsimp [rho] at hx
    linarith [hx.2]
  · apply le_min
    · dsimp [lowerBoundary] at hy
      linarith [hy.1]
    · linarith [hy.2]

/-- The source's exact residual range is derived, including the stronger
55/48 upper bound.  The diagonal is handled separately in the whole integral. -/
theorem original_residual_window {x y : ℝ} (hx : x ∈ Icc mu rho)
    (hy : y ∈ Icc (lowerBoundary x) x) (hstrict : y < x) :
    0 < y ∧ y < endpointEnvelope x - x - y ∧
      endpointEnvelope x - x - y ≤ endpointEnvelope y - x - y ∧
      endpointEnvelope y - x - y ≤ (55 / 48 : ℝ) * y := by
  have hb := physical_denominator_bounds hx hy
  have hc := original_closed_caps hx hy
  have hu := endpointEnvelope_le_Lambda y
  have hxl : (25 / 128 : ℝ) ≤ x := hx.1
  refine ⟨by linarith [hb.2.1], ?_, by linarith [hc.2], ?_⟩
  · linarith [hc.1]
  · linarith [hb.2.1]

/-- Literal physical source licenses, not assumed residual or selected gates. -/
theorem original_source_gates {x y : ℝ} (h : (x,y) ∈ physicalDomain) :
    2*x < endpointEnvelope x ∧ x+2*y < endpointEnvelope x ∧
      2*x+y < endpointEnvelope x ∧ endpointEnvelope x < endpointEnvelope y ∧
      endpointEnvelope y ≤ (153 / 256 : ℝ) ∧
      endpointEnvelope y < (299 / 500 : ℝ) := by
  obtain ⟨hx,hy⟩ := (physicalDomain_iff x y).mp h
  have hxc : x ∈ Icc mu rho := ⟨hx.1.le,hx.2.le⟩
  have hvx := endpointEnvelope_on_closed_strip hxc
  have hpos : 0 < x := by have := hx.1; dsimp [mu] at this; linarith
  have h3 : 3*x < endpointEnvelope x := by
    rw [hvx]
    have := hx.2
    dsimp [rho] at this
    linarith
  have hraise : endpointEnvelope x < endpointEnvelope y := by
    rw [hvx]
    apply lt_min
    · dsimp [lowerBoundary] at hy
      linarith [hy.1]
    · linarith [hy.2]
  have hcap := endpointEnvelope_le_Lambda y
  exact ⟨by linarith, by linarith [hy.2], by linarith [hy.2],
    hraise, hcap, by linarith⟩

theorem upperBar_initial {s : ℝ} (hs : 1 < s) (hs3 : s ≤ 3) :
    upperBar s = 1 / s := by
  rw [upperBar, suzukiContinuousUpperFactor_eq_initial_of_actual_limits s hs hs3]
  field_simp [ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant),
    ne_of_gt (lt_trans (by norm_num : (0:ℝ) < 1) hs)]
  <;> ring

/-- This is an equality of the actual sieve-profile integrand on the entire
closed physical region.  At y=x both cap differences vanish, so no false
extension of the initial branch to s=1 is needed. -/
theorem sourceProfileKernel_eq_physicalKernel {x y : ℝ}
    (hx : x ∈ Icc mu rho) (hy : y ∈ Icc (lowerBoundary x) x) :
    sourceProfileKernel x y = physicalKernel x y := by
  by_cases heq : y = x
  · subst y
    simp [sourceProfileKernel, physicalKernel]
  · have hstrict : y < x := lt_of_le_of_ne hy.2 heq
    obtain ⟨hy0,ho,hon,hn⟩ := original_residual_window hx hy hstrict
    have ho3 : endpointEnvelope x-x-y ≤ 3*y := by linarith
    have hn3 : endpointEnvelope y-x-y ≤ 3*y := by linarith
    have hxo : x ≠ 0 := ne_of_gt
      ((by norm_num [mu] : 0 < mu).trans_le hx.1)
    have hro : endpointEnvelope x-x-y ≠ 0 := (hy0.trans ho).ne'
    have hrn : endpointEnvelope y-x-y ≠ 0 := (hy0.trans (ho.trans_le hon)).ne'
    unfold sourceProfileKernel
    rw [upperBar_initial ((one_lt_div hy0).mpr ho) ((div_le_iff₀ hy0).mpr ho3),
      upperBar_initial ((one_lt_div hy0).mpr (ho.trans_le hon))
        ((div_le_iff₀ hy0).mpr hn3)]
    unfold physicalKernel
    field_simp [hxo,hy0.ne',hro,hrn]
    <;> ring

theorem residualSaving_div_eq_physicalKernel {x y : ℝ}
    (hx : x ∈ Icc mu rho) (hy : y ∈ Icc (lowerBoundary x) x) :
    residualSaving x y / (x*y) = physicalKernel x y := by
  obtain ⟨hx0,hy0,ho,hn⟩ := physical_denominator_bounds hx hy
  have hr : 0 < rho := by norm_num [rho]
  have hxp : 0 < x := (by norm_num [mu] : 0 < mu).trans_le hx0
  have hyp : 0 < y := (by norm_num : (0:ℝ) < 3/16).trans_le hy0
  unfold residualSaving physicalKernel
  field_simp [hxp.ne',hyp.ne',(hr.trans_le ho).ne',(hr.trans_le hn).ne']
  <;> ring

theorem sourceProfile_fibre_intervalIntegrable {x : ℝ} (hx : x ∈ Icc mu rho) :
    IntervalIntegrable (sourceProfileKernel x) volume (lowerBoundary x) x := by
  have horder := (boundary_order hx).2.1.trans hx.1
  apply (physical_fibre_intervalIntegrable hx le_rfl horder le_rfl).congr
  intro y hy
  rw [uIoc_of_le horder] at hy
  exact (sourceProfileKernel_eq_physicalKernel hx ⟨hy.1.le,hy.2⟩).symm

theorem sourceProfile_row_eq {x : ℝ} (hx : x ∈ Icc mu rho) :
    (∫ y in lowerBoundary x..x, sourceProfileKernel x y) =
      ∫ y in lowerBoundary x..x, physicalKernel x y := by
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le ((boundary_order hx).2.1.trans hx.1)] at hy
  exact sourceProfileKernel_eq_physicalKernel hx hy

theorem sourceProfile_outer_intervalIntegrable :
    IntervalIntegrable (fun x => ∫ y in lowerBoundary x..x, sourceProfileKernel x y)
      volume mu rho := by
  apply physical_outer_intervalIntegrable.congr
  intro x hx
  rw [uIoc_of_le (by norm_num [mu,rho])] at hx
  exact (sourceProfile_row_eq ⟨hx.1.le,hx.2⟩).symm

/-- Actual upper-factor integral, not a quoted endpoint or a renamed chart. -/
theorem sourceProfileSaving_eq_physicalSaving : sourceProfileSaving = physicalSaving := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num [mu,rho])] at hx
  exact sourceProfile_row_eq hx

theorem original_profile_saving_ge_catalog_five :
    (640339 / 15210735000 : ℝ) ≤ sourceProfileSaving := by
  rw [sourceProfileSaving_eq_physicalSaving]
  exact original_physical_saving_ge_catalog_five

/-! Fixed original compact interiors and actual residual thresholds. -/

def trimmedRegion (delta : ℝ) : Set (ℝ × ℝ) :=
  {p | mu+delta ≤ p.1 ∧ p.1 ≤ rho-delta ∧
    lowerBoundary p.1+delta ≤ p.2 ∧ p.2 ≤ p.1-delta}

theorem trimmedRegion_subset_physicalDomain {delta : ℝ} (hd : 0 < delta) :
    trimmedRegion delta ⊆ physicalDomain := by
  rintro ⟨x,y⟩ ⟨h1,h2,h3,h4⟩
  apply (physicalDomain_iff x y).mpr
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem isCompact_trimmedRegion {delta : ℝ} (hd : 0 < delta) :
    IsCompact (trimmedRegion delta) := by
  have hclosed : IsClosed (trimmedRegion delta) := by
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le (by unfold lowerBoundary; fun_prop) continuous_snd).inter
          (isClosed_le continuous_snd (by fun_prop))))
  have hbox : IsCompact (Icc mu rho ×ˢ Icc (3 / 16 : ℝ) rho) :=
    isCompact_Icc.prod isCompact_Icc
  apply hbox.of_isClosed_subset hclosed
  intro p hp
  obtain ⟨hx,hy⟩ := (physicalDomain_iff p.1 p.2).mp
    (trimmedRegion_subset_physicalDomain hd hp)
  have hxc : p.1 ∈ Icc mu rho := ⟨hx.1.le,hx.2.le⟩
  exact ⟨hxc,⟨(boundary_order hxc).1.trans hy.1.le,hy.2.le.trans hx.2.le⟩⟩

def oldResidualPair (p : ℝ × ℝ) : ℝ × ℝ :=
  (endpointEnvelope p.1-p.1-p.2,p.2)

def newResidualPair (p : ℝ × ℝ) : ℝ × ℝ :=
  (endpointEnvelope p.2-p.1-p.2,p.2)

def residualParameterSet (B : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  oldResidualPair '' B ∪ newResidualPair '' B

theorem residualParameterSet_compact {B : Set (ℝ × ℝ)} (hB : IsCompact B) :
    IsCompact (residualParameterSet B) := by
  have ho : Continuous oldResidualPair :=
    (((continuous_endpointEnvelope.comp continuous_fst).sub continuous_fst).sub
      continuous_snd).prodMk continuous_snd
  have hn : Continuous newResidualPair :=
    (((continuous_endpointEnvelope.comp continuous_snd).sub continuous_fst).sub
      continuous_snd).prodMk continuous_snd
  exact (hB.image ho).union (hB.image hn)

theorem residualParameterSet_legal {B : Set (ℝ × ℝ)} (hB : B ⊆ physicalDomain) :
    ∀ q ∈ residualParameterSet B, 0 < q.2 ∧ q.2 < q.1 ∧ q.1 ≤ 3*q.2 := by
  intro q hq
  rcases hq with ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · obtain ⟨hx,hy⟩ := (physicalDomain_iff p.1 p.2).mp (hB hp)
    obtain ⟨hy0,ho,hon,hn⟩ := original_residual_window
      ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩ hy.2
    exact ⟨hy0,ho,by dsimp [oldResidualPair]; linarith⟩
  · obtain ⟨hx,hy⟩ := (physicalDomain_iff p.1 p.2).mp (hB hp)
    obtain ⟨hy0,ho,hon,hn⟩ := original_residual_window
      ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩ hy.2
    exact ⟨hy0,ho.trans_le hon,by dsimp [newResidualPair]; linarith⟩

/-- One threshold, before N and both original variable caps.  The only
premises on B are ordinary compact geometry inside the original strip. -/
theorem exists_actual_second_residual_uniform_threshold
    (B : Set (ℝ × ℝ)) (hBc : IsCompact B) (hB : B ⊆ physicalDomain)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ B, ∀ cap : ℕ, (N : ℝ)^p.2 ≤ (cap : ℝ) →
        |(actualSmallRosserPlusDensity N cap ((N : ℝ)^p.2)
            ((N : ℝ)^(endpointEnvelope p.1-p.1-p.2)) -
          actualSmallRosserPlusDensity N cap ((N : ℝ)^p.2)
            ((N : ℝ)^(endpointEnvelope p.2-p.1-p.2))) *
          Real.log (N : ℝ) / singularSeries N - residualSaving p.1 p.2| < eta := by
  obtain ⟨N0,hN0,hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_compact_difference_threshold
      (residualParameterSet B) (residualParameterSet_compact hBc)
      (residualParameterSet_legal hB) eta heta
  refine ⟨N0,hN0,?_⟩
  intro N hN hEven p hp cap hcap
  have ho : oldResidualPair p ∈ residualParameterSet B := Or.inl ⟨p,hp,rfl⟩
  have hn : newResidualPair p ∈ residualParameterSet B := Or.inr ⟨p,hp,rfl⟩
  have h := hbound N hN hEven _ _ _ ho hn cap hcap
  have hcancel : (endpointEnvelope p.2-p.1-p.2) -
      (endpointEnvelope p.1-p.1-p.2) = endpointEnvelope p.2-endpointEnvelope p.1 := by ring
  simpa only [oldResidualPair,newResidualPair,residualSaving,hcancel] using h

/-- A concrete original trimmed source needs no window/cap licence premise. -/
theorem exists_actual_trimmed_second_residual_threshold
    (delta eta : ℝ) (hd : 0 < delta) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ trimmedRegion delta, ∀ cap : ℕ, (N : ℝ)^p.2 ≤ (cap : ℝ) →
        |(actualSmallRosserPlusDensity N cap ((N : ℝ)^p.2)
            ((N : ℝ)^(endpointEnvelope p.1-p.1-p.2)) -
          actualSmallRosserPlusDensity N cap ((N : ℝ)^p.2)
            ((N : ℝ)^(endpointEnvelope p.2-p.1-p.2))) *
          Real.log (N : ℝ) / singularSeries N - residualSaving p.1 p.2| < eta :=
  exists_actual_second_residual_uniform_threshold (trimmedRegion delta)
    (isCompact_trimmedRegion hd) (trimmedRegion_subset_physicalDomain hd) eta heta

/-- The same threshold applies at the actual ordered prime pair's product,
last prime, target-deleted coefficients and endpoint caps.  No residual
parameter membership or approximation is assumed in this caller. -/
theorem exists_actual_second_prime_pair_uniform_threshold
    (B : Set (ℝ × ℝ)) (hBc : IsCompact B) (hB : B ⊆ physicalDomain)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p : Fin 2 → ℕ, (∀ i, 0 < p i) →
      (actualPrimeTupleLog N p 0, actualPrimeTupleLog N p 1) ∈ B →
      ∀ cap : ℕ, (p 1 : ℝ) ≤ cap →
        |actualPrimeTupleInitialSaving N cap
            (endpointEnvelope (actualPrimeTupleLog N p 0))
            (endpointEnvelope (actualPrimeTupleLog N p 1)) p -
          residualSaving (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1)| < eta := by
  obtain ⟨N0,hN0,hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold
      (residualParameterSet B) (residualParameterSet_compact hBc)
      (residualParameterSet_legal hB) eta heta
  refine ⟨N0,hN0,?_⟩
  intro N hN hEven p hp hsource cap hcap
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hp i)
  have hy : (0 : ℝ) < p 1 := by exact_mod_cast hp 1
  have hsum : Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ) =
      actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 := by
    rw [← actualPrimeTupleLog_sum_prod p hp, Fin.sum_univ_two]
  have ho : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 1 : ℝ)
      (endpointEnvelope (actualPrimeTupleLog N p 0)) ∈ residualParameterSet B := by
    unfold actualRosserQuotientParameters
    rw [hsum]
    exact Or.inl ⟨_,hsource,by simp only [oldResidualPair,actualPrimeTupleLog,sub_sub]⟩
  have hn : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 1 : ℝ)
      (endpointEnvelope (actualPrimeTupleLog N p 1)) ∈ residualParameterSet B := by
    unfold actualRosserQuotientParameters
    rw [hsum]
    exact Or.inr ⟨_,hsource,by simp only [newResidualPair,actualPrimeTupleLog,sub_sub]⟩
  have h := hbound N hN hEven _ _ _ _ hP hy ho hn cap hcap
  rw [hsum] at h
  simpa only [actualPrimeTupleInitialSaving,residualSaving,sub_sub] using h

/-! Actual target-deleted, strictly ordered original prime source. -/

def trimmedPrimePairs (delta : ℝ) (N : ℕ) : Finset (Fin 2 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ : Fin 2 => (3 / 16 : ℝ)) (fun _ => rho)).filter
    (fun p => (actualPrimeTupleLog N p 0,actualPrimeTupleLog N p 1) ∈ trimmedRegion delta)

/-- The enumeration box deletes no original trimmed source tuple.  Its
membership is exactly primality, target exclusion and the original geometry. -/
theorem mem_trimmedPrimePairs_iff {delta : ℝ} (hd : 0 < delta)
    {N : ℕ} (hN : 1 < N) (p : Fin 2 → ℕ) :
    p ∈ trimmedPrimePairs delta N ↔
      (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N) ∧
      (actualPrimeTupleLog N p 0,actualPrimeTupleLog N p 1) ∈ trimmedRegion delta := by
  constructor
  · intro hp
    have hm := Finset.mem_filter.mp hp
    exact ⟨fun i => ⟨(mem_actualPrimeBoxTuples_iff.mp hm.1 i).1,
      (mem_actualPrimeBoxTuples_iff.mp hm.1 i).2.1⟩,hm.2⟩
  · rintro ⟨hprime,hsource⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,hsource⟩
    apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
    refine ⟨hprime,mem_logPrimeBox.mpr ?_⟩
    obtain ⟨hx,hy⟩ := (physicalDomain_iff _ _).mp
      (trimmedRegion_subset_physicalDomain hd hsource)
    have hxc : actualPrimeTupleLog N p 0 ∈ Icc mu rho := ⟨hx.1.le,hx.2.le⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · exact ⟨(by norm_num [mu] : (3 / 16 : ℝ) ≤ mu).trans hx.1.le,hx.2⟩
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact ⟨(boundary_order hxc).1.trans hy.1.le,hy.2.trans hx.2⟩
theorem trimmedPrimePairs_prime_target {delta : ℝ} {N : ℕ} {p : Fin 2 → ℕ}
    (hp : p ∈ trimmedPrimePairs delta N) :
    (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N) ∧ (∏ i, p i).Coprime N := by
  have hb := (Finset.mem_filter.mp hp).1
  exact ⟨fun i => ⟨(mem_actualPrimeBoxTuples_iff.mp hb i).1,
    (mem_actualPrimeBoxTuples_iff.mp hb i).2.1⟩,
    actualPrimeBoxTuple_product_coprime_target hb⟩

theorem trimmedPrimePairs_strict_order {delta : ℝ} (hd : 0 < delta)
    {N : ℕ} (hN : 1 < N) {p : Fin 2 → ℕ} (hp : p ∈ trimmedPrimePairs delta N) :
    p 1 < p 0 := by
  have hm := Finset.mem_filter.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hm.1 i).1.pos
  have hyx := ((physicalDomain_iff _ _).mp
    (trimmedRegion_subset_physicalDomain hd hm.2)).2.2
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow := (Real.rpow_lt_rpow_left_iff hNr).mpr hyx
  rw [actualPrimeTupleLog_rpow hN p hpos 1,
    actualPrimeTupleLog_rpow hN p hpos 0] at hpow
  exact_mod_cast hpow

/-- The residual ambient cap is the original N.  It is not enlarged in the
arithmetic supplier, because the actual last prime is already below N^rho. -/
theorem exists_actual_trimmed_prime_pairs_threshold
    (delta eta : ℝ) (hd : 0 < delta) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ trimmedPrimePairs delta N,
        |actualPrimeTupleInitialSaving N N
            (endpointEnvelope (actualPrimeTupleLog N p 0))
            (endpointEnvelope (actualPrimeTupleLog N p 1)) p -
          residualSaving (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1)| < eta := by
  obtain ⟨N0,hN0,hbound⟩ := exists_actual_second_prime_pair_uniform_threshold
    (trimmedRegion delta) (isCompact_trimmedRegion hd)
    (trimmedRegion_subset_physicalDomain hd) eta heta
  refine ⟨N0,hN0,?_⟩
  intro N hN hEven p hp
  have hm := Finset.mem_filter.mp hp
  have hpi := mem_actualPrimeBoxTuples_iff.mp hm.1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcap : (p 1 : ℝ) ≤ N := by
    calc
      _ ≤ (N : ℝ)^rho := (hpi 1).2.2.2.le
      _ ≤ (N : ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hNr
        (by norm_num [rho])
      _ = N := Real.rpow_one _
  exact hbound N hN hEven p (fun i => (hpi i).1.pos) hm.2 N hcap

def trimmedArithmeticSaving (delta : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ trimmedPrimePairs delta N, (∏ i, 1 / ((p i : ℝ)-1)) *
    actualPrimeTupleInitialSaving N N
      (endpointEnvelope (actualPrimeTupleLog N p 0))
      (endpointEnvelope (actualPrimeTupleLog N p 1)) p

def trimmedRationalProfileSum (delta : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ trimmedPrimePairs delta N, (∏ i, 1 / ((p i : ℝ)-1)) *
    residualSaving (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1)

/-- Exact placement of the logarithmic harmonic mass: x*y is removed from
the physical integrand before weighting by actual reciprocal-prime masses. -/
theorem trimmedRationalProfileSum_eq_original_profile (delta : ℝ) (hd : 0 < delta)
    (N : ℕ) :
    trimmedRationalProfileSum delta N =
      ∑ p ∈ trimmedPrimePairs delta N, (∏ i, 1 / ((p i : ℝ)-1)) *
        (sourceProfileKernel (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1) *
          (actualPrimeTupleLog N p 0 * actualPrimeTupleLog N p 1)) := by
  apply Finset.sum_congr rfl
  intro p hp
  have hs := trimmedRegion_subset_physicalDomain hd (Finset.mem_filter.mp hp).2
  obtain ⟨hx,hy⟩ := (physicalDomain_iff _ _).mp hs
  have hxc : actualPrimeTupleLog N p 0 ∈ Icc mu rho := ⟨hx.1.le,hx.2.le⟩
  have hyc : actualPrimeTupleLog N p 1 ∈ Icc (lowerBoundary (actualPrimeTupleLog N p 0))
      (actualPrimeTupleLog N p 0) := ⟨hy.1.le,hy.2.le⟩
  obtain ⟨hx0,hy0,_,_⟩ := physical_denominator_bounds hxc hyc
  have hxp : 0 < actualPrimeTupleLog N p 0 :=
    (by norm_num [mu] : 0 < mu).trans_le hx0
  have hyp : 0 < actualPrimeTupleLog N p 1 :=
    (by norm_num : (0:ℝ) < 3/16).trans_le hy0
  rw [sourceProfileKernel_eq_physicalKernel hxc hyc]
  exact congrArg (fun r : ℝ => (∏ i, 1 / ((p i : ℝ)-1)) * r)
    ((div_eq_iff (mul_pos hxp hyp).ne').mp (residualSaving_div_eq_physicalKernel hxc hyc))

/-- The original fixed source carries an actual arithmetic-to-profile
asymptotic, not an assumed uniform source error.  Positivity of the real
prime weights and the existing box mass limit pay the complete summation. -/
theorem tendsto_trimmedArithmeticSaving_sub_profile (delta : ℝ) (hd : 0 < delta) :
    Tendsto (fun N : ℕ => trimmedArithmeticSaving delta N - trimmedRationalProfileSum delta N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let l : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}
  let T := trimmedPrimePairs delta
  let w (_N : ℕ) (p : Fin 2 → ℕ) := ∏ i, 1 / ((p i : ℝ)-1)
  let f (N : ℕ) (p : Fin 2 → ℕ) := actualPrimeTupleInitialSaving N N
    (endpointEnvelope (actualPrimeTupleLog N p 0))
    (endpointEnvelope (actualPrimeTupleLog N p 1)) p
  let g (N : ℕ) (p : Fin 2 → ℕ) :=
    residualSaving (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1)
  have hmasslimit := (tendsto_actualPrimeBoxMass
    (fun _ : Fin 2 => (3 / 16 : ℝ)) (fun _ => rho)
    (fun _ => by norm_num) (fun _ => by norm_num [rho])).mono_left
      (show l ≤ atTop from inf_le_left)
  obtain ⟨M,hM,hmass⟩ := exists_eventually_bounded_mass_of_tendsto hmasslimit
  have hw : ∀ᶠ N in l, ∀ p ∈ T N, 0 ≤ w N p :=
    Eventually.of_forall (fun N p hp => actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1)
  have hmass' : ∀ᶠ N in l, (∑ p ∈ T N, w N p) ≤ M := by
    filter_upwards [hmass] with N hN
    apply le_trans ?_ hN
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p hp _ => actualPrimeBoxWeight_nonneg hp)
  have hfg : ∀ eta > 0, ∀ᶠ N in l, ∀ p ∈ T N, |f N p-g N p| < eta := by
    intro eta heta
    obtain ⟨N0,hN0,hbound⟩ := exists_actual_trimmed_prime_pairs_threshold delta eta hd heta
    have hNat : ∀ᶠ N in l, N0 ≤ N := (eventually_ge_atTop N0).filter_mono inf_le_left
    have hEven : ∀ᶠ N in l, 0 < N ∧ Even N :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [hNat,hEven] with N hN hE
    exact hbound N hN hE.2
  exact tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w f g M hM hw hmass' hfg
/-- One-for-one replacement of the catalog5 physical slot by its actual
upper-factor integral.  The remaining unpaid slots stay in the partial ledger. -/
def sourceProfileLedger : ℝ :=
  physicalSecondLedger + physicalSaving - sourceProfileSaving

theorem sourceProfileLedger_eq_physicalSecondLedger :
    sourceProfileLedger = physicalSecondLedger := by
  rw [sourceProfileLedger,sourceProfileSaving_eq_physicalSaving]
  ring

theorem sourceProfileLedger_with_original_reserves_lt_K :
    sourceProfileLedger + densityReserve + compilerReserve < currentK := by
  rw [sourceProfileLedger_eq_physicalSecondLedger]
  exact physicalSecondLedger_with_original_reserves_lt_K

end
end ImbalancedChen.P4AOriginalSecondResidualSupplier





