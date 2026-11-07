import ImbalancedChen.P4ACatalogFiveCoarseWeightedPayment
import ImbalancedChen.AffinePrimeWallReserve
import ImbalancedChen.ActualExtendedThirdLowerFactorRegularity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The part of Q's actual omittedRow with p3 >= N^h is paid on the two
original ordering walls. The firstStop is supplied from the same actual
before-third history. Every strict prime atom is retained in the closed
wall-strip mass. The proof bounds the complete endpoint continuation
difference behind its admission gates, including old-rejected nodes.

The complementary p3 < N^h sum is retained exactly. In particular the
disabled-small-third branch has not been assigned zero omission.
-/

namespace ImbalancedChen.P4ACatalogFiveOmittedOrderPayment
noncomputable section
open Set Filter Topology VariableEnvelope HistoricalThirdCoarse
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonThirdScreenedSource
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P4AOriginalRankThreeRestorationSource P4ACatalogFiveActualPairDecomposition
open P4ACatalogFiveCoarseResidualUniformity P4ACatalogFiveCoarseWeightedPayment

def orderForms : Fin 2 → (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ![ContinuousLinearMap.proj 0-ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 1-ContinuousLinearMap.proj 2]

theorem orderForms_ne_zero (i : Fin 2) : orderForms i ≠ 0 := by
  intro h
  have hh := congrArg (fun F : (Fin 3 → ℝ) →L[ℝ] ℝ => F ![1,2,4]) h
  fin_cases i <;> norm_num [orderForms] at hh

def compactMask (d : OriginalData) (h : ℝ) (N : ℕ) (pre : List ℕ) : Prop :=
  h ≤ primeHistoryLogCoordinates (N:ℝ) 3 pre 2 ∧
    secondGuard (N:ℝ) pre ∧ ¬selectedThird d (N:ℝ) pre

def compactOmittedMass (d : OriginalData) (h : ℝ) (N : ℕ) : ℝ :=
  ((candidates d (N:ℝ) weight (carrier N)).map (fun s =>
    if compactMask d h N s.selectedPrefix then s.mass else 0)).sum

def compactOmittedAbsoluteSum (d : OriginalData) (h : ℝ) (N : ℕ) : ℝ :=
  ((candidates d (N:ℝ) weight (carrier N)).map (fun s =>
    if compactMask d h N s.selectedPrefix then
      |endpointRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N|
    else 0)).sum

/-- The definition is precisely the above-cutoff part of actual omittedRow. -/
theorem compactOmittedAbsoluteSum_eq_actual (d : OriginalData) (h : ℝ) (N : ℕ) :
    compactOmittedAbsoluteSum d h N =
      ((candidates d (N:ℝ) weight (carrier N)).map (fun s =>
        if h ≤ primeHistoryLogCoordinates (N:ℝ) 3 s.selectedPrefix 2 then
          |omittedRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N|
        else 0)).sum := by
  unfold compactOmittedAbsoluteSum
  congr 1
  apply List.map_congr_left
  intro s hs
  by_cases hc : h ≤ primeHistoryLogCoordinates (N:ℝ) 3 s.selectedPrefix 2
  · by_cases hg : secondGuard (N:ℝ) s.selectedPrefix ∧ ¬selectedThird d (N:ℝ) s.selectedPrefix
    · simp [compactMask,omittedRow,hc,hg,hg.1,hg.2]
    · simp [compactMask,omittedRow,hc,hg]
  · simp [compactMask,omittedRow,hc]

theorem endpointRow_normalized_eq_gated_difference
    (d : OriginalData) (N : ℕ) (hN : 1 < N) (s : FirstExitDepthState ℕ)
    (hs : s ∈ candidates d (N:ℝ) weight (carrier N))
    (p : Fin 3 → ℕ) (hp : s.selectedPrefix = [p 2,p 1,p 0])
    (hpos : ∀ i, 0 < p i) (hg : secondGuard (N:ℝ) s.selectedPrefix) :
    endpointRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N =
      s.mass * (actualPrimeTupleOwnCubeMinus N N (v (actualPrimeTupleLog N p 1)) p -
        actualPrimeTupleOwnCubeMinus N N (v (actualPrimeTupleLog N p 0)) p) := by
  have hc (new : Bool) := endpoint_pairCap_cube N hN p hpos (hp ▸ hg) new
  have hQ (new : Bool) : pairCap (N:ℝ) new (rosserAncestor 2 s.selectedPrefix) =
      (N:ℝ)^v (actualPrimeTupleLog N p (if new then 1 else 0)) := by
    cases new <;>
      simp [hp,pairCap,rosserAncestor,primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog]
  rw [endpointRow,sub_mul,sub_div,
    endpoint_admitted_eq_ordinary d N false s hs hg,
    endpoint_admitted_eq_ordinary d N true s hs hg,
    admittedOrdinary_normalized d N s hs p hp (hpos 2) _ (by simpa only [hp] using hc false),
    admittedOrdinary_normalized d N s hs p hp (hpos 2) _ (by simpa only [hp] using hc true),
    hQ false,hQ true]
  change -s.mass * actualPrimeTupleOwnCubeMinus N N _ p -
    -s.mass * actualPrimeTupleOwnCubeMinus N N _ p = _
  ring

/-- Uniform absolute lower-residual bound on the fixed positive cube,
derived from Q's all-cap theorem and the canonical factor bound. -/
theorem exists_compact_gated_residual_bound (h : ℝ) (hh : 0 < h) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ)),
      ∀ lam : ℝ, lam ≤ thirdPrefixTheta → |actualPrimeTupleOwnCubeMinus N N lam p| ≤ B := by
  let C := 4*(1/(2*Real.exp Real.eulerMascheroniConstant))/h
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N0,hN0,hbound⟩ := exists_all_caps_ownCube_uniform_threshold h 1 hh (by norm_num)
  refine ⟨C+1,by linarith,N0,hN0,?_⟩
  intro N hN hEven p hp lam hlam
  have hN1 : 1 < N := by omega
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN1.le
  have hcap : (N:ℝ)^(19/96:ℝ) ≤ (N:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr
      (by norm_num : (19/96:ℝ) ≤ 1)
  have hz := (mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2 2).1
  have hz0 : 0 < actualPrimeTupleLog N p 2 := hh.trans_le hz
  have hprofile : |primeTupleMinusProfile lam (actualPrimeTupleLog N p)| ≤ C := by
    rw [primeTupleMinusProfile_eq_extendedThirdFactor _ _ hz0]
    have hn := actualExtendedThirdLowerFactor_nonneg
      ((lam-actualPrimeTupleLog N p 0-actualPrimeTupleLog N p 1-actualPrimeTupleLog N p 2) /
        actualPrimeTupleLog N p 2)
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hn) hz0.le)]
    calc
      _ ≤ 4*(1/(2*Real.exp Real.eulerMascheroniConstant))/actualPrimeTupleLog N p 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (actualExtendedThirdLowerFactor_le_normalization _) (by norm_num)) hz0.le
      _ ≤ C := div_le_div_of_nonneg_left (by positivity) hh hz
  have hr := hbound N hN hEven N hcap p hp lam hlam
  have ht := abs_add (actualPrimeTupleOwnCubeMinus N N lam p-
    primeTupleMinusProfile lam (actualPrimeTupleLog N p))
    (primeTupleMinusProfile lam (actualPrimeTupleLog N p))
  rw [sub_add_cancel] at ht
  linarith

theorem candidate_cutoff_mem_box (d : OriginalData) (h : ℝ) (N : ℕ) (hN : 1 < N)
    (p : Fin 3 → ℕ) (hp : p ∈ candidateTuples d N)
    (hlow : h ≤ actualPrimeTupleLog N p 2) :
    p ∈ actualPrimeBoxTuples N (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ)) := by
  have hm := (mem_firstExitAdmittedTuples_iff_of_decreasing 3
    (beforeThirdPolicy (old3 d (N:ℝ))) (carrier N)
    (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (mem_roughPrimeUniverse_prime (hm.2.1 i)).pos
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN.le
  have hp2 : (N:ℝ)^h ≤ (p 2:ℝ) := by
    rw [← actualPrimeTupleLog_rpow hN p hpos 2]
    exact Real.rpow_le_rpow_of_exponent_le hNr hlow
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  have hi := mem_roughPrimeUniverse.mp (hm.2.1 i)
  have hord : p 2 ≤ p i := hm.1.antitone (by omega)
  exact ⟨hi.2.1,hi.2.2.1,hp2.trans (by exact_mod_cast hord),hi.2.2.2.2⟩

theorem compact_omitted_tuple_in_order_strip
    (d : OriginalData) (h delta : ℝ) (hh : 0 < h) (homega : d.omega ≤ h)
    (hmesh : P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ d.chi)
    (hwidth : 2*P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta)
    (N : ℕ) (hN : 1 < N) (p : Fin 3 → ℕ) (hp : p ∈ candidateTuples d N)
    (hm : compactMask d h N (List.ofFn p).reverse) :
    actualPrimeTupleLog N p ∈ primeAffineWallStrip orderForms (fun _ => 0) delta := by
  have hpre : (List.ofFn p).reverse = [p 2,p 1,p 0] := by simp [List.ofFn_succ]
  have hlog : primeHistoryLogCoordinates (N:ℝ) 3 [p 2,p 1,p 0] = actualPrimeTupleLog N p :=
    HistoricalThirdCoarse.P1ActualTuple.history_log N p
  have hm' : h ≤ actualPrimeTupleLog N p 2 ∧ secondGuard (N:ℝ) [p 2,p 1,p 0] ∧
      ¬selectedThird d (N:ℝ) [p 2,p 1,p 0] := by
    simpa only [compactMask,hpre,hlog] using hm
  have hd := (mem_firstExitAdmittedTuples_iff_of_decreasing 3
    (beforeThirdPolicy (old3 d (N:ℝ))) (carrier N)
    (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (mem_roughPrimeUniverse_prime (hd.2.1 i)).pos
  have hb := candidate_cutoff_mem_box d h N hN p hp hm'.1
  have ht := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hb).2
  have ht0 : actualPrimeTupleLog N p ∈ logPrimeBox (fun _ : Fin 3 => 0) (fun _ => (19/96:ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro i
    exact ⟨hh.le.trans (mem_logPrimeBox.mp ht i).1,(mem_logPrimeBox.mp ht i).2⟩
  obtain ⟨j,hj⟩ := exists_logPrimeMeshCell 0 (19/96) d.m ht0
  have hv : FirstExitValidSelection (beforeThirdPolicy (old3 d (N:ℝ))) [] true [p 0,p 1,p 2] := by
    simpa [List.ofFn_succ] using hd.2.2
  have hfirst : old3 d (N:ℝ) false [p 0] = true := by
    simpa [beforeThirdPolicy,firstExitDepthSplicePolicy] using hv.1
  have hstop := (P1OriginalFirstStopInheritance.singleton_original_tests
    (d.e:ℝ) d.chi d.m d.omega (N:ℝ) (p 0) hfirst).2.1
  have hbad := P4ACatalogFiveHistoricalCoverage.actual_unsupported_third_in_tail_or_order_strips
    d (N:ℝ) (p 0) (p 1) (p 2) j (hlog.symm ▸ hj) hmesh hstop hm'.2.2
  rw [hlog] at hbad
  have hNr : (1:ℝ) < N := by exact_mod_cast hN
  have hrough : (N:ℝ)^d.omega ≤ (p 2:ℝ) := by
    rw [← actualPrimeTupleLog_rpow hN p hpos 2]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le (homega.trans hm'.1)
  have horder (i j : Fin 3) (hij : i < j) : actualPrimeTupleLog N p j < actualPrimeTupleLog N p i := by
    apply (Real.rpow_lt_rpow_left_iff hNr).mp
    rw [actualPrimeTupleLog_rpow hN p hpos,actualPrimeTupleLog_rpow hN p hpos]
    exact_mod_cast hd.1 hij
  rcases hbad with hbad | hbad | hbad
  · exact (not_lt_of_ge hrough hbad).elim
  · refine ⟨0,?_⟩
    have ho := horder 0 1 (by decide)
    simpa [orderForms,abs_of_nonneg (sub_nonneg.mpr ho.le)] using hbad.le.trans hwidth
  · refine ⟨1,?_⟩
    have ho := horder 1 2 (by decide)
    simpa [orderForms,abs_of_nonneg (sub_nonneg.mpr ho.le)] using hbad.le.trans hwidth

theorem compactOmittedMass_le_order_strip
    (d : OriginalData) (h delta : ℝ) (hh : 0 < h) (homega : d.omega ≤ h)
    (hmesh : P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ d.chi)
    (hwidth : 2*P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta)
    (N : ℕ) (hN : 1 < N) :
    compactOmittedMass d h N ≤ actualPrimeAffineWallStripMass N
      (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ)) orderForms (fun _ => 0) delta := by
  have heq : compactOmittedMass d h N =
      ∑ p ∈ (candidateTuples d N).filter (fun p => compactMask d h N (List.ofFn p).reverse),
        ∏ i, 1 / ((p i:ℝ)-1) := by
    have ht := firstExitRootFrontier_history_sum_eq_admitted_tuple_sum 3
      (beforeThirdPolicy (old3 d (N:ℝ))) weight (carrier N) (roughPrimeUniverse_nodup _ _ _ _)
      (fun pre => if compactMask d h N pre then (1:ℝ) else 0)
    rw [Finset.sum_filter]
    convert ht using 1
    · unfold compactOmittedMass candidates
      congr 1
      apply List.map_congr_left
      intro s hs
      have hm := (actualPrimeFrontier_geometry 3 (by omega)
        (beforeThirdPolicy (old3 d (N:ℝ))) N N ((N:ℝ)^(19/96:ℝ)) s hs).2.2.2.2.2.2
      split_ifs <;> simp [hm]
    · apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hm := Finset.mem_filter.mp hp
    have hpre : (List.ofFn p).reverse = [p 2,p 1,p 0] := by simp [List.ofFn_succ]
    have hl : h ≤ actualPrimeTupleLog N p 2 := by
      simpa [hpre,primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog] using hm.2.1
    exact Finset.mem_filter.mpr ⟨candidate_cutoff_mem_box d h N hN p hm.1 hl,
      compact_omitted_tuple_in_order_strip d h delta hh homega hmesh hwidth N hN p hm.1 hm.2⟩
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- Actual full-continuation omission above h is arbitrarily small once
the original full-rectangle mesh is fine enough. The width and threshold
precede every d and N; no wall mass or source error is assumed. -/
theorem exists_compact_omittedRow_payment (h epsilon : ℝ)
    (hh : 0 < h) (hhrho : h < (19/96:ℝ)) (heps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ d : OriginalData, d.omega ≤ h →
        P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ d.chi →
        2*P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
      ∀ N : ℕ, N0 ≤ N → Even N → compactOmittedAbsoluteSum d h N < epsilon := by
  obtain ⟨B,hB,Nb,hNb,hbound⟩ := exists_compact_gated_residual_bound h hh
  obtain ⟨delta,hd,Ns,hNs,hstrip⟩ := exists_actualPrimeAffineWallStrip_mass_lt hh hhrho
    orderForms (fun _ => 0) orderForms_ne_zero (epsilon/(2*B)) (by positivity)
  refine ⟨delta,hd,max Nb Ns,hNb.trans (le_max_left _ _),?_⟩
  intro d homega hmesh hwidth N hN hEven
  have hN1 : 1 < N := by omega
  have hrow : ∀ s ∈ candidates d (N:ℝ) weight (carrier N),
      (if compactMask d h N s.selectedPrefix then
        |endpointRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N| else 0) ≤
      2*B*(if compactMask d h N s.selectedPrefix then s.mass else 0) := by
    intro s hs
    by_cases hm : compactMask d h N s.selectedPrefix
    · obtain ⟨hlen,_,_,_,_,_,hmass⟩ := actualPrimeFrontier_geometry 3 (by omega)
        (beforeThirdPolicy (old3 d (N:ℝ))) N N ((N:ℝ)^(19/96:ℝ)) s hs
      let p := primeHistoryTuple 3 s.selectedPrefix
      have hp : s.selectedPrefix = [p 2,p 1,p 0] := by
        simpa [List.ofFn_succ] using (primeHistoryTuple_reverse_ofFn hlen).symm
      have ht : p ∈ candidateTuples d N := by
        apply List.mem_toFinset.mpr
        apply List.mem_map.mpr
        refine ⟨s.selectedPrefix.reverse,?_,?_⟩
        · exact (firstExitRootFrontier_admitted_history_perm 3
            (beforeThirdPolicy (old3 d (N:ℝ))) weight (carrier N)).mem_iff.mp
              (List.mem_map.mpr ⟨s,hs,rfl⟩)
        · simp only [List.reverse_reverse]; rfl
      have hlow : h ≤ actualPrimeTupleLog N p 2 := hm.1
      have hb := candidate_cutoff_mem_box d h N hN1 p ht hlow
      have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hb i).1.pos
      have hv (i : Fin 3) : v (actualPrimeTupleLog N p i) ≤ thirdPrefixTheta := by
        have hh := v_le_cap (actualPrimeTupleLog N p i)
        dsimp [cap,thirdPrefixTheta] at *
        linarith
      have ho := hbound N ((le_max_left _ _).trans hN) hEven p hb _ (hv 0)
      have hn := hbound N ((le_max_left _ _).trans hN) hEven p hb _ (hv 1)
      have hdiff := (abs_sub _ _).trans (add_le_add hn ho)
      have hw : 0 ≤ s.mass := by
        rw [hmass,← primeHistoryTuple_reciprocal_mass hlen]
        exact actualPrimeBoxWeight_nonneg hb
      rw [if_pos hm,if_pos hm,endpointRow_normalized_eq_gated_difference d N hN1 s hs p hp hpos hm.2.1,
        abs_mul,abs_of_nonneg hw]
      have hh := mul_le_mul_of_nonneg_left hdiff hw
      nlinarith
    · simp only [if_neg hm,mul_zero,le_refl]
  have hsum : compactOmittedAbsoluteSum d h N ≤ 2*B*compactOmittedMass d h N := by
    unfold compactOmittedAbsoluteSum compactOmittedMass
    generalize candidates d (N:ℝ) weight (carrier N) = L at hrow ⊢
    revert hrow
    induction L with
    | nil => intro hrow; simp
    | cons s L ih =>
      intro hrow
      simp only [List.map_cons,List.sum_cons]
      have hs := hrow s (by simp)
      have hh := ih (fun t ht => hrow t (by simp [ht]))
      nlinarith
  have hm := compactOmittedMass_le_order_strip d h delta hh homega hmesh hwidth N hN1
  have hs := hstrip N ((le_max_right _ _).trans hN)
  calc
    _ ≤ 2*B*compactOmittedMass d h N := hsum
    _ ≤ 2*B*actualPrimeAffineWallStripMass N (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ))
        orderForms (fun _ => 0) delta := mul_le_mul_of_nonneg_left hm (by positivity)
    _ < epsilon := by
      have hh := (lt_div_iff₀ (by positivity : 0<2*B)).mp hs
      simpa only [mul_comm] using hh

/-- The unbounded small-third part remains an actual signed source sum. -/
def smallOmittedSum (d : OriginalData) (h : ℝ) (N : ℕ) : ℝ :=
  ((candidates d (N:ℝ) weight (carrier N)).map (fun s =>
    if primeHistoryLogCoordinates (N:ℝ) 3 s.selectedPrefix 2 < h then
      omittedRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N
    else 0)).sum

theorem omitted_sum_sub_small_abs_le (d : OriginalData) (h : ℝ) (N : ℕ) :
    |((candidates d (N:ℝ) weight (carrier N)).map (fun s =>
        omittedRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N)).sum -
      smallOmittedSum d h N| ≤ compactOmittedAbsoluteSum d h N := by
  rw [compactOmittedAbsoluteSum_eq_actual]
  unfold smallOmittedSum
  generalize candidates d (N:ℝ) weight (carrier N) = L
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons,List.sum_cons]
    by_cases ht : h ≤ primeHistoryLogCoordinates (N:ℝ) 3 s.selectedPrefix 2
    · rw [if_pos ht,if_neg (not_lt_of_ge ht)]
      have ha := abs_add
        (omittedRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N)
        ((L.map (fun s => omittedRow d (N:ℝ) weight (fun _ _ => 1) s *
          Real.log (N:ℝ) / singularSeries N)).sum -
          (L.map (fun s => if primeHistoryLogCoordinates (N:ℝ) 3 s.selectedPrefix 2 < h then
            omittedRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N else 0)).sum)
      simp only [zero_add,add_sub_assoc] at *
      linarith
    · rw [if_neg ht,if_pos (lt_of_not_ge ht)]
      simpa only [zero_add,add_sub_add_left_eq_sub] using ih

end
end ImbalancedChen.P4ACatalogFiveOmittedOrderPayment
