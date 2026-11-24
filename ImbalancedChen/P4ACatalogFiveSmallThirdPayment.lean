import ImbalancedChen.P4ACatalogFiveSmallThirdEndpointTail

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Complete actual small-third omission payment on the original candidate
List, including disabled actions. The proof bounds the absolute sum of
all omitted endpoint rows, not only a signed cancellation. The generic
tiny and middle suppliers are joined to the original guarded carrier;
the resulting h threshold is chosen before the common mesh and N.
-/

namespace ImbalancedChen.P4ACatalogFiveSmallThirdPayment
noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P4AOriginalRankThreeRestorationSource P4ACatalogFiveActualPairDecomposition
open P4ACatalogFiveCoarseWeightedPayment P4ACatalogFiveOmittedOrderPayment
open P4ACatalogFiveSmallThirdMass P4ACatalogFiveSmallThirdEndpointTail
open P4ACatalogFiveGlobalLossReduction P4AOriginalSecondPhysicalIntegral
open P1OriginalFifthMovingScaleLimit

def smallOmittedAbsoluteSum (d : OriginalData) (h : ℝ) (N : ℕ) : ℝ :=
  ((candidates d (N:ℝ) weight (carrier N)).map (fun s =>
    if primeHistoryLogCoordinates (N:ℝ) 3 s.selectedPrefix 2 < h then
      |omittedRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ)/singularSeries N|
    else 0)).sum

def omittedAbsoluteSum (d : OriginalData) (N : ℕ) : ℝ :=
  ((candidates d (N:ℝ) weight (carrier N)).map (fun s =>
    |omittedRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ)/singularSeries N|)).sum

theorem guarded_small_candidate_mem_tailBox (d : OriginalData) (N : ℕ) (hN : 1 < N)
    (h : ℝ) (p : Fin 3 → ℕ) (hp : p ∈ candidateTuples d N)
    (hg : tupleGuard N p) (hs : actualPrimeTupleLog N p 2 < h) : p ∈ tailBox N h := by
  have hm := (mem_firstExitAdmittedTuples_iff_of_decreasing 3
    (beforeThirdPolicy (old3 d (N:ℝ))) (carrier N)
    (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (mem_roughPrimeUniverse_prime (hm.2.1 i)).pos
  have hn : (1:ℝ) < N := by exact_mod_cast hN
  have hu (i : Fin 3) : actualPrimeTupleLog N p i < (19/96:ℝ) := by
    apply (Real.rpow_lt_rpow_left_iff hn).mp
    rw [actualPrimeTupleLog_rpow hN p hpos i]
    exact (mem_roughPrimeUniverse.mp (hm.2.1 i)).2.2.2.2
  have hz0 : 0 ≤ actualPrimeTupleLog N p 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (mem_roughPrimeUniverse_prime (hm.2.1 2)).one_lt.le))
      (Real.log_pos hn).le
  obtain ⟨hx,hy,_,_⟩ := guard_geometry N p hg
  apply (mem_actualPrimeBoxTuples_log_iff hN lower (upper h) p).mpr
  refine ⟨?_,?_⟩
  · intro i
    have hi := mem_roughPrimeUniverse.mp (hm.2.1 i)
    exact ⟨hi.2.1,hi.2.2.1⟩
  · apply mem_logPrimeBox.mpr
    intro i
    fin_cases i
    · simpa [lower,upper] using And.intro hx (hu 0)
    · simpa [lower,upper] using And.intro hy (hu 1)
    · simpa [lower,upper] using And.intro hz0 hs

/-- Every original small omitted occurrence is charged to the actual
guarded box. No assertion that the disabled comparison term is zero. -/
theorem smallOmittedAbsoluteSum_le_tailAbsolute (d : OriginalData) (h : ℝ)
    (N : ℕ) (hN : 1 < N) : smallOmittedAbsoluteSum d h N ≤ tailAbsolute N h := by
  let F (p : Fin 3 → ℕ) := (∏ i, 1/((p i:ℝ)-1)) *
    (if tupleGuard N p ∧ actualPrimeTupleLog N p 2 < h then |endpointDifference N p| else 0)
  have hrow : ∀ s ∈ candidates d (N:ℝ) weight (carrier N),
      (if primeHistoryLogCoordinates (N:ℝ) 3 s.selectedPrefix 2 < h then
        |omittedRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ)/singularSeries N| else 0) ≤
        F (primeHistoryTuple 3 s.selectedPrefix) := by
    intro s hs
    obtain ⟨hlen,_,_,_,_,_,hmass⟩ := actualPrimeFrontier_geometry 3 (by omega)
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
    change (if actualPrimeTupleLog N p 2 < h then _ else 0) ≤ F p
    by_cases hz : actualPrimeTupleLog N p 2 < h
    · by_cases hg : tupleGuard N p
      · have hb := guarded_small_candidate_mem_tailBox d N hN h p ht hg hz
        have hw := actualPrimeBoxWeight_nonneg hb
        have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hb i).1.pos
        have hgp : secondGuard (N:ℝ) s.selectedPrefix := by simpa only [hp] using hg
        have hm : s.mass = ∏ i, 1/((p i:ℝ)-1) := by
          rw [hmass,← primeHistoryTuple_reciprocal_mass hlen]
        rw [if_pos hz]
        dsimp only [F]
        rw [if_pos ⟨hg,hz⟩]
        by_cases hsel : selectedThird d (N:ℝ) s.selectedPrefix
        · simp only [omittedRow,hsel,not_true_eq_false,and_false,if_false,zero_mul,zero_div,abs_zero]
          exact mul_nonneg hw (abs_nonneg _)
        · rw [omittedRow,if_pos ⟨hgp,hsel⟩,
            endpointRow_normalized_eq_gated_difference d N hN s hs p hp hpos hgp,abs_mul,hm,abs_of_nonneg hw]
          exact le_rfl
      · have hgp : ¬secondGuard (N:ℝ) s.selectedPrefix := by simpa only [hp] using hg
        simp [F,hz,hg,omittedRow,hgp]
    · simp [F,hz]
  have hsum : smallOmittedAbsoluteSum d h N ≤
      ((candidates d (N:ℝ) weight (carrier N)).map (fun s => F (primeHistoryTuple 3 s.selectedPrefix))).sum := by
    unfold smallOmittedAbsoluteSum
    generalize candidates d (N:ℝ) weight (carrier N) = L at hrow ⊢
    revert hrow
    induction L with
    | nil => intro hrow; simp
    | cons s L ih =>
      intro hrow
      simp only [List.map_cons,List.sum_cons]
      exact add_le_add (hrow s (by simp)) (ih (fun t ht => hrow t (by simp [ht])))
  have heq := firstExitRootFrontier_sum_eq_admitted_tuple_sum 3
    (beforeThirdPolicy (old3 d (N:ℝ))) weight (carrier N)
    (roughPrimeUniverse_nodup _ _ _ _) F
  change _ = ∑ p ∈ candidateTuples d N, F p at heq
  rw [heq] at hsum
  let S := (candidateTuples d N).filter (fun p => tupleGuard N p ∧ actualPrimeTupleLog N p 2 < h)
  have hf : (∑ p ∈ candidateTuples d N, F p) =
      ∑ p ∈ S, (∏ i, 1/((p i:ℝ)-1)) * (if tupleGuard N p then |endpointDifference N p| else 0) := by
    rw [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hg : tupleGuard N p <;> by_cases hz : actualPrimeTupleLog N p 2 < h <;> simp [F,hg,hz]
  rw [hf] at hsum
  apply hsum.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hg,hz⟩ := Finset.mem_filter.mp hp
    exact guarded_small_candidate_mem_tailBox d N hN h p hp hg hz
  · intro p hp _
    exact mul_nonneg (actualPrimeBoxWeight_nonneg hp) (by split_ifs <;> positivity)

theorem abs_smallOmittedSum_le (d : OriginalData) (h : ℝ) (N : ℕ) :
    |smallOmittedSum d h N| ≤ smallOmittedAbsoluteSum d h N := by
  unfold smallOmittedSum smallOmittedAbsoluteSum
  generalize candidates d (N:ℝ) weight (carrier N) = L
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons,List.sum_cons]
    by_cases hz : primeHistoryLogCoordinates (N:ℝ) 3 s.selectedPrefix 2 < h
    · rw [if_pos hz,if_pos hz]
      exact (abs_add _ _).trans (add_le_add le_rfl ih)
    · simpa only [if_neg hz,zero_add] using ih

theorem omittedAbsoluteSum_split (d : OriginalData) (h : ℝ) (N : ℕ) :
    omittedAbsoluteSum d N = smallOmittedAbsoluteSum d h N+compactOmittedAbsoluteSum d h N := by
  rw [compactOmittedAbsoluteSum_eq_actual]
  unfold omittedAbsoluteSum smallOmittedAbsoluteSum
  generalize candidates d (N:ℝ) weight (carrier N) = L
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons,List.sum_cons]
    by_cases hz : primeHistoryLogCoordinates (N:ℝ) 3 s.selectedPrefix 2 < h
    · rw [if_pos hz,if_neg (not_le_of_gt hz),ih]; ring
    · rw [if_neg hz,if_pos (le_of_not_gt hz),ih]; ring

/-- D is independent of h, all OriginalData, and the later target.
Both the microscopic part and the entire moving middle interval are paid. -/
theorem exists_uniform_smallOmittedAbsoluteSum_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ h : ℝ, 0 < h → h ≤ (19/96:ℝ)/6 →
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ d : OriginalData, smallOmittedAbsoluteSum d h N < D*h := by
  obtain ⟨A,B,hA,hB,hpoint⟩ := exists_eventually_endpointDifference_tail_bound
  obtain ⟨M,hM,Nm,hNm,hmoment⟩ := exists_uniform_secondMoment_bound
  let D := 1+B*M
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro h hh hhr
  have htiny : ∀ᶠ N : ℕ in atTop, A*normalizedMovingMajorant N < h := by
    have ht := normalizedMovingMajorant_tendsto_zero.const_mul A
    simpa only [mul_zero] using ht.eventually (gt_mem_nhds hh)
  have hpower : ∀ᶠ N : ℕ in atTop, 2 ≤ (N:ℝ)^h :=
    ((tendsto_rpow_atTop hh).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2:ℝ))
  obtain ⟨Np,hNp⟩ := eventually_atTop.mp hpoint
  obtain ⟨Nt,hNt⟩ := eventually_atTop.mp htiny
  obtain ⟨Nh,hNh⟩ := eventually_atTop.mp hpower
  refine ⟨max Nm (max Np (max Nt Nh)),hNm.trans (le_max_left _ _),?_⟩
  intro N hN hEven d
  have hNm' : Nm ≤ N := by omega
  have hNp' : Np ≤ N := by omega
  have hNt' : Nt ≤ N := by omega
  have hNh' : Nh ≤ N := by omega
  have hN1 := (hNp N hNp').1
  let E := A*|Real.log (N:ℝ)/singularSeries N|*Real.exp (-movingBudget N)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hfinite : tailAbsolute N h ≤
      E*(∑ p ∈ tailBox N h, ∏ i, 1/((p i:ℝ)-1))+B*secondMoment N h := by
    calc
      tailAbsolute N h ≤ ∑ p ∈ tailBox N h,
          (∏ i, 1/((p i:ℝ)-1))*(E+B*(actualPrimeTupleLog N p 2)^2) := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (actualPrimeBoxWeight_nonneg hp)
        by_cases hg : tupleGuard N p
        · rw [if_pos hg]
          exact (hNp N hNp').2 h hhr hEven p hp hg
        · rw [if_neg hg]
          exact add_nonneg hE (mul_nonneg hB.le (sq_nonneg _))
      _ = _ := by
        rw [Finset.mul_sum,secondMoment,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hmass := tailBox_mass_le_harmonic N hN1 h (by linarith)
  have hHp : (harmonicFactor N)^3 ≤ (harmonicFactor N)^5 :=
    pow_le_pow_right₀ (harmonicFactor_ge_one N hN1) (by norm_num : (3:ℕ) ≤ 5)
  have htinyBound : E*(∑ p ∈ tailBox N h, ∏ i, 1/((p i:ℝ)-1)) ≤
      A*normalizedMovingMajorant N := by
    have hh' := mul_le_mul_of_nonneg_left (hmass.trans hHp) hE
    convert hh' using 1 <;> dsimp [E,normalizedMovingMajorant] <;> ring
  have hm := hmoment N hNm' h hh (hNh N hNh')
  have hquad : h^2 ≤ h := by nlinarith
  calc
    smallOmittedAbsoluteSum d h N ≤ tailAbsolute N h := smallOmittedAbsoluteSum_le_tailAbsolute d h N hN1
    _ ≤ A*normalizedMovingMajorant N+B*(M*h^2) :=
      hfinite.trans (add_le_add htinyBound (mul_le_mul_of_nonneg_left hm hB.le))
    _ < h+B*(M*h^2) := add_lt_add_right (hNt N hNt') _
    _ ≤ h+B*(M*h) := add_le_add_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hquad hM.le) hB.le) _
    _ = D*h := by dsimp [D]; ring

/-- The complete omittedRow ABSOLUTE sum, including every disabled-small
comparison row. Cutoff first, then one order width and one N0, all before d. -/
theorem exists_complete_omittedRow_payment (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ h0 : ℝ, 0 < h0 ∧ h0 < (19/96:ℝ) ∧
      ∀ h : ℝ, 0 < h → h ≤ h0 →
      ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ d : OriginalData, d.omega ≤ h →
        P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ d.chi →
        2*P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
      ∀ N : ℕ, N0 ≤ N → Even N → omittedAbsoluteSum d N < epsilon := by
  obtain ⟨D,hD,htail⟩ := exists_uniform_smallOmittedAbsoluteSum_bound
  let h0 := min ((19/96:ℝ)/12) (epsilon/(4*D))
  have hh0 : 0 < h0 := lt_min (by norm_num) (by positivity)
  have hh0rho : h0 < (19/96:ℝ) := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨h0,hh0,hh0rho,?_⟩
  intro h hh hhh
  obtain ⟨Nt,hNt,ht⟩ := htail h hh (by have := hhh.trans (min_le_left _ _); linarith)
  obtain ⟨delta,hd,No,hNo,ho⟩ := exists_compact_omittedRow_payment h (epsilon/2)
    hh (hhh.trans_lt hh0rho) (by positivity)
  refine ⟨delta,hd,max Nt No,hNt.trans (le_max_left _ _),?_⟩
  intro d homega hmesh hwidth N hN hEven
  have hs := ht N ((le_max_left _ _).trans hN) hEven d
  have hc := ho d homega hmesh hwidth N ((le_max_right _ _).trans hN) hEven
  have hcut : D*h ≤ epsilon/4 := by
    have hh' := hhh.trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0<4*D)).mp hh'
    nlinarith
  rw [omittedAbsoluteSum_split d h N]
  linarith

/-- Whole actual catalog-five approximation for the original policy.
The small-tail choice precedes the coarse/trim/order widths and target;
the final d is one common original historical instance. -/
theorem exists_complete_actual_catalog5_approx (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ h0 : ℝ, 0 < h0 ∧ h0 < (19/96:ℝ) ∧
      ∀ h : ℝ, 0 < h → h ≤ h0 →
      ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ d : OriginalData, d.omega = h →
        0 < (d.e:ℝ) → (d.e:ℝ) < (3/256:ℝ)/100 → d.chi < (d.e:ℝ)/10 →
        P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ d.chi →
        4*(d.e:ℝ)+P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
        (3/2:ℝ)*d.chi+2*(d.e:ℝ) ≤ delta →
        2*P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
      ∀ N : ℕ, N0 ≤ N → Even N →
        |normalizedActualSaving d N-physicalSaving| < epsilon := by
  obtain ⟨D,hD,htail⟩ := exists_uniform_smallOmittedAbsoluteSum_bound
  let h0 := min ((19/96:ℝ)/12) (epsilon/(4*D))
  have hh0 : 0 < h0 := lt_min (by norm_num) (by positivity)
  have hh0rho : h0 < (19/96:ℝ) := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨h0,hh0,hh0rho,?_⟩
  intro h hh hhh
  obtain ⟨Nt,hNt,ht⟩ := htail h hh (by have := hhh.trans (min_le_left _ _); linarith)
  obtain ⟨delta,hd,Nr,hNr,hr⟩ := exists_actual_saving_approx_with_small_omission
    h (epsilon/2) hh (hhh.trans_lt hh0rho) (by positivity)
  refine ⟨delta,hd,max Nt Nr,hNt.trans (le_max_left _ _),?_⟩
  intro d homega he hesmall hchi hmesh hp hc ho N hN hEven
  have hs := (abs_smallOmittedSum_le d h N).trans_lt
    (ht N ((le_max_left _ _).trans hN) hEven d)
  have hres := hr d homega he hesmall hchi hmesh hp hc ho N ((le_max_right _ _).trans hN) hEven
  have hcut : D*h ≤ epsilon/4 := by
    have hh' := hhh.trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0<4*D)).mp hh'
    nlinarith
  have htri : |normalizedActualSaving d N-physicalSaving| ≤
      |normalizedActualSaving d N+smallOmittedSum d h N-physicalSaving|+|smallOmittedSum d h N| := by
    calc
      _ = |(normalizedActualSaving d N+smallOmittedSum d h N-physicalSaving)-smallOmittedSum d h N| := by
        congr 1 <;> ring
      _ ≤ _ := abs_sub _ _
  linarith

end
end ImbalancedChen.P4ACatalogFiveSmallThirdPayment
