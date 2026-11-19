import ImbalancedChen.P2Historical246WallFaceAtoms

/-! SOURCE ONLY / UNEVALUATED. Finite sum for one literal H246 prime
face and any subset of that face. The uniform limit covers only lanes
0 and 2 per parent. Both-face and marked-book payments remain open. -/
namespace ImbalancedChen.P2Historical246WallFaceSum
noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2Historical246SuccessorParentWindow
open P2Historical246RepeatedCeilingAtom P2OriginalPositiveSameQMassLift
open P2Historical246PairCarrierPartition P2Historical246WallFaceAtoms
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalHalfOpenProfileCarrier P2OriginalCompactScaledPrimeMass
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

/-- The nonfixed coordinate as a literal one-prime tuple. -/
def otherProjection (i : Fin 2) (p : Pair) : Fin 1 → ℕ := fun _ => p (1-i)

/-- Exact face projection is injective; its image is a sub-box of the
original N-deleted one-dimensional prime carrier. -/
theorem face_reciprocal_sum_le_box {N : ℕ} {L : ℝ}
    (hN : 1 < N) (hL : 0 < L) (j : Fin 36) (k : Fin 4)
    (i : Fin 2) (r : ℝ) (S : Finset Pair)
    (hS : ∀ p ∈ S, p ∈ halfCarrier N L j k ∧ normalizedLog N L p i = r) :
    (∑ p ∈ S, 1/((p (1-i) : ℝ)-1)) ≤
      actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  have hsubset : S.image (otherProjection i) ⊆ actualPrimeBoxTuples N
      (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    have hbox := (Finset.mem_filter.mp (hS p hp).1).1
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro a
    fin_cases a
    simpa [otherProjection] using (mem_actualPrimeBoxTuples_iff.mp hbox (1-i))
  have hsum : (∑ p ∈ S, 1/((p (1-i) : ℝ)-1)) =
      ∑ q ∈ S.image (otherProjection i), 1/((q 0 : ℝ)-1) := by
    symm
    apply Finset.sum_image
    intro p hp q hq heq
    apply fixed_face_other_injective hN hL j k i r (hS p hp).1 (hS q hq).1
      (hS p hp).2 (hS q hq).2
    simpa [otherProjection] using congrFun heq 0
  rw [hsum]
  unfold actualPrimeBoxMass
  simp only [Fin.prod_univ_one]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
  intro q hq _
  have hprime := (mem_actualPrimeBoxTuples_iff.mp hq 0).1
  have hr : (0 : ℝ) < (q 0 : ℝ)-1 := by
    have h : (1 : ℝ) < q 0 := by exact_mod_cast hprime.one_lt
    linarith
  exact (one_div_pos.mpr hr).le

/-- A single fixed-coordinate face, or any literal subset of it, has a
finite H246 atom bound. No wall intersection is removed here. -/
theorem face_atom_sum_bound {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (hA : 4 ≤ (N : ℝ)^(L/10)) (j : Fin 36) (k : Fin 4)
    (i : Fin 2) (r : ℝ) (S : Finset Pair)
    (hS : ∀ p ∈ S, p ∈ halfCarrier N L j k ∧ normalizedLog N L p i = r) :
    |∑ p ∈ S, oldPairAtom N Q L (parentProduct old) j k p| ≤
      |thetaAtom N Q (parentProduct old)| *
        ((80*floorBound (outputAt 246 true))/((N : ℝ)^(L/10))) *
          actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  let A : ℝ := (N : ℝ)^(L/10)
  let B : ℝ := floorBound (outputAt 246 true)
  have hApos : 0 < A := by dsimp [A]; linarith
  have hB : 0 ≤ B := by dsimp [B]; exact floorBound_nonneg _
  have hcoef : 0 ≤ |thetaAtom N Q (parentProduct old)| * ((80*B)/A) :=
    mul_nonneg (abs_nonneg _) (div_nonneg (mul_nonneg (by norm_num) hB) hApos.le)
  calc
    |∑ p ∈ S, oldPairAtom N Q L (parentProduct old) j k p| ≤
        ∑ p ∈ S, |oldPairAtom N Q L (parentProduct old) j k p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, (|thetaAtom N Q (parentProduct old)| * ((80*B)/A)) *
        (1/((p (1-i) : ℝ)-1)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpbox := (Finset.mem_filter.mp (hS p hp).1).1
      have hpi := (mem_actualPrimeBoxTuples_iff.mp hpbox i).2.2.1
      have hpo := (mem_actualPrimeBoxTuples_iff.mp hpbox (1-i)).1
      have hri : (0 : ℝ) < (p i : ℝ)-1 := by dsimp [A] at *; linarith
      have hro : (0 : ℝ) < (p (1-i) : ℝ)-1 := by
        have h : (1 : ℝ) < p (1-i) := by exact_mod_cast hpo.one_lt
        linarith
      have hinv : 1/((p i : ℝ)-1) ≤ 2/A := by
        apply (div_le_div_iff₀ hri hApos).2
        dsimp [A] at *
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hinv (one_div_pos.mpr hro).le
      have hcomp : (2*(1/((p 0 : ℝ)-1))) * (2*(1/((p 1 : ℝ)-1))) ≤
          (8/A)*(1/((p (1-i) : ℝ)-1)) := by
        fin_cases i <;> norm_num at hmul ⊢ <;> nlinarith only [hmul]
      have hbound := full_pair_atom_bound hN hd hL hQ hA j k (hS p hp).1
      calc
        _ ≤ |thetaAtom N Q (parentProduct old)| *
            ((2*(1/((p 0 : ℝ)-1))) * (2*(1/((p 1 : ℝ)-1)))) * (10*B) := hbound
        _ ≤ (|thetaAtom N Q (parentProduct old)| * ((8/A)*(1/((p (1-i) : ℝ)-1)))) * (10*B) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp (abs_nonneg _))
            (mul_nonneg (by norm_num) hB)
        _ = _ := by ring
    _ = (|thetaAtom N Q (parentProduct old)| * ((80*B)/A)) *
        (∑ p ∈ S, 1/((p (1-i) : ℝ)-1)) := by rw [Finset.mul_sum]
    _ ≤ (|thetaAtom N Q (parentProduct old)| * ((80*B)/A)) *
        actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) :=
      mul_le_mul_of_nonneg_left (face_reciprocal_sum_le_box hN hL j k i r S hS) hcoef
    _ = _ := rfl


/-- For the original lanes 0 and 2 the complete lower wall is just
x0=a0. The wall is summed as a finite prime carrier, never erased. -/
theorem single_face_wall_atom_sum_bound {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (hA : 4 ≤ (N : ℝ)^(L/10)) (j : Fin 36) (k : Fin 4)
    (hk : k = 0 ∨ k = 2) :
    |∑ p ∈ (halfCarrier N L j k).filter (fun p => ¬ interior N L j k p),
      oldPairAtom N Q L (parentProduct old) j k p| ≤
      |thetaAtom N Q (parentProduct old)| *
        ((80*floorBound (outputAt 246 true))/((N : ℝ)^(L/10))) *
          actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  apply face_atom_sum_bound hN hd hL hQ hA j k 0 (a0 (originalW2At j))
  intro p hp
  obtain ⟨hp,hnot⟩ := Finset.mem_filter.mp hp
  refine ⟨hp,?_⟩
  have hw := noninterior_is_lower_wall hp hnot
  rcases hk with rfl | rfl <;> simpa [pairLowerWall] using hw


/-- One threshold before actual successor tuples and rows: for each of
the single-face lanes, its complete literal wall is epsilon times the
same parent Theta atom. This is before the W2 /5 and book summation. -/
theorem successor_single_face_wall_uniform {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu, ∀ (j : Fin 36) (k : Fin 4), k = 0 ∨ k = 2 →
      let Q := (N : ℝ)^nu
      let old := oldWord t
      let L := residualExponent N (parentProduct old) nu
      |∑ p ∈ (halfCarrier N L j k).filter (fun p => ¬ interior N L j k p),
        oldPairAtom N Q L (parentProduct old) j k p| ≤
        epsilon * thetaAtom N Q (parentProduct old) := by
  let lo := floorAt eta (horizon+1)
  let C : ℝ := 80*floorBound (outputAt 246 true)
  have hlo : 0 < lo := floorAt_pos he (horizon+1)
  have hC : 0 ≤ C := by dsimp [C]; exact mul_nonneg (by norm_num) (floorBound_nonneg _)
  have hpow := tendsto_nat_log_pow_div_rpow 0 (show 0 < lo/10 by positivity)
  simp only [pow_zero] at hpow
  have hmass := tendsto_actualPrimeBoxMass (fun _ : Fin 1 => lo/20) (fun _ => max 1 lo)
    (fun _ => by positivity) (fun _ => by have h := le_max_right (1 : ℝ) lo; linarith)
  have hlimit : Tendsto (fun N : ℕ => (C/(N : ℝ)^(lo/10)) *
      actualPrimeBoxMass N (fun _ : Fin 1 => lo/20) (fun _ => max 1 lo)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,mul_one_div] using (hpow.const_mul C).mul hmass
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp (hlimit.eventually (gt_mem_nhds heps))
  obtain ⟨T1,hT1,hfloor⟩ := successor_pair_floor_uniform he horizon
  refine ⟨max T1 (max 4 T0),?_,?_⟩
  · exact (le_max_left 4 T0).trans (le_max_right T1 _)
  · intro N hN nu hnu m choice hm t ht j k hk
    have hN1 : 1 < N := by omega
    have hn := advance_boxRows m choice hm
    have hf := (advance m choice).source_facts hN1 he hn ht
    have htrue := facts_trueAlpha hN1 hlo hf
    have hleft : lo ≤ residualExponent N (parentProduct (oldWord t)) nu := by
      rw [oldWord_product]
      linarith only [htrue.2.1,hlo]
    have hd1 : (1 : ℝ) ≤ Part3.labelledProduct t := by exact_mod_cast htrue.1
    have hbeta : 0 ≤ prefixExponent N (Part3.labelledProduct t) :=
      div_nonneg (Real.log_nonneg hd1) (Real.log_pos (by exact_mod_cast hN1)).le
    have hright : residualExponent N (parentProduct (oldWord t)) nu ≤ max 1 lo := by
      rw [oldWord_product]
      have hu : residualExponent N (Part3.labelledProduct t) nu ≤ 1 := by
        unfold residualExponent
        linarith only [hnu,hbeta]
      exact hu.trans (le_max_left _ _)
    obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level hN1 he m choice hm ht
    have htheta : 0 ≤ thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) :=
      thetaAtom_nonneg (by omega) hd (sameQ_residual_gt_one hN1 hd hL hQ)
    have hpowle : (N : ℝ)^(lo/10) ≤
        (N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le : (1 : ℝ) ≤ N)
      linarith
    have hpowpos : (0 : ℝ) < (N : ℝ)^(lo/10) := by positivity
    have hcoeff : C/(N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10) ≤
        C/(N : ℝ)^(lo/10) := div_le_div_of_nonneg_left hC hpowpos hpowle
    have hmove := moving_box_mass_le_ambient (d := 1) hN1 hlo ⟨hleft,hright⟩
    have hmasspos := actualPrimeBoxMass_nonneg N
      (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
      (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5)
    have hsmall : (C/(N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10)) *
        actualPrimeBoxMass N
          (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
          (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5) < epsilon := by
      exact (mul_le_mul hcoeff hmove hmasspos (div_nonneg hC hpowpos.le)).trans_lt
        (hT0 N (by omega))
    have hbound := single_face_wall_atom_sum_bound hN1 hd hL hQ
      (hfloor N (by omega) nu hnu m choice hm t ht) j k hk
    have hfinal := mul_le_mul_of_nonneg_left hsmall.le
      (abs_nonneg (thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))))
    dsimp [C] at hfinal
    calc
      _ ≤ |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| *
          ((80*floorBound (outputAt 246 true))/
            ((N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10))) *
          actualPrimeBoxMass N
            (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
            (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5) := hbound
      _ ≤ epsilon * |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| := by
        nlinarith only [hfinal]
      _ = epsilon * thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
        rw [abs_of_nonneg htheta]

end
end ImbalancedChen.P2Historical246WallFaceSum
