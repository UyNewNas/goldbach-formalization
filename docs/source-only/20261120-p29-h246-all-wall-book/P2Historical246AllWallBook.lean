import ImbalancedChen.P2Historical246WallFaceSum
import ImbalancedChen.P2Historical246RepeatedCeilingBook

/-! SOURCE ONLY / UNEVALUATED. Exact disjoint lower-wall partition,
four H246 pair occurrences and same marked-Theta payment. Does not pay
any other W2 exception, count licence or H247 endpoint. -/
namespace ImbalancedChen.P2Historical246AllWallBook
noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2Historical246PairCarrierPartition P2Historical246SuccessorParentWindow
open P2Historical246RepeatedCeilingAtom P2Historical246WallFaceAtoms P2Historical246WallFaceSum
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalHalfOpenProfileCarrier P2OriginalCompactScaledPrimeMass P2OriginalPositiveSameQMassLift
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

def wallCarrier (N : ℕ) (L : ℝ) (j : Fin 36) (k : Fin 4) : Finset Pair :=
  (halfCarrier N L j k).filter (fun p => ¬ interior N L j k p)

def firstWall (N : ℕ) (L : ℝ) (j : Fin 36) (k : Fin 4) : Finset Pair :=
  (wallCarrier N L j k).filter (fun p => normalizedLog N L p 0 = a0 (originalW2At j))

def otherWall (N : ℕ) (L : ℝ) (j : Fin 36) (k : Fin 4) : Finset Pair :=
  (wallCarrier N L j k).filter (fun p => normalizedLog N L p 0 ≠ a0 (originalW2At j))

def secondFace (j : Fin 36) (k : Fin 4) : ℝ :=
  if k = 1 then a2 (originalW2At j) else a1 (originalW2At j)

/-- A wall intersection is included only in firstWall, exactly once. -/
theorem wall_sum_split (N : ℕ) (L : ℝ) (j : Fin 36) (k : Fin 4) (F : Pair → ℝ) :
    (∑ p ∈ wallCarrier N L j k, F p) =
      (∑ p ∈ firstWall N L j k, F p) + (∑ p ∈ otherWall N L j k, F p) := by
  unfold firstWall otherWall
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : normalizedLog N L p 0 = a0 (originalW2At j) <;> simp [h]

/-- The non-first piece is contained in the original second lower face.
For lanes 0 and 2 it is empty; for 1 and 3 it excludes the intersection. -/
theorem otherWall_second_face {N : ℕ} {L : ℝ} {j : Fin 36} {k : Fin 4}
    {p : Pair} (hp : p ∈ otherWall N L j k) :
    p ∈ halfCarrier N L j k ∧ normalizedLog N L p 1 = secondFace j k := by
  obtain ⟨hw,hne⟩ := Finset.mem_filter.mp hp
  obtain ⟨hh,hnot⟩ := Finset.mem_filter.mp hw
  have hlower := noninterior_is_lower_wall hh hnot
  refine ⟨hh,?_⟩
  fin_cases k <;> simp [pairLowerWall,secondFace] at hlower ⊢ <;> tauto

/-- Full finite wall bound: both face sums are bounded independently,
while the signed decomposition retains the intersection once. -/
theorem all_wall_atom_sum_bound {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (hA : 4 ≤ (N : ℝ)^(L/10)) (j : Fin 36) (k : Fin 4) :
    |∑ p ∈ wallCarrier N L j k, oldPairAtom N Q L (parentProduct old) j k p| ≤
      |thetaAtom N Q (parentProduct old)| *
        ((160*floorBound (outputAt 246 true))/((N : ℝ)^(L/10))) *
          actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  have hfirst := face_atom_sum_bound hN hd hL hQ hA j k 0 (a0 (originalW2At j))
    (firstWall N L j k) (by
      intro p hp
      obtain ⟨hw,hface⟩ := Finset.mem_filter.mp hp
      exact ⟨(Finset.mem_filter.mp hw).1,hface⟩)
  have hother := face_atom_sum_bound hN hd hL hQ hA j k 1 (secondFace j k)
    (otherWall N L j k) (by intro p hp; exact otherWall_second_face hp)
  rw [wall_sum_split N L j k (oldPairAtom N Q L (parentProduct old) j k)]
  calc
    |(∑ p ∈ firstWall N L j k, oldPairAtom N Q L (parentProduct old) j k p) +
      (∑ p ∈ otherWall N L j k, oldPairAtom N Q L (parentProduct old) j k p)| ≤
      |∑ p ∈ firstWall N L j k, oldPairAtom N Q L (parentProduct old) j k p| +
      |∑ p ∈ otherWall N L j k, oldPairAtom N Q L (parentProduct old) j k p| := abs_add _ _
    _ ≤ (|thetaAtom N Q (parentProduct old)| *
        ((80*floorBound (outputAt 246 true))/((N : ℝ)^(L/10))) *
          actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5)) +
        (|thetaAtom N Q (parentProduct old)| *
        ((80*floorBound (outputAt 246 true))/((N : ℝ)^(L/10))) *
          actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5)) := add_le_add hfirst hother
    _ = _ := by ring

/-- One threshold before N and the source book, for all four lanes. -/
theorem successor_all_wall_uniform {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu, ∀ (j : Fin 36) (k : Fin 4),
      let Q := (N : ℝ)^nu
      let old := oldWord t
      let L := residualExponent N (parentProduct old) nu
      |∑ p ∈ wallCarrier N L j k,
        oldPairAtom N Q L (parentProduct old) j k p| ≤
        epsilon * thetaAtom N Q (parentProduct old) := by
  let lo := floorAt eta (horizon+1)
  let C : ℝ := 160*floorBound (outputAt 246 true)
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
  · intro N hN nu hnu m choice hm t ht j k
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
    have hbound := all_wall_atom_sum_bound hN1 hd hL hQ
      (hfloor N (by omega) nu hnu m choice hm t ht) j k
    have hfinal := mul_le_mul_of_nonneg_left hsmall.le
      (abs_nonneg (thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))))
    dsimp [C] at hfinal
    calc
      _ ≤ |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| *
          ((160*floorBound (outputAt 246 true))/
            ((N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10))) *
          actualPrimeBoxMass N
            (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
            (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5) := hbound
      _ ≤ epsilon * |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| := by
        nlinarith only [hfinal]
      _ = epsilon * thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
        rw [abs_of_nonneg htheta]



/-- Original signed wall for a single actual successor tuple and lane. -/
def laneWall (N : ℕ) (nu : ℝ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) (j : Fin 36) (k : Fin 4) : ℝ :=
  let old := oldWord t
  let Q := (N : ℝ)^nu
  let L := residualExponent N (parentProduct old) nu
  ∑ p ∈ wallCarrier N L j k, oldPairAtom N Q L (parentProduct old) j k p

/-- Every actual external path, tuple and lane remains separate; the
original W2 /5 is used once after summing its four positive pair terms. -/
def wallBook {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, laneWall N nu (marks a) (choices a) t j k)/5)

/-- On the actual tagged H246 row, all four lower-wall occurrences
have a uniform common marked-Theta bound. -/
theorem tagged_book_all_wall_payment {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark)
        (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
        b.2.pairRows.length = 4 ∧ (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        let next := fun a => advance (marks a) (choices a)
        |wallBook A marks choices N nu j| ≤
          epsilon * Theta N ((N : ℝ)^nu)
            (sourceSupport A next N nu) (sourceSigma A next N nu) := by
  have heps' : 0 < (5*epsilon/4 : ℝ) := by positivity
  obtain ⟨T,hT,huniform⟩ := successor_all_wall_uniform he heps' horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu I A marks choices hm b hb
  have hN1 : 1 < N := by omega
  let next := fun a => advance (marks a) (choices a)
  obtain ⟨j,hparam,hlen,hlanes⟩ := actual_pair_lists 246 hb
  refine ⟨j,hparam,hlen,hlanes,?_⟩
  have hpoint (a : I) (ha : a ∈ A) (t : Fin (next a).rank → Fin (N+1))
      (ht : t ∈ (next a).source N nu) :
      |(∑ k : Fin 4, laneWall N nu (marks a) (choices a) t j k)/5| ≤
        epsilon * thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
    have hk (k : Fin 4) :
        |laneWall N nu (marks a) (choices a) t j k| ≤
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
      exact huniform N hN nu hnu (marks a) (choices a) (hm a ha) t ht
        j k
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2
    calc
      |∑ k : Fin 4, laneWall N nu (marks a) (choices a) t j k| ≤
          ∑ k : Fin 4, |laneWall N nu (marks a) (choices a) t j k| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 4,
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
            exact Finset.sum_le_sum (fun k _ => hk k)
      _ = (epsilon*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)))*5 := by
            simp [Fin.sum_univ_succ] <;> ring
  calc
    |wallBook A marks choices N nu j| ≤
        ∑ a ∈ A, ∑ t ∈ (next a).source N nu,
          (next a).weight * (epsilon * thetaAtom N ((N : ℝ)^nu)
            (parentProduct (oldWord t))) := by
      unfold wallBook
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro t ht
      have hw : 0 ≤ (next a).weight := by
        exact mul_nonneg (advance_boxRows (marks a) (choices a) (hm a ha)).2.2.2.2
          (next a).history.scalar_nonneg
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hpoint a ha t ht) hw
    _ = epsilon * Theta N ((N : ℝ)^nu)
        (sourceSupport A next N nu) (sourceSigma A next N nu) := by
      rw [source_Theta_exact, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [oldWord_product]
      ring


end
end ImbalancedChen.P2Historical246AllWallBook
