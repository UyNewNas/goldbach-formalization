import ImbalancedChen.P2Historical246RepeatedCeilingSum

/-! SOURCE ONLY / UNEVALUATED. Summation for the actual finite successor
book, preserving labels and four ordered pair occurrences. Not an H247
endpoint, full collision licence or count-to-profile bridge. -/
namespace ImbalancedChen.P2Historical246RepeatedCeilingBook
noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2Historical246PairCarrierPartition P2Historical246SuccessorParentWindow
open P2Historical246SuccessorPrimeCeiling P2Historical246RepeatedCeilingAtom
open P2Historical246RepeatedCeilingSum
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalHalfOpenProfileCarrier P2OriginalCompactScaledPrimeMass
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

theorem successor_equal_ceiling_all_rows_uniform {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu, ∀ c : ℕ, c.Prime →
      c ∣ parentProduct (oldWord t) →
      (advance m choice).history.ceiling (advance m choice).ceiling t = physicalPrime N c →
      ∀ (j : Fin 36) (k : Fin 4),
            let Q := (N : ℝ)^nu
            let old := oldWord t
            let L := residualExponent N (parentProduct old) nu
            let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
            |∑ p ∈ equalityCollision N Q L chi old j k c,
              oldPairAtom N Q L (parentProduct old) j k p| ≤
                epsilon * thetaAtom N Q (parentProduct old) := by
  let lo := floorAt eta (horizon+1)
  let C : ℝ := 20*floorBound (outputAt 246 true)
  have hlo : 0 < lo := floorAt_pos he (horizon+1)
  have hC : 0 ≤ C := by dsimp [C]; exact mul_nonneg (by norm_num) (floorBound_nonneg _)
  have hpow := tendsto_nat_log_pow_div_rpow 0 hlo
  simp only [pow_zero] at hpow
  have hmass := tendsto_actualPrimeBoxMass (fun _ : Fin 1 => lo/20) (fun _ => max 1 lo)
    (fun _ => by positivity) (fun _ => by have h := le_max_right (1 : ℝ) lo; linarith)
  have hlimit : Tendsto (fun N : ℕ => (C/(N : ℝ)^lo) *
      actualPrimeBoxMass N (fun _ : Fin 1 => lo/20) (fun _ => max 1 lo)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,mul_one_div] using (hpow.const_mul C).mul hmass
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp (hlimit.eventually (gt_mem_nhds heps))
  obtain ⟨T1,hT1,hface⟩ := successor_pair_floor_uniform he horizon
  refine ⟨max T1 (max 4 T0),?_,?_⟩
  · exact (le_max_left 4 T0).trans (le_max_right T1 _)
  · intro N hN nu hnu m choice hm t ht c hc hdiv hchi j k
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
      P2OriginalPositiveSameQMassLift.thetaAtom_nonneg (by omega) hd
        (P2OriginalPositiveSameQMassLift.sameQ_residual_gt_one hN1 hd hL hQ)
    have hceiling : lo ≤ physicalPrime N c := by
      rw [← hchi]
      exact successor_ceiling_floor hN1 he m choice hm ht
    have hc_floor : (N : ℝ)^lo ≤ c := physical_floor_to_power hN1 hc.pos hceiling
    have hpowpos : (0 : ℝ) < (N : ℝ)^lo := by positivity
    have hcoeff : C/(c : ℝ) ≤ C/(N : ℝ)^lo :=
      div_le_div_of_nonneg_left hC hpowpos hc_floor
    have hmove := moving_box_mass_le_ambient (d := 1) hN1 hlo ⟨hleft,hright⟩
    have hmovepos := actualPrimeBoxMass_nonneg N
      (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
      (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5)
    have hsmall : (C/(c : ℝ)) * actualPrimeBoxMass N
        (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
        (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5) < epsilon := by
      exact (mul_le_mul hcoeff hmove hmovepos (div_nonneg hC hpowpos.le)).trans_lt
        (hT0 N (by omega))
    have hA := hface N (by omega) nu hnu m choice hm t ht
    have hbound := equalityCollision_atom_sum_bound hN1 hd hL hQ hA hc hdiv j k
      (chi := (advance m choice).history.ceiling (advance m choice).ceiling t)
    have hfinal := mul_le_mul_of_nonneg_left hsmall.le
      (abs_nonneg (thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))))
    dsimp [C] at hsmall
    dsimp [C] at hfinal
    calc
      _ ≤ |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| *
          ((20*floorBound (outputAt 246 true))/(c : ℝ)) *
            actualPrimeBoxMass N
              (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
              (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5) := hbound
      _ = |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| *
          (((20*floorBound (outputAt 246 true))/(c : ℝ)) *
            actualPrimeBoxMass N
              (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
              (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5)) := by ring
      _ ≤ epsilon * |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| := by
        linarith only [hfinal]
      _ = epsilon * thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
        rw [abs_of_nonneg htheta]


/-- Select a prime only from the concrete ceiling identity. The default
zero is used off the actual successor source; it is never used as a
prime in the theorem below. -/
def ceilingPrime (N : ℕ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) : ℕ :=
  if h : ∃ c : ℕ, c.Prime ∧ c ∣ parentProduct (oldWord t) ∧
      (advance m choice).history.ceiling (advance m choice).ceiling t = physicalPrime N c
  then Classical.choose h else 0

theorem ceilingPrime_spec {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) :
    (ceilingPrime N m choice t).Prime ∧
      ceilingPrime N m choice t ∣ parentProduct (oldWord t) ∧
      (advance m choice).history.ceiling (advance m choice).ceiling t =
        physicalPrime N (ceilingPrime N m choice t) := by
  have h := successor_ceiling_is_prime hN he m choice hm ht
  simpa only [ceilingPrime, dif_pos h] using Classical.choose_spec h

/-- The signed H246 collision slice for one actual parent and one
ordered archived pair occurrence, before the original W2 /5. -/
def laneSlice (N : ℕ) (nu : ℝ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) (j : Fin 36) (k : Fin 4) : ℝ :=
  let old := oldWord t
  let Q := (N : ℝ)^nu
  let L := residualExponent N (parentProduct old) nu
  let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
  ∑ p ∈ equalityCollision N Q L chi old j k (ceilingPrime N m choice t),
    oldPairAtom N Q L (parentProduct old) j k p

/-- Keep each external book label, source tuple and ordered W2 lane.
The single factor /5 is the original W2 factor, not a Q80 /4 or a
replacement payment. -/
def bookSlice {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, laneSlice N nu (marks a) (choices a) t j k)/5)

/-- A common threshold for the actual successor book and actual tagged
H246 W2 row. The original positive marked weight and exact product
pushforward provide the SAME Theta normalizer, even for repeated products
or two paths with the same arithmetic tuple. -/
theorem tagged_book_equal_ceiling_payment {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark)
        (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
        b.2.pairRows.length = 4 ∧ (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        let next := fun a => advance (marks a) (choices a)
        |bookSlice A marks choices N nu j| ≤
          epsilon * Theta N ((N : ℝ)^nu)
            (sourceSupport A next N nu) (sourceSigma A next N nu) := by
  have heps' : 0 < (5*epsilon/4 : ℝ) := by positivity
  obtain ⟨T,hT,huniform⟩ := successor_equal_ceiling_all_rows_uniform he heps' horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu I A marks choices hm b hb
  have hN1 : 1 < N := by omega
  let next := fun a => advance (marks a) (choices a)
  obtain ⟨j,hparam,hlen,hlanes⟩ := actual_pair_lists 246 hb
  refine ⟨j,hparam,hlen,hlanes,?_⟩
  have hpoint (a : I) (ha : a ∈ A) (t : Fin (next a).rank → Fin (N+1))
      (ht : t ∈ (next a).source N nu) :
      |(∑ k : Fin 4, laneSlice N nu (marks a) (choices a) t j k)/5| ≤
        epsilon * thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
    obtain ⟨hc,hdiv,hchi⟩ := ceilingPrime_spec hN1 he (marks a) (choices a) (hm a ha) ht
    have hk (k : Fin 4) :
        |laneSlice N nu (marks a) (choices a) t j k| ≤
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
      exact huniform N hN nu hnu (marks a) (choices a) (hm a ha) t ht
        (ceilingPrime N (marks a) (choices a) t) hc hdiv hchi j k
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2
    calc
      |∑ k : Fin 4, laneSlice N nu (marks a) (choices a) t j k| ≤
          ∑ k : Fin 4, |laneSlice N nu (marks a) (choices a) t j k| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 4,
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
            exact Finset.sum_le_sum (fun k _ => hk k)
      _ = (epsilon*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)))*5 := by
            simp [Fin.sum_univ_succ] <;> ring
  calc
    |bookSlice A marks choices N nu j| ≤
        ∑ a ∈ A, ∑ t ∈ (next a).source N nu,
          (next a).weight * (epsilon * thetaAtom N ((N : ℝ)^nu)
            (parentProduct (oldWord t))) := by
      unfold bookSlice
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
end ImbalancedChen.P2Historical246RepeatedCeilingBook
