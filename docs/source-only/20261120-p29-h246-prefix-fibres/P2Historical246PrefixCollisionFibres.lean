import ImbalancedChen.P2Historical246PrefixSlotLocalization
import ImbalancedChen.P2Historical246WallFaceSum

/-! SOURCE ONLY / UNEVALUATED. Partition the literal prefix-collision
carrier by one chosen actual (coordinate,parent slot) witness. No
colliding pair is duplicated, even if a parent prime repeats. -/
namespace ImbalancedChen.P2Historical246PrefixCollisionFibres
noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2Historical246PairCarrierPartition
open P2Historical246SuccessorParentWindow P2Historical246PrefixSlotLocalization
open P2Historical246WallFaceSum P2OriginalChildPhysicalNormalization
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalCompactScaledPrimeMass
open P2OriginalPositiveSameQMassLift P2Historical246RepeatedCeilingAtom
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def prefixCarrier (N : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) : Finset Pair :=
  (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
    parentWindow N Q old chi ∧ ¬ bothCoprime N old p)

/-- A single parent and original lane, including BOTH previously
separated ceiling-equality slices. Reusing those payments in addition to
this full-carrier bound would double-charge them. -/
theorem successor_prefix_fibre_sum_bound {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu)
    (hA : 4 ≤ (N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10))
    (j : Fin 36) (k : Fin 4) :
    let Q := (N : ℝ)^nu
    let old := oldWord t
    let L := residualExponent N (parentProduct old) nu
    let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
    let lo := floorAt eta (horizon+1)
    |∑ p ∈ prefixCarrier N Q L chi old j k,
      oldPairAtom N Q L (parentProduct old) j k p| ≤
      |thetaAtom N Q (parentProduct old)| *
        ((160*floorBound (outputAt 246 true))/(lo*(N : ℝ)^(L/10))) *
          actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  classical
  let Q := (N : ℝ)^nu
  let old := oldWord t
  let L := residualExponent N (parentProduct old) nu
  let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
  let lo := floorAt eta (horizon+1)
  let S := prefixCarrier N Q L chi old j k
  let R := Fin 2 × Fin (advance m choice).rank
  let J : Finset (Option R) := Finset.univ.image some
  let F := oldPairAtom N Q L (parentProduct old) j k
  have hlo : 0 < lo := floorAt_pos he (horizon+1)
  obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level hN he m choice hm ht
  have hwitness (p : Pair) (hp : p ∈ S) : ∃ w : R, p w.1 = (t w.2).val := by
    have hS := Finset.mem_filter.mp hp
    obtain ⟨i,a,ha⟩ := collision_has_parent_slot hN he m choice hm ht j k hS.1 hS.2.2.2
    exact ⟨⟨i,a⟩,ha⟩
  let pick : Pair → Option R := fun p =>
    if hp : p ∈ S then some (Classical.choose (hwitness p hp)) else none
  have hpick (p : Pair) (hp : p ∈ S) :
      ∃ w : R, pick p = some w ∧ p w.1 = (t w.2).val := by
    refine ⟨Classical.choose (hwitness p hp),?_,Classical.choose_spec (hwitness p hp)⟩
    simp [pick,hp]
  have hmaps : ∀ p ∈ S, pick p ∈ J := by
    intro p hp
    obtain ⟨w,hw,_⟩ := hpick p hp
    rw [hw]
    exact Finset.mem_image.mpr ⟨w,Finset.mem_univ w,rfl⟩
  have hsum := Finset.sum_fiberwise_of_maps_to (s := S) (t := J) (g := pick) hmaps F
  have hfibre (w : Option R) (hw : w ∈ J) :
      |∑ p ∈ S.filter (fun p => pick p = w), F p| ≤
      |thetaAtom N Q (parentProduct old)| *
        ((80*floorBound (outputAt 246 true))/((N : ℝ)^(L/10))) *
          actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
    obtain ⟨⟨i,a⟩,_,rfl⟩ := Finset.mem_image.mp hw
    apply face_atom_sum_bound hN hd hL hQ hA j k i
      (L⁻¹*(Real.log ((t a).val : ℝ)/Real.log N))
    intro p hp
    obtain ⟨hpS,hpk⟩ := Finset.mem_filter.mp hp
    have hpHalf := (Finset.mem_filter.mp hpS).1
    obtain ⟨v,hpv,hv⟩ := hpick p hpS
    have heq : v = (i,a) := Option.some.inj (hpv.symm.trans hpk)
    subst v
    refine ⟨hpHalf,?_⟩
    simp [normalizedLog,Pi.smul_apply,smul_eq_mul,actualPrimeTupleLog,hv]
  have hsumabs : |∑ p ∈ S, F p| ≤
      ∑ w ∈ J, |∑ p ∈ S.filter (fun p => pick p = w), F p| := by
    rw [← hsum]
    exact Finset.abs_sum_le_sum_abs _ _
  have hB : 0 ≤ floorBound (outputAt 246 true) := floorBound_nonneg _
  have hLpow : (0 : ℝ) < (N : ℝ)^(L/10) := by positivity
  have hmass : 0 ≤ actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) :=
    actualPrimeBoxMass_nonneg _ _ _
  let C : ℝ := |thetaAtom N Q (parentProduct old)| *
    ((80*floorBound (outputAt 246 true))/((N : ℝ)^(L/10))) *
      actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (abs_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hB) hLpow.le)) hmass
  have hrank : ((advance m choice).rank : ℝ) ≤ 1/lo :=
    (le_div_iff₀ hlo).2 (successor_rank_floor_bound hN he hnu m choice hm ht)
  calc
    _ ≤ ∑ w ∈ J, |∑ p ∈ S.filter (fun p => pick p = w), F p| := hsumabs
    _ ≤ ∑ _w ∈ J, C := Finset.sum_le_sum (fun w hw => hfibre w hw)
    _ = (2*((advance m choice).rank : ℝ))*C := by
      dsimp [J]
      rw [Finset.sum_image (fun a _ b _ h => Option.some.inj h)]
      simp [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul] <;> ring
    _ ≤ (2*(1/lo))*C := by nlinarith [mul_nonneg (sub_nonneg.mpr hrank) hC]
    _ = _ := by
      dsimp [C,lo,Q,old,L]
      simp only [div_eq_mul_inv, mul_inv_rev]
      <;> ring


/-- Uniform full prefix bucket, no ceiling slice added a second time. -/
theorem successor_full_prefix_uniform {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu, ∀ (j : Fin 36) (k : Fin 4),
      let Q := (N : ℝ)^nu
      let old := oldWord t
      let L := residualExponent N (parentProduct old) nu
      let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
      |∑ p ∈ prefixCarrier N Q L chi old j k,
        oldPairAtom N Q L (parentProduct old) j k p| ≤
        epsilon * thetaAtom N Q (parentProduct old) := by
  let lo := floorAt eta (horizon+1)
  let C : ℝ := (160*floorBound (outputAt 246 true))/lo
  have hlo : 0 < lo := floorAt_pos he (horizon+1)
  have hC : 0 ≤ C := by dsimp [C]; exact div_nonneg (mul_nonneg (by norm_num) (floorBound_nonneg _)) hlo.le
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
    have hbound := successor_prefix_fibre_sum_bound hN1 he hnu m choice hm ht
      (hfloor N (by omega) nu hnu m choice hm t ht) j k
    have hfinal := mul_le_mul_of_nonneg_left hsmall.le
      (abs_nonneg (thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))))
    dsimp [C] at hfinal
    calc
      _ ≤ |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| *
          ((160*floorBound (outputAt 246 true))/
            (lo*((N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10)))) *
          actualPrimeBoxMass N
            (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
            (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5) := hbound
      _ = |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| *
          (((160*floorBound (outputAt 246 true)/lo)/
            ((N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu/10))) *
          actualPrimeBoxMass N
            (fun _ : Fin 1 => residualExponent N (parentProduct (oldWord t)) nu/10)
            (fun _ => 3*residualExponent N (parentProduct (oldWord t)) nu/5)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            <;> ring
      _ ≤ epsilon * |thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t))| := by
        linarith only [hfinal]
      _ = epsilon * thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
        rw [abs_of_nonneg htheta]


/-- The entire original prefix-collision bucket for one actual parent. -/
def prefixLane (N : ℕ) (nu : ℝ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) (j : Fin 36) (k : Fin 4) : ℝ :=
  let old := oldWord t
  let Q := (N : ℝ)^nu
  let L := residualExponent N (parentProduct old) nu
  let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
  ∑ p ∈ prefixCarrier N Q L chi old j k, oldPairAtom N Q L (parentProduct old) j k p

def prefixBook {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, prefixLane N nu (marks a) (choices a) t j k)/5)

/-- Full original prefix bucket for one actual tagged H246 row; this
single estimate supersedes rather than adds the earlier equality slices. -/
theorem tagged_book_full_prefix_payment {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark)
        (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
        b.2.pairRows.length = 4 ∧ (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        let next := fun a => advance (marks a) (choices a)
        |prefixBook A marks choices N nu j| ≤
          epsilon * Theta N ((N : ℝ)^nu)
            (sourceSupport A next N nu) (sourceSigma A next N nu) := by
  have heps' : 0 < (5*epsilon/4 : ℝ) := by positivity
  obtain ⟨T,hT,huniform⟩ := successor_full_prefix_uniform he heps' horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu I A marks choices hm b hb
  have hN1 : 1 < N := by omega
  let next := fun a => advance (marks a) (choices a)
  obtain ⟨j,hparam,hlen,hlanes⟩ := actual_pair_lists 246 hb
  refine ⟨j,hparam,hlen,hlanes,?_⟩
  have hpoint (a : I) (ha : a ∈ A) (t : Fin (next a).rank → Fin (N+1))
      (ht : t ∈ (next a).source N nu) :
      |(∑ k : Fin 4, prefixLane N nu (marks a) (choices a) t j k)/5| ≤
        epsilon * thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
    have hk (k : Fin 4) :
        |prefixLane N nu (marks a) (choices a) t j k| ≤
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
      exact huniform N hN nu hnu (marks a) (choices a) (hm a ha) t ht
        j k
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2
    calc
      |∑ k : Fin 4, prefixLane N nu (marks a) (choices a) t j k| ≤
          ∑ k : Fin 4, |prefixLane N nu (marks a) (choices a) t j k| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 4,
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
            exact Finset.sum_le_sum (fun k _ => hk k)
      _ = (epsilon*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)))*5 := by
            simp [Fin.sum_univ_succ] <;> ring
  calc
    |prefixBook A marks choices N nu j| ≤
        ∑ a ∈ A, ∑ t ∈ (next a).source N nu,
          (next a).weight * (epsilon * thetaAtom N ((N : ℝ)^nu)
            (parentProduct (oldWord t))) := by
      unfold prefixBook
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
end ImbalancedChen.P2Historical246PrefixCollisionFibres
