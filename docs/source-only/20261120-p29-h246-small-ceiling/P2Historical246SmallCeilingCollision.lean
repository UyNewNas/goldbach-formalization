import ImbalancedChen.P2Historical246JointWallCeiling
import ImbalancedChen.P2Historical246WallFaceSum

/-! SOURCE ONLY / UNEVALUATED. Bound the original prefix-collision
subclass where the SMALL pair prime equals the actual parent ceiling.
The earlier large=ceiling slice is excluded. Other collisions, strict
ceiling, count bridge and H247 endpoint remain unpaid. -/
namespace ImbalancedChen.P2Historical246SmallCeilingCollision
noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2Historical246PairCarrierPartition P2Historical246SuccessorParentWindow
open P2Historical246BoundedPairBridge P2OriginalW2CountTupleReindex
open P5OriginalActionMassBound
open P2Historical246RepeatedCeilingAtom P2Historical246RepeatedCeilingBook
open P2Historical246RepeatedCeilingDecomposition P2Historical246WallFaceSum
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalCompactScaledPrimeMass P2OriginalPositiveSameQMassLift
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

def smallCeilingCollision (N : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) (c : ℕ) : Finset Pair :=
  (otherCollision N Q L chi old j k c).filter (fun p => p 0 = c)

/-- The finite actual previous prefix bucket separates into the small=c
slice and its exact complement, without changing the earlier p1≠c gate. -/
theorem otherCollision_small_split (N : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) (c : ℕ) (F : Pair → ℝ) :
    (∑ p ∈ otherCollision N Q L chi old j k c, F p) =
      (∑ p ∈ smallCeilingCollision N Q L chi old j k c, F p) +
      (∑ p ∈ (otherCollision N Q L chi old j k c).filter (fun p => p 0 ≠ c), F p) := by
  unfold smallCeilingCollision
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p 0 = c <;> simp [h]

/-- At the genuine parent ceiling c|d, small=c forces the prefix
collision; original ordered pair geometry also gives large≠c. -/
theorem actual_small_ceiling_forces_collision {N c : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L) (hc : c.Prime)
    (hdiv : c ∣ parentProduct old) (j : Fin 36) (k : Fin 4) {p : Pair}
    (hp : p ∈ halfCarrier N L j k) (hi : interior N L j k p)
    (hparent : parentWindow N Q old chi) (heq : p 0 = c) :
    p ∈ smallCeilingCollision N Q L chi old j k c := by
  have hm := (pair_count_carrier_membership hN hd hL hQ
    (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k p).mp hp
  have hne : p 1 ≠ c := by
    have horder : p 0 < p 1 := hm.2.1
    omega
  have hnot : ¬ bothCoprime N old p := by
    intro hcop
    have hcnd : c ∣ N*parentProduct old := by
      obtain ⟨v,hv⟩ := hdiv
      refine ⟨N*v,?_⟩
      rw [hv]
      ring
    have hcc : c.Coprime (N*parentProduct old) := by simpa only [heq] using hcop.1
    have hc1 : c ∣ 1 := by
      have hg := Nat.dvd_gcd (dvd_refl c) hcnd
      change Nat.gcd c (N*parentProduct old) = 1 at hcc
      simpa only [hcc] using hg
    exact hc.ne_one (Nat.dvd_one.mp hc1)
  apply Finset.mem_filter.mpr
  refine ⟨?_,heq⟩
  exact Finset.mem_filter.mpr ⟨hp,hi,hparent,hnot,hne⟩

/-- Fixed small=c is a true fixed normalized-log face. The whole
actual subset, including repeated-prefix gating, satisfies the existing
finite face estimate. No assumption that c is fresh is made. -/
theorem small_ceiling_atom_sum_bound {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (hA : 4 ≤ (N : ℝ)^(L/10)) (j : Fin 36) (k : Fin 4) (c : ℕ) :
    |∑ p ∈ smallCeilingCollision N Q L chi old j k c,
      oldPairAtom N Q L (parentProduct old) j k p| ≤
      |thetaAtom N Q (parentProduct old)| *
        ((80*floorBound (outputAt 246 true))/((N : ℝ)^(L/10))) *
          actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  apply face_atom_sum_bound hN hd hL hQ hA j k 0
    (L⁻¹*(Real.log (c : ℝ)/Real.log N))
  intro p hp
  obtain ⟨hother,heq⟩ := Finset.mem_filter.mp hp
  refine ⟨(Finset.mem_filter.mp hother).1,?_⟩
  simp [normalizedLog,Pi.smul_apply,smul_eq_mul,actualPrimeTupleLog,heq]

/-- One pre-N threshold, every actual source and every c. -/
theorem successor_small_ceiling_uniform {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu, ∀ (j : Fin 36) (k : Fin 4) (c : ℕ),
      let Q := (N : ℝ)^nu
      let old := oldWord t
      let L := residualExponent N (parentProduct old) nu
      |∑ p ∈ smallCeilingCollision N Q L ((advance m choice).history.ceiling (advance m choice).ceiling t) old j k c,
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
  · intro N hN nu hnu m choice hm t ht j k c
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
    have hbound := small_ceiling_atom_sum_bound hN1 hd hL hQ
      (hfloor N (by omega) nu hnu m choice hm t ht) j k c
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



/-- Actual small=ceiling collision in one marked successor and one lane.
The selected ceilingPrime is proven to be its genuine last prime by
ceilingPrime_spec on the actual source. -/
def smallLane (N : ℕ) (nu : ℝ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) (j : Fin 36) (k : Fin 4) : ℝ :=
  let old := oldWord t
  let Q := (N : ℝ)^nu
  let L := residualExponent N (parentProduct old) nu
  let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
  ∑ p ∈ smallCeilingCollision N Q L chi old j k (ceilingPrime N m choice t),
    oldPairAtom N Q L (parentProduct old) j k p

def smallBook {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, smallLane N nu (marks a) (choices a) t j k)/5)

/-- The exact archived row and all four ordered occurrences: a single
pre-N threshold yields epsilon times the same marked-source Theta. -/
theorem tagged_book_small_ceiling_payment {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark)
        (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
        b.2.pairRows.length = 4 ∧ (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        let next := fun a => advance (marks a) (choices a)
        |smallBook A marks choices N nu j| ≤
          epsilon * Theta N ((N : ℝ)^nu)
            (sourceSupport A next N nu) (sourceSigma A next N nu) := by
  have heps' : 0 < (5*epsilon/4 : ℝ) := by positivity
  obtain ⟨T,hT,huniform⟩ := successor_small_ceiling_uniform he heps' horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu I A marks choices hm b hb
  have hN1 : 1 < N := by omega
  let next := fun a => advance (marks a) (choices a)
  obtain ⟨j,hparam,hlen,hlanes⟩ := actual_pair_lists 246 hb
  refine ⟨j,hparam,hlen,hlanes,?_⟩
  have hpoint (a : I) (ha : a ∈ A) (t : Fin (next a).rank → Fin (N+1))
      (ht : t ∈ (next a).source N nu) :
      |(∑ k : Fin 4, smallLane N nu (marks a) (choices a) t j k)/5| ≤
        epsilon * thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
    have hk (k : Fin 4) :
        |smallLane N nu (marks a) (choices a) t j k| ≤
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
      exact huniform N hN nu hnu (marks a) (choices a) (hm a ha) t ht
        j k (ceilingPrime N (marks a) (choices a) t)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2
    calc
      |∑ k : Fin 4, smallLane N nu (marks a) (choices a) t j k| ≤
          ∑ k : Fin 4, |smallLane N nu (marks a) (choices a) t j k| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 4,
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
            exact Finset.sum_le_sum (fun k _ => hk k)
      _ = (epsilon*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)))*5 := by
            simp [Fin.sum_univ_succ] <;> ring
  calc
    |smallBook A marks choices N nu j| ≤
        ∑ a ∈ A, ∑ t ∈ (next a).source N nu,
          (next a).weight * (epsilon * thetaAtom N ((N : ℝ)^nu)
            (parentProduct (oldWord t))) := by
      unfold smallBook
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
end ImbalancedChen.P2Historical246SmallCeilingCollision
