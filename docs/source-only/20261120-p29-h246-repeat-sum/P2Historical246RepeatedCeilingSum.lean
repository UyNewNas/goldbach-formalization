import ImbalancedChen.P2Historical246RepeatedCeilingAtom
import ImbalancedChen.P2OriginalCompactScaledPrimeMass
import ImbalancedChen.P2OriginalPositiveSameQMassLift

/-!
SOURCE ONLY / UNEVALUATED. Sum the exact large=c prefix-collision lane
for ONE actual H246 parent and ONE pair occurrence. This is not the full
marked-family budget, all prefix collisions, or an H247 endpoint licence.
-/
namespace ImbalancedChen.P2Historical246RepeatedCeilingSum

noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization
open P2Historical246PairCarrierPartition P2Historical246SuccessorParentWindow
open P2Historical246SuccessorPrimeCeiling P2Historical246RepeatedCeilingAtom
open P2OriginalChildPhysicalNormalization P2OriginalBankChildPrimeMass
open P2OriginalHalfOpenProfileCarrier P2OriginalCompactScaledPrimeMass
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

def equalityCollision (N : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) (c : ℕ) : Finset Pair :=
  (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
    parentWindow N Q old chi ∧ ¬ bothCoprime N old p ∧ p 1 = c)

def smallProjection (p : Pair) : Fin 1 → ℕ := fun _ => p 0

/-- For fixed large=c the small-prime projection is injective on the
actual equality slice, including the original physical filters. -/
theorem equalityCollision_projection_injective {N c : ℕ} {Q L chi : ℝ} {old : List ℕ}
    {j : Fin 36} {k : Fin 4} {p q : Pair}
    (hp : p ∈ equalityCollision N Q L chi old j k c)
    (hq : q ∈ equalityCollision N Q L chi old j k c)
    (h : smallProjection p = smallProjection q) : p = q := by
  obtain ⟨_,_,_,_,hp1⟩ := Finset.mem_filter.mp hp
  obtain ⟨_,_,_,_,hq1⟩ := Finset.mem_filter.mp hq
  funext i
  fin_cases i
  · simpa [smallProjection] using congrFun h 0
  · exact hp1.trans hq1.symm

/-- Exact N-deleted small-prime box mass dominates the reciprocal sum;
the projection does not quotient two distinct pair occurrences. -/
theorem equalityCollision_reciprocal_le_mass (N c : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) :
    (∑ p ∈ equalityCollision N Q L chi old j k c, 1/((p 0 : ℝ)-1)) ≤
      actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  let S := equalityCollision N Q L chi old j k c
  have hsubset : S.image smallProjection ⊆ actualPrimeBoxTuples N
      (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    have hhalf := (Finset.mem_filter.mp hp).1
    have hbox := (Finset.mem_filter.mp hhalf).1
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    fin_cases i
    simpa [smallProjection] using (mem_actualPrimeBoxTuples_iff.mp hbox 0)
  have hsum : (∑ p ∈ S, 1/((p 0 : ℝ)-1)) =
      ∑ q ∈ S.image smallProjection, 1/((q 0 : ℝ)-1) := by
    symm
    exact Finset.sum_image (fun p hp q hq heq => equalityCollision_projection_injective hp hq heq)
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

/-- Sum the preceding packet's actual H246 atom bound over this equality
slice, before the original W2 /5 and without deleting any other class. -/
theorem equalityCollision_atom_sum_bound {N c : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (hA : 4 ≤ (N : ℝ)^(L/10)) (hc : c.Prime) (hdiv : c ∣ parentProduct old)
    (j : Fin 36) (k : Fin 4) :
    |∑ p ∈ equalityCollision N Q L chi old j k c,
      oldPairAtom N Q L (parentProduct old) j k p| ≤
      |thetaAtom N Q (parentProduct old)| *
        ((20*floorBound (outputAt 246 true))/(c : ℝ)) *
          actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) := by
  let S := equalityCollision N Q L chi old j k c
  let C : ℝ := 20*floorBound (outputAt 246 true)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (floorBound_nonneg _)
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc.pos
  have hcoef : 0 ≤ |thetaAtom N Q (parentProduct old)| * (C/(c : ℝ)) :=
    mul_nonneg (abs_nonneg _) (div_nonneg hC hcR.le)
  calc
    |∑ p ∈ S, oldPairAtom N Q L (parentProduct old) j k p| ≤
        ∑ p ∈ S, |oldPairAtom N Q L (parentProduct old) j k p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, (|thetaAtom N Q (parentProduct old)| * (C/(c : ℝ))) *
        (1/((p 0 : ℝ)-1)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hhalf,_,_,_,heq⟩ := Finset.mem_filter.mp hp
      have hrepeat : p 1 ∣ parentProduct old := by simpa only [heq] using hdiv
      have h := repeated_large_atom_bound hN hd hL hQ hA j k hhalf hrepeat
      rw [heq] at h
      calc
        _ ≤ |thetaAtom N Q (parentProduct old)| *
          ((2*(1/((p 0 : ℝ)-1)))/(c : ℝ)) * (10*floorBound (outputAt 246 true)) := h
        _ = _ := by dsimp [C]; ring
    _ = (|thetaAtom N Q (parentProduct old)| * (C/(c : ℝ))) *
        (∑ p ∈ S, 1/((p 0 : ℝ)-1)) := by rw [Finset.mul_sum]
    _ ≤ (|thetaAtom N Q (parentProduct old)| * (C/(c : ℝ))) *
        actualPrimeBoxMass N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5) :=
      mul_le_mul_of_nonneg_left (equalityCollision_reciprocal_le_mass N c Q L chi old j k) hcoef
    _ = _ := by dsimp [C]; ring

/-- On an actual successor tuple the last appended prime's physical
exponent retains the existing common fixed floor. -/
theorem successor_ceiling_floor {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) :
    floorAt eta (horizon+1) ≤
      (advance m choice).history.ceiling (advance m choice).ceiling t := by
  have hf := (advance m choice).source_facts hN he (advance_boxRows m choice hm) ht
  cases choice with
  | inl rule =>
      change floorAt eta (horizon+1) ≤ physicalPrime N (t (Fin.last m.rank)).val
      exact (hf.1 _).2.2
  | inr p =>
      rcases p with ⟨bank,piece⟩
      change floorAt eta (horizon+1) ≤ physicalPrime N (t (Fin.last (m.rank+1))).val
      exact (hf.1 _).2.2

/-- For each actual successor parent, the equality-at-ceiling pair slice
has a uniform small bound relative to that parent's own Theta atom. The
threshold precedes N, the mark, tuple, row and all four lane choices. -/
theorem successor_equal_ceiling_sum_uniform {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (m : Mark) (choice : SuccessorChoice), m.BoxRows nu eta horizon →
      ∀ t ∈ (advance m choice).source N nu, ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ c : ℕ, c.Prime ∧ c ∣ parentProduct (oldWord t) ∧
        (advance m choice).history.ceiling (advance m choice).ceiling t = physicalPrime N c ∧
        ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
          (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
          ∀ k : Fin 4,
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
  · intro N hN nu hnu m choice hm t ht b hb
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
    obtain ⟨c,hc,hdiv,hchi⟩ := successor_ceiling_is_prime hN1 he m choice hm ht
    obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level hN1 he m choice hm ht
    have htheta : 0 ≤ thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) :=
      P2OriginalPositiveSameQMassLift.thetaAtom_nonneg (by omega) hd
        (P2OriginalPositiveSameQMassLift.sameQ_residual_gt_one hN1 hd hL hQ)
    obtain ⟨j,hp,hnrow,hlanes⟩ := actual_pair_lists 246 hb
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
    refine ⟨c,hc,hdiv,hchi,j,hp,hnrow,hlanes,?_⟩
    intro k
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

end
end ImbalancedChen.P2Historical246RepeatedCeilingSum
