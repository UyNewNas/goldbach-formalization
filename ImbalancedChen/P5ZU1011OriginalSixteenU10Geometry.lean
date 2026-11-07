import ImbalancedChen.P5ZU1011OriginalSixteenNativeHarmonic
import ImbalancedChen.P5ZU1011OriginalSixteenMixedGatePrimeTests

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The ORIGINAL low-fourth U10 band is a<=w<z<y<x<h. It is NOT the U11
support x>=h, and no U11-domain membership is asserted here. Existing
ordinary/H248 state circuits remain unchanged. Their clipped denominators
are licensed directly from U10's smallest-coordinate wall and the actual
full-square eligibility test. The literal Y10 four-prime source is then
attached by an exact tuple bijection with its genuine reciprocal totient.
No harmonic limit, quotient-cardinality bound or distribution licence is
assumed in this bounded geometry/native-source component.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenU10Geometry

noncomputable section
open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open U11Integral U11Canonical U11H248
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenEligibilityState
open U1011OriginalSixteenMixedGatePrimeTests U1011OriginalSixteenStateKernel
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenNativeHarmonic

/-- Exact low fourth-prime band, in DECREASING logarithmic slots. -/
def domain10 : Set LogFour := {v | (417/5000 : ℝ)≤v 3 ∧ v 3<v 2 ∧ v 2<v 1 ∧ v 1<v 0 ∧ v 0<(19/125 : ℝ)}

def supportGates : Fin 5 → MixedGate :=
  ![⟨-ContinuousLinearMap.proj 3,-(417/5000 : ℝ),false⟩,
    ⟨ContinuousLinearMap.proj 3-ContinuousLinearMap.proj 2,0,true⟩,
    ⟨ContinuousLinearMap.proj 2-ContinuousLinearMap.proj 1,0,true⟩,
    ⟨ContinuousLinearMap.proj 1-ContinuousLinearMap.proj 0,0,true⟩,
    ⟨ContinuousLinearMap.proj 0,19/125,true⟩]

theorem domain10_eq_mixed : domain10=mixedRegion supportGates := by
  ext v
  simp [domain10,mixedRegion,supportGates,MixedGate.Holds,Fin.forall_fin_succ,neg_le_neg_iff]

theorem measurableSet_domain10 : MeasurableSet domain10 := by
  rw [domain10_eq_mixed]
  exact measurableSet_mixedRegion _

theorem domain10_smallest_pos {v : LogFour} (hv : v ∈ domain10) : 0<v 3 := by linarith [hv.1]

theorem domain10_subset_compactBox : domain10 ⊆ compactBox := by
  intro v hv
  refine ⟨?_,?_⟩ <;> intro i <;> fin_cases i <;> dsimp <;>
    linarith [hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2]

theorem domain10_subset_box : domain10 ⊆ U1011OriginalSixteenFullHarmonic.box := by
  intro v hv
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i <;> dsimp <;> constructor <;>
    linarith [hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2]

/-- The old TRUE U10 argument lemma is reused on its correct domain;
the U11 lower wall x>=h never enters this bound. -/
theorem domain10_argument_bounds {v : LogFour} (hv : v ∈ domain10) :
    (49/19 : ℝ)≤(1-(v 0+v 1+v 2+v 3))/v 2 ∧
      (1-(v 0+v 1+v 2+v 3))/v 2≤(3332/417 : ℝ) := by
  have h := P5U10OriginalMean.buchstab_argument_bounds hv.1 hv.2.1.le hv.2.2.1.le
    hv.2.2.2.1.le hv.2.2.2.2.le
  convert h using 1 <;> ring

/-- The SAME clipped ordinary kernel is exact on the low-band state:
actual eligibility proves R>w>=a before clipping is removed. -/
theorem frozenOrdinary_eq_actual_D10 (s : U1011OriginalSixteenStateKernel.State)
    (p : Policy) {v : LogFour} (hv : v ∈ domain10) (hs : v ∈ stateCell s)
    (ha : s.active p=true) :
    frozenOrdinary s p v=4*(1-H248 (max 2 (typedResidual p v/v 3)))/typedResidual p v := by
  have he := (hs p).2.1.mp ha
  have hmargin : (417/5000 : ℝ)≤affineResidual s p v := by
    rw [affineResidual_eq_original hs p]
    exact hv.1.trans (typedEligible_residual_gt_smallest p v he).le
  have hH := U1011H248Partition.H248_eq_stateValue ((hs p).2.2 ha)
  rw [frozenOrdinary,max_eq_right hmargin,affineResidual_eq_original hs p,hH]

theorem candidate_eq_on_D10_state (s : U1011OriginalSixteenStateKernel.State)
    {v : LogFour} (hv : v ∈ domain10) (hs : v ∈ stateCell s)
    (c : ℕ) (hc : c ∈ tags bank) : actualCandidate c v=frozenCandidate s c v := by
  rcases Finset.mem_insert.mp hc with rfl | hc
  · simp only [actualCandidate,guarded,frozenCandidate,if_pos rfl]
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hc
    have hj16 : j<16 := Finset.mem_range.mp hj
    let p : Policy := ⟨j,hj16⟩
    have he : eligible j v ↔ s.active p=true := by
      simpa only [eligible,dif_pos hj16] using (hs p).2.1.symm
    by_cases ha : s.active p=true
    · have hordinary := frozenOrdinary_eq_actual_D10 s p hv hs ha
      have heNat := he.mpr ha
      simpa only [actualCandidate,guarded,Nat.succ_ne_zero,if_false,Nat.pred_succ,
        if_pos heNat,frozenCandidate,dif_pos hj16,if_pos ha,ordinaryKernel,residual,p] using hordinary.symm
    · have heNat : ¬eligible j v := fun h => ha (he.mp h)
      simp only [actualCandidate,guarded,Nat.succ_ne_zero,if_false,Nat.pred_succ,
        if_neg heNat,frozenCandidate,dif_pos hj16,if_neg ha,p]

theorem actualMinimum_eq_frozen_D10 (s : U1011OriginalSixteenStateKernel.State)
    {v : LogFour} (hv : v ∈ domain10) (hs : v ∈ stateCell s) : actualMinimum v=frozenMinimum s v := by
  have h := U1011AdaptivePrimeError.envelope_abs_sub_le bank actualCandidate (frozenCandidate s) v 0
    (fun c hc => by rw [candidate_eq_on_D10_state s hv hs c hc]; simp)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

def physical10 (N : ℕ) (p : Fin 4 → ℕ) : Prop :=
  (N : ℝ)^(417/5000 : ℝ)≤(p 3 : ℝ) ∧ p 3<p 2 ∧ p 2<p 1 ∧ p 1<p 0 ∧
    (p 0 : ℝ)<(N : ℝ)^(19/125 : ℝ)

theorem unslots_mem_selector_iff (N : ℕ) (p : Fin 4 → ℕ) :
    unslots p ∈ P5U10OriginalMean.selector N ↔
      (∀ i, p i ∈ chenAdditivePrimeCarrier N) ∧ physical10 N p := by
  simp only [P5U10OriginalMean.selector,chenY10PrimeSelector,Finset.mem_filter,Finset.mem_product,
    unslots,physical10,Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
  tauto

theorem log_domain10_iff_physical10 {N : ℕ} (hN : 1<N) (p : Fin 4 → ℕ) (hp : ∀ i, 0<p i) :
    actualPrimeTupleLog N p ∈ domain10 ↔ physical10 N p := by
  have hNr : (1 : ℝ)<N := by exact_mod_cast hN
  have hlow (a : ℝ) (i : Fin 4) : a≤actualPrimeTupleLog N p i ↔ (N : ℝ)^a≤(p i : ℝ) := by
    have h := (Real.rpow_le_rpow_left_iff hNr :
      (N : ℝ)^a≤(N : ℝ)^(actualPrimeTupleLog N p i) ↔ a≤actualPrimeTupleLog N p i)
    simpa only [actualPrimeTupleLog_rpow hN p hp] using h.symm
  have hhigh (a : ℝ) (i : Fin 4) : actualPrimeTupleLog N p i<a ↔ (p i : ℝ)<(N : ℝ)^a := by
    have h := (Real.rpow_lt_rpow_left_iff hNr :
      (N : ℝ)^(actualPrimeTupleLog N p i)<(N : ℝ)^a ↔ actualPrimeTupleLog N p i<a)
    simpa only [actualPrimeTupleLog_rpow hN p hp] using h.symm
  have horder (i j : Fin 4) : actualPrimeTupleLog N p i<actualPrimeTupleLog N p j ↔ p i<p j := by
    have h := (Real.rpow_lt_rpow_left_iff hNr :
      (N : ℝ)^(actualPrimeTupleLog N p i)<(N : ℝ)^(actualPrimeTupleLog N p j) ↔
        actualPrimeTupleLog N p i<actualPrimeTupleLog N p j)
    have hh : actualPrimeTupleLog N p i<actualPrimeTupleLog N p j ↔ (p i : ℝ)<p j := by
      simpa only [actualPrimeTupleLog_rpow hN p hp] using h.symm
    exact hh.trans Nat.cast_lt
  simp only [domain10,Set.mem_setOf_eq,hlow,hhigh,horder,physical10]

def tuples10 (N : ℕ) : Finset (Fin 4 → ℕ) :=
  (boxTuples N).filter (fun p => actualPrimeTupleLog N p ∈ domain10)

theorem unslots_mem_selector_iff_tuples10 {N : ℕ} (hN : 1<N) (p : Fin 4 → ℕ) :
    unslots p ∈ P5U10OriginalMean.selector N ↔ p ∈ tuples10 N := by
  have hNr : (1 : ℝ)<N := by exact_mod_cast hN
  have hupper : (N : ℝ)^(59/250 : ℝ)<N := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hNr (by norm_num : (59/250 : ℝ)<1)
  constructor
  · intro ht
    obtain ⟨hc,hphy⟩ := (unslots_mem_selector_iff N p).1 ht
    have hp : ∀ i, Nat.Prime (p i) := fun i => (mem_chenAdditivePrimeCarrier.mp (hc i)).2.1
    have hd := (log_domain10_iff_physical10 hN p (fun i => (hp i).pos)).2 hphy
    apply Finset.mem_filter.mpr
    refine ⟨?_,hd⟩
    apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).2
    exact ⟨fun i => ⟨hp i,(hp i).coprime_iff_not_dvd.mp (mem_chenAdditivePrimeCarrier.mp (hc i)).2.2⟩,
      domain10_subset_box hd⟩
  · intro hp
    obtain ⟨hb,hd⟩ := Finset.mem_filter.mp hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hb
    apply (unslots_mem_selector_iff N p).2
    refine ⟨?_,(log_domain10_iff_physical10 hN p (fun i => (hi i).1.pos)).1 hd⟩
    intro i
    apply mem_chenAdditivePrimeCarrier.mpr
    refine ⟨?_,(hi i).1,(hi i).1.coprime_iff_not_dvd.mpr (hi i).2.1⟩
    exact_mod_cast (hi i).2.2.2.trans hupper

theorem selector_mem_joint {N : ℕ} (hN : 1<N) {t : Four} (ht : t ∈ P5U10OriginalMean.selector N)
    (E : ℕ×ℕ → Prop) : t ∈ P5U1011JointOverlap.jointSelector N E := by
  rw [P5U1011JointOverlap.jointSelector_eq_original_union]
  · exact Finset.mem_union_left _ ht
  · exact_mod_cast (show 1≤N by omega)

def native10 (N : ℕ) (f : LogFour → ℝ) : ℝ :=
  ∑ t ∈ P5U10OriginalMean.selector N, f (coordinates N t)/(Nat.totient (fullPrefix t) : ℝ)

/-- Exact native low-band harmonic attachment, with all FOUR prime labels
and their actual full-product totient. No U11 band is substituted. -/
theorem native10_eq_actualPrimeBox {N : ℕ} (hN : 1<N) (f : LogFour → ℝ) :
    native10 N f=actualPrimeBoxTestSum N (fun _ : Fin 4 => (417/5000 : ℝ))
      (fun _ => (59/250 : ℝ)) (domain10.indicator f) := by
  calc
    _ = ∑ p ∈ tuples10 N, (∏ i,1/((p i : ℝ)-1))*f (actualPrimeTupleLog N p) := by
      unfold native10
      refine Finset.sum_bij (fun t _ => slots t) ?_ ?_ ?_ ?_
      · intro t ht
        apply (unslots_mem_selector_iff_tuples10 hN (slots t)).1
        simpa only [unslots_slots] using ht
      · intro t _ u _ htu
        exact slots_injective htu
      · intro p hp
        exact ⟨unslots p,(unslots_mem_selector_iff_tuples10 hN p).2 hp,slots_unslots p⟩
      · intro t ht
        have hj := selector_mem_joint hN ht (fun _ => False)
        have hpbox : slots t ∈ boxTuples N :=
          (Finset.mem_filter.mp ((unslots_mem_selector_iff_tuples10 hN (slots t)).1
            (by simpa only [unslots_slots] using ht))).1
        have htot := actualPrimeBoxTuple_reciprocalTotient hpbox (slots_strictAnti hj).injective
        change f (actualPrimeTupleLog N (slots t))/(Nat.totient (∏ i,slots t i) : ℝ)=_
        calc
          _ = (1/(Nat.totient (∏ i,slots t i) : ℝ))*f (actualPrimeTupleLog N (slots t)) := by ring
          _ = _ := by rw [htot]
    _ = _ := by
      unfold tuples10 boxTuples actualPrimeBoxTestSum
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hd : actualPrimeTupleLog N p ∈ domain10 <;> simp [hd]

end
end ImbalancedChen.P5Z.U1011OriginalSixteenU10Geometry
