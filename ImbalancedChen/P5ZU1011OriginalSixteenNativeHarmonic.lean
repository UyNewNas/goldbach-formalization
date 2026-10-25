import ImbalancedChen.P5ZU1011OriginalSixteenFullHarmonic
import ImbalancedChen.P5ZU1011OriginalSixteenArithmeticProducts
import ImbalancedChen.P5ZU11AdaptiveMinimum

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The harmonic mean is transported to the literal ORIGINAL U11 source,
not a surrogate logarithmic tuple family. Its actual arithmetic labels
p1<p2<p3<p4 are reversed by the existing original16 slots dictionary.
The same target-prime exclusions, weak p1 lower wall, strict p3 upper
wall and complete half-open p4 band [N^h,N^d) are retained exactly.
The last-pair E mask is evaluated on (p3,p4), not on the first two labels.

The complete-prime reciprocal totient is the original squarefree product
of all FOUR labels. Arbitrary masks occur only in an exact finite identity;
the concluding mean is the fixed UNMASKED original source. This is a
harmonic main-term theorem, not a bound for its quotient cardinal weights.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenNativeHarmonic

noncomputable section
open Set Filter Topology MeasureTheory
open Classical
open U11Integral U1011AdaptivePrimeError U1011OriginalSixteenArithmeticProducts
open scoped BigOperators

def unslots (p : Fin 4 → ℕ) : Four := ((p 3,p 2),(p 1,p 0))

theorem unslots_slots (t : Four) : unslots (slots t)=t := by
  rcases t with ⟨⟨p1,p2⟩,⟨p3,p4⟩⟩
  rfl

theorem slots_unslots (p : Fin 4 → ℕ) : slots (unslots p)=p := by
  funext i
  fin_cases i <;> rfl

theorem slots_injective : Function.Injective slots := by
  intro t u h
  have hh := congrArg unslots h
  simpa only [unslots_slots] using hh

/-- Exactly the original six physical support tests, in decreasing slots. -/
def physicalRegion (N : ℕ) (p : Fin 4 → ℕ) : Prop :=
  (N : ℝ)^(417/5000 : ℝ) ≤ (p 3 : ℝ) ∧ p 3<p 2 ∧ p 2<p 1 ∧
    (p 1 : ℝ)<(N : ℝ)^(19/125 : ℝ) ∧
    (N : ℝ)^(19/125 : ℝ)≤(p 0 : ℝ) ∧ (p 0 : ℝ)<(N : ℝ)^(59/250 : ℝ)

theorem unslots_source_iff (N : ℕ) (E : ℕ×ℕ → Prop) (p : Fin 4 → ℕ) :
    unslots p ∈ U11Adaptive.source N E ↔
      (∀ i, p i ∈ chenAdditivePrimeCarrier N) ∧ physicalRegion N p ∧ ¬E (p 1,p 0) := by
  simp only [U11Adaptive.source,chenY11FullPrimeSelector,Finset.mem_filter,
    Finset.mem_product,unslots,physicalRegion,Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
  tauto

/-- The original physical endpoints and strict order have their exact
logarithmic meanings. In particular both half-open fourth-prime endpoints
are preserved in their original directions. -/
theorem log_originalDomain_iff_physicalRegion {N : ℕ} (hN : 1<N)
    (p : Fin 4 → ℕ) (hp : ∀ i, 0<p i) :
    actualPrimeTupleLog N p ∈ originalDomain ∅ ↔ physicalRegion N p := by
  have hNr : (1 : ℝ)<N := by exact_mod_cast hN
  have hlow (a : ℝ) (i : Fin 4) :
      a≤actualPrimeTupleLog N p i ↔ (N : ℝ)^a≤(p i : ℝ) := by
    have h := (Real.rpow_le_rpow_left_iff hNr :
      (N : ℝ)^a≤(N : ℝ)^(actualPrimeTupleLog N p i) ↔ a≤actualPrimeTupleLog N p i)
    simpa only [actualPrimeTupleLog_rpow hN p hp] using h.symm
  have hhigh (a : ℝ) (i : Fin 4) :
      actualPrimeTupleLog N p i<a ↔ (p i : ℝ)<(N : ℝ)^a := by
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
  simp only [originalDomain,Set.mem_setOf_eq,Set.mem_empty_iff_false,
    not_false_eq_true,and_true,hlow,hhigh,horder,physicalRegion]

def boxTuples (N : ℕ) : Finset (Fin 4 → ℕ) :=
  actualPrimeBoxTuples N (fun _ : Fin 4 => (417/5000 : ℝ)) (fun _ => (59/250 : ℝ))

def kept (N : ℕ) (E : ℕ×ℕ → Prop) (p : Fin 4 → ℕ) : Prop :=
  actualPrimeTupleLog N p ∈ originalDomain ∅ ∧ ¬E (p 1,p 0)

/-- Exact source/box bijection dictionary, before selecting a policy or
estimating any kernel. All native carrier bounds are reconstructed. -/
theorem unslots_source_iff_kept_box {N : ℕ} (hN : 1<N)
    (E : ℕ×ℕ → Prop) (p : Fin 4 → ℕ) :
    unslots p ∈ U11Adaptive.source N E ↔ p ∈ (boxTuples N).filter (kept N E) := by
  have hNr : (1 : ℝ)<N := by exact_mod_cast hN
  have hupper : (N : ℝ)^(59/250 : ℝ)<N := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hNr
      (by norm_num : (59/250 : ℝ)<1)
  constructor
  · intro ht
    obtain ⟨hcarrier,hphysical,hE⟩ := (unslots_source_iff N E p).1 ht
    have hp : ∀ i, Nat.Prime (p i) := fun i => (mem_chenAdditivePrimeCarrier.mp (hcarrier i)).2.1
    have hd := (log_originalDomain_iff_physicalRegion hN p (fun i => (hp i).pos)).2 hphysical
    apply Finset.mem_filter.mpr
    refine ⟨?_,hd,hE⟩
    apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).2
    refine ⟨fun i => ⟨hp i,(hp i).coprime_iff_not_dvd.mp
      (mem_chenAdditivePrimeCarrier.mp (hcarrier i)).2.2⟩,?_⟩
    exact U1011OriginalSixteenFullHarmonic.domain_subset_box hd
  · intro hp
    obtain ⟨hpbox,hd,hE⟩ := Finset.mem_filter.mp hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hpbox
    apply (unslots_source_iff N E p).2
    refine ⟨?_,(log_originalDomain_iff_physicalRegion hN p (fun i => (hi i).1.pos)).1 hd,hE⟩
    intro i
    apply mem_chenAdditivePrimeCarrier.mpr
    refine ⟨?_,(hi i).1,(hi i).1.coprime_iff_not_dvd.mpr (hi i).2.1⟩
    exact_mod_cast (hi i).2.2.2.trans hupper

/-- The actual source and target exclusion give the existing original
arithmetic product dictionary; no alternative coefficient is selected. -/
theorem source_mem_joint {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ U11Adaptive.source N E) : t ∈ P5U1011JointOverlap.jointSelector N E := by
  apply P5U1011JointOverlap.originalU11_mem_joint
  · exact_mod_cast (show 1≤N by omega)
  · exact ht

def nativeHarmonicSum (N : ℕ) (E : ℕ×ℕ → Prop) (f : LogFour → ℝ) : ℝ :=
  ∑ t ∈ U11Adaptive.source N E, f (coordinates N t)/(Nat.totient (fullPrefix t) : ℝ)


theorem nativeHarmonicSum_eq_literal_four_product (N : ℕ)
    (E : ℕ×ℕ → Prop) (f : LogFour → ℝ) :
    nativeHarmonicSum N E f = ∑ t ∈ U11Adaptive.source N E,
      f (coordinates N t)/(Nat.totient (t.1.1*t.1.2*t.2.1*t.2.2) : ℝ) := by
  simp only [nativeHarmonicSum,fullPrefix_eq_multiplier,P5U10OriginalMean.multiplier]
/-- The exact finite harmonic source is attached to actual box tuples by
a bijection, with reciprocal totient of the complete original four-prime
product. E keeps its true original last pair on every term. -/
theorem nativeHarmonicSum_eq_masked_box {N : ℕ} (hN : 1<N)
    (E : ℕ×ℕ → Prop) (f : LogFour → ℝ) :
    nativeHarmonicSum N E f = maskedTestSum N
      (fun _ : Fin 4 => (417/5000 : ℝ)) (fun _ => (59/250 : ℝ)) (kept N E) f := by
  let T := (boxTuples N).filter (kept N E)
  calc
    _ = ∑ p ∈ T, (∏ i, 1/((p i : ℝ)-1))*f (actualPrimeTupleLog N p) := by
      unfold nativeHarmonicSum
      refine Finset.sum_bij (fun t _ => slots t) ?_ ?_ ?_ ?_
      · intro t ht
        apply (unslots_source_iff_kept_box hN E (slots t)).1
        simpa only [unslots_slots] using ht
      · intro t _ u _ htu
        exact slots_injective htu
      · intro p hp
        refine ⟨unslots p,(unslots_source_iff_kept_box hN E p).2 hp,slots_unslots p⟩
      · intro t ht
        have hj := source_mem_joint hN ht
        have hpbox : slots t ∈ boxTuples N :=
          (Finset.mem_filter.mp ((unslots_source_iff_kept_box hN E (slots t)).1
            (by simpa only [unslots_slots] using ht))).1
        have htot := actualPrimeBoxTuple_reciprocalTotient hpbox (slots_strictAnti hj).injective
        change f (actualPrimeTupleLog N (slots t))/(Nat.totient (∏ i,slots t i) : ℝ)=_
        calc
          _ = (1/(Nat.totient (∏ i,slots t i) : ℝ))*f (actualPrimeTupleLog N (slots t)) := by ring
          _ = _ := by rw [htot]
    _ = _ := by
      unfold T boxTuples maskedTestSum
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hk : kept N E p <;> simp [hk]

/-- Exact UNMASKED source attachment to the actual original-domain prime
box test used in the independently proved full-sixteen harmonic mean. -/
theorem nativeHarmonicSum_eq_actualPrimeBox {N : ℕ} (hN : 1<N) (f : LogFour → ℝ) :
    nativeHarmonicSum N (fun _ => False) f = actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417/5000 : ℝ)) (fun _ => (59/250 : ℝ))
      ((originalDomain ∅).indicator f) := by
  rw [nativeHarmonicSum_eq_masked_box hN]
  unfold maskedTestSum actualPrimeBoxTestSum
  apply Finset.sum_congr rfl
  intro p _
  by_cases hd : actualPrimeTupleLog N p ∈ originalDomain ∅ <;> simp [kept,hd]

/-- Full original16 nonlinear harmonic mean on the LITERAL native source.
It is not an averaged quotient-count theorem and supplies no AP licence. -/
theorem tendsto_native_original_sixteen_mean :
    Tendsto (fun N : ℕ => nativeHarmonicSum N (fun _ => False)
      U1011OriginalSixteenFullHarmonic.actualMinimum) atTop
      (𝓝 (∫ v in originalDomain ∅, U1011OriginalSixteenFullHarmonic.actualMinimum v*
        U11Canonical.harmonicDensity v)) := by
  have heq : U1011OriginalSixteenFullHarmonic.primeMean =ᶠ[atTop]
      (fun N : ℕ => nativeHarmonicSum N (fun _ => False)
        U1011OriginalSixteenFullHarmonic.actualMinimum) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact (nativeHarmonicSum_eq_actualPrimeBox hN _).symm
  exact U1011OriginalSixteenFullHarmonic.tendsto_actual_original_full_sixteen_mean.congr' heq

end
end ImbalancedChen.P5Z.U1011OriginalSixteenNativeHarmonic

