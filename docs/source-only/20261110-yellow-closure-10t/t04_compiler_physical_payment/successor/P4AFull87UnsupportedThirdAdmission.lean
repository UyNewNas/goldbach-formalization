import ImbalancedChen.P4AFull87TaggedAtomValue

/-! The actual enlarged policy at a third ancestor missed by the historical
table. This is a computation of its actual boolean decision on ordinary
words, including every higher splice and the exact rank-eight trim. -/
namespace ImbalancedChen.P4AFull87UnsupportedThirdAdmission
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor VariableEnvelope
open P5OriginalCommonRefinedPreservation (lambda3_le_exponent5)
open P4AOriginalFull87DataPolicy
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_some_spec)
open P4AOriginalFull87SourceDispatch (point8)

def missed (d : OriginalData) (N : ℝ) (h : List ℕ) : Prop :=
  ¬P1ThirdFallbackSupport.supported d.e d.chi d.m d.omega N (rosserAncestor 3 h)

theorem missed_ancestor {d : OriginalData} {N : ℝ} {pre : List ℕ}
    (h : missed d N pre) (j : ℕ) (hj : 3≤j) : missed d N (rosserAncestor j pre) := by
  simpa only [missed,rosserAncestor_nested 3 j hj] using h

theorem missed_of_small {d : OriginalData} {N : ℝ} {pre : List ℕ}
    (hp : (primeHistoryTuple 3 (rosserAncestor 3 pre) 2:ℝ)<N^d.omega) :
    missed d N pre := fun h => (not_le_of_gt hp) h.1.2

theorem seed_of_missed {d : OriginalData} {N : ℝ} {pre : List ℕ} (h : missed d N pre) :
    originalSeed d N pre=HistoricalThirdCoarse.initial d.e := by
  simp only [originalSeed,P1OriginalVariableFourthContinuation.seedExponent,
    P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_neg h]

theorem lambda3_of_missed {d : OriginalData} {N : ℝ} {pre : List ℕ} (h : missed d N pre)
    (he : (d.e:ℝ)<11/64000) :
    lambda3 d N pre=HistoricalThirdCoarse.initial d.e ∧
      VariableEnvelope.cap < lambda3 d N pre := by
  have hi : VariableEnvelope.cap < HistoricalThirdCoarse.initial d.e := by
    unfold VariableEnvelope.cap HistoricalThirdCoarse.initial extendedDistributionCap
    linarith
  have hfb : fallbackSeed d N pre ≤ HistoricalThirdCoarse.initial d.e := by
    unfold fallbackSeed
    split_ifs <;> first | exact (VariableEnvelope.v_le_cap _).trans hi.le | exact (seed_of_missed h).le
  have hq : lambda3 d N pre=HistoricalThirdCoarse.initial d.e := by
    rw [lambda3,seed_of_missed h,max_eq_left hfb]
  exact ⟨hq,by simpa only [hq] using hi⟩

theorem no_selection {delta : ℝ} (hd : 0<delta) (n : ℕ) (N : ℝ) (pre : List ℕ)
    (hsmall : point8 N pre 2 ≤ 1/100) : selectedCap delta n N pre=none := by
  cases ha : selectedCap delta n N pre with
  | none => rfl
  | some a =>
    obtain ⟨c,_,ht,_⟩ := selectedCap_some_spec delta n N pre a ha
    have hs := P4AOriginalFull87StrictActionTrim.trim_subset_source c hd ht
    exact ((not_lt_of_ge hsmall) (P4AOriginalFull87SourceDictionary.source_basic hs).2.1).elim

private theorem old_pass {d : OriginalData} {N : ℝ} {pre : List ℕ} (h : missed d N pre)
    (ho : ordinaryRosserPrefixAdmissible false (N^HistoricalThirdCoarse.initial d.e) pre)
    (h1 : pre.length=1 → HistoricalThirdCoarse.firstStop d.e d.m N pre) :
    common3 d N false pre=true := by
  have hold : old3 d N false pre=true := by
    by_cases h2 : pre.length≤2
    · simp [old3,HistoricalThirdCoarse.policy_through_two _ _ _ _ _ _ _ h2,
        HistoricalThirdCoarse.initialPolicy,oddFirstExitPolicy,ho,h1]
    · simp [old3,HistoricalThirdCoarse.policy,thirdCappedUpperPolicy,firstExitDepthSplicePolicy,
        h2,frozenParityRosserPolicy,ancestorFrozenPolicy,
        P1ThirdFallbackSupport.rawLevel_fallback _ _ _ _ _ _ h,
        ordinaryParityRosserPolicy,oddFirstExitPolicy,ho]
  simp [common3,hold]

/-- Every level and the final selector is checked on its own predecessor.
The true/false branches are the ones in the published D-data constructor. -/
theorem passes {d : OriginalData} {N : ℝ} (hN : 1≤N) {pre : List ℕ}
    {delta : ℝ} (hd : 0<delta) (n : ℕ) (h : missed d N pre)
    (h8 : point8 N pre 2≤1/100)
    (ho : ordinaryRosserPrefixAdmissible false (N^HistoricalThirdCoarse.initial d.e) pre)
    (h1 : pre.length=1 → HistoricalThirdCoarse.firstStop d.e d.m N pre) :
    policy delta n d N false pre=true := by
  have hf (p : List ℕ) (hm : missed d N p) :
      HistoricalThirdCoarse.initial d.e ≤ exponent5 d N p :=
    calc
      _ = originalSeed d N p := (seed_of_missed hm).symm
      _ ≤ lambda3 d N p := le_max_left _ _
      _ ≤ _ := lambda3_le_exponent5 d N p
  have ha (p : List ℕ) (hm : missed d N p) : ¬active d N p := fun hh => hm hh.2
  have five : fifthPolicy n d N false pre=true := by
    by_cases h4 : pre.length≤4
    · simpa [fifthPolicy,firstExitDepthSplicePolicy,h4] using old_pass h ho h1
    · have h5 := missed_ancestor h 5 (by decide)
      have hg := ordinaryRosserPrefixAdmissible_mono false pre
        (Real.rpow_le_rpow_of_exponent_le hN (hf _ h5)) ho
      simp [fifthPolicy,firstExitDepthSplicePolicy,h4,frozenParityRosserPolicy,ancestorFrozenPolicy,
        level5Exponent,ha _ h5,ordinaryParityRosserPolicy,oddFirstExitPolicy,hg]
  have six : sixthPolicy n d N false pre=true := by
    by_cases h6 : pre.length≤6
    · simpa [sixthPolicy,firstExitDepthSplicePolicy,h6] using five
    · let s := rosserAncestor 6 pre
      have hm := missed_ancestor h 6 (by decide)
      have hcf : HistoricalThirdCoarse.initial d.e ≤ currentSixthExponent d N s :=
        (hf _ (missed_ancestor hm 5 (by decide))).trans (fifth_le_current d N s)
      have hg := ordinaryRosserPrefixAdmissible_mono false pre
        (Real.rpow_le_rpow_of_exponent_le hN hcf) ho
      simpa [sixthPolicy,firstExitDepthSplicePolicy,h6,frozenParityRosserPolicy,ancestorFrozenPolicy,
        level6Exponent,ha _ hm,ordinaryParityRosserPolicy,oddFirstExitPolicy,s] using hg
  by_cases hlen : pre.length≤8
  · simpa [policy,firstExitDepthSplicePolicy,hlen] using six
  · simpa [policy,firstExitDepthSplicePolicy,hlen,eighthContinuation,no_selection hd n N pre h8] using six

private theorem valid (keep : List ℕ → Bool) (xs : List ℕ) (pre : List ℕ)
    (pos : Bool) (h : ∀ i < xs.length, keep ((xs.take (i+1)).reverse ++ pre)=true) :
    FirstExitValidSelection (oddFirstExitPolicy keep) pre pos xs := by
  induction xs generalizing pre pos with
  | nil => trivial
  | cons p tail ih =>
    have h0 := h 0 (by simp)
    simp only [List.take_succ_cons,List.take_zero,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.singleton_append] at h0
    refine ⟨by simp [oddFirstExitPolicy,h0],ih (p::pre) (!pos) ?_⟩
    intro i hi
    simpa only [List.take_succ_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append] using h (i+1) (by simpa using hi)

/-- Actual full physical fibre at the even raw word. Positivity of the
outer branch follows from its own word; the small part is 1 by the
existing disjoint prime factorization. Neither fact concerns density. -/
theorem even_word_rho {d : OriginalData} {N cap : ℕ} (hN : 1≤N)
    {delta w z tau L : ℝ} (hd : 0<delta) (hL : 1<L) (n : ℕ)
    (xs : List ℕ) (hxs : xs.Sublist (roughPrimeUniverse N cap w z)) (he : Even xs.length)
    (hprefix : ∀ i < xs.length,
      let pre := (xs.take (i+1)).reverse
      missed d N pre ∧ point8 N pre 2≤1/100 ∧
        ordinaryRosserPrefixAdmissible false ((N:ℝ)^HistoricalThirdCoarse.initial d.e) pre ∧
        (pre.length=1 → HistoricalThirdCoarse.firstStop d.e d.m N pre)) :
    let keep := P4AFull87UnionCompilerPayment.keep delta n d N
    let tag := P4AFull87DataCompilerReads.tag delta hd n d N
    xs.prod ∈ P4AUpperTaggedBetaAttachment.support N cap w z ∧
    P4AUpperTaggedBetaAttachment.rho keep tag N cap w z tau L xs.prod=1 := by
  let keep := P4AFull87UnionCompilerPayment.keep delta n d N
  let tag := P4AFull87DataCompilerReads.tag delta hd n d N
  let U := P4AUpperTaggedParityCompiler.universe N cap w z
  let S := actualSmallRosserSupport N cap w
  have hvalid := valid keep xs [] true (fun i hi => by
    obtain ⟨hm,h8,ho,h1⟩ := hprefix i hi
    simpa only [List.append_nil] using passes (by exact_mod_cast hN) hd n hm h8 ho h1)
  have hraw : xs.prod ∈ P4AUpperTaggedParityCompiler.rawSupport keep N cap w z := by
    change xs.prod ∈ firstExitRetainedModuli (oddFirstExitPolicy keep) (roughPrimeUniverse N cap w z)
    exact (mem_firstExitRetainedModuli_iff_validSelection _ _ _).mpr ⟨xs,hxs,hvalid,rfl⟩
  have hu := P4AUpperTaggedParityCompiler.rawSupport_subset_universe keep N cap w z hraw
  have hpr (p : ℕ) (hp : p∈xs) : p.Prime :=
    mem_roughPrimeUniverse_prime (hxs.subset hp)
  have hmu : (ArithmeticFunction.moebius xs.prod:ℝ)=1 := by
    rw [actualPrimeVector_moebius_eq_sign xs hpr ((roughPrimeUniverse_nodup N cap w z).sublist hxs),
      he.neg_one_pow,Int.cast_one]
  have hc : P4AUpperTaggedParityCompiler.coefficient keep tag N cap w z tau xs.prod = 1 := by
    have hx := P4AUpperTaggedParityCompiler.outer_of_raw keep tag N cap w z tau hraw
    simp [P4AUpperTaggedParityCompiler.coefficient,hu,hmu,hx]
  have hs : 1∈S := Nat.mem_divisors.mpr ⟨one_dvd _,actualSmallPrimeProduct_ne_zero N cap w⟩
  have hb : actualSmallRosserPlus N cap w L 1=1 :=
    MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_one
      (actualSmallPrimeProduct_ne_zero N cap w) hL
  constructor
  · change xs.prod ∈ (smallRoughPairs S U).image _
    exact Finset.mem_image.mpr ⟨(1,xs.prod),by simp [smallRoughPairs,hs,hu,U],one_mul _⟩
  · have hval := smallRoughRho_mul (w:=w) (small:=S) (rough:=U)
      (actualSmallRosserSupport_smallPrimeSupportedAt N cap w)
      (P2LowerFiniteCellRounding.universe_rough N cap w z)
      (P4AUpperTaggedParityCompiler.coefficient keep tag N cap w z tau)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) hs hu
    simpa only [P4AUpperTaggedBetaAttachment.rho,one_mul,smallRoughPairCoefficient,
      signAttachedCoefficient,hc,zero_le_one,if_true,hb] using hval

end
end ImbalancedChen.P4AFull87UnsupportedThirdAdmission
