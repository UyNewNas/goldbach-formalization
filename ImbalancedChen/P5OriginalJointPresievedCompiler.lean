import ImbalancedChen.P5OriginalOrdinaryPresievedQuotientUpper

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The distinct W row is included in this explicit ALL16 common-beta physical
compiler. The original ordinary/fallback source partition, tuple ownership,
selected profile and full prefix are unchanged. This new jointPresievedSigma
is built from the actual rough/common-beta rows; it is not a redefinition
of the existing all-prime native sigma. Analytic licences are not inherited.
-/

namespace ImbalancedChen.P5Z.OriginalJointPresievedCompiler

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open OriginalOrdinaryPresievedSigma
open OriginalOrdinaryPresievedQuotientUpper (quotient_upper)
open OriginalOrdinaryCommonBetaModel
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

def jointMarks (n N:ℕ) (eta:ℚ) (w:ℝ) (E:ℕ×ℕ→Prop) : Finset Mark :=
  (U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E).sigma (rowSupport n N eta w)

def jointSupport (n N:ℕ) (eta:ℚ) (w:ℝ) (E:ℕ×ℕ→Prop) : Finset ℕ :=
  (jointMarks n N eta w E).image modulus

def jointPresievedSigma (n N:ℕ) (eta:ℚ) (w B:ℝ) (E:ℕ×ℕ→Prop) (q:ℕ) : ℝ :=
  ∑m∈(jointMarks n N eta w E).filter (fun m=>modulus m=q),rowCoefficient n N eta w B m.1 m.2

theorem joint_modulus_injective {n N:ℕ} {eta:ℚ} {w:ℝ}
    (hN:1<N) (heta:0<eta) (E:ℕ×ℕ→Prop)
    (hw:∀t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    Set.InjOn modulus (jointMarks n N eta w E:Set Mark) := by
  intro m hm k hk hq
  obtain ⟨hmt,hmr⟩ := Finset.mem_sigma.mp hm
  obtain ⟨hkt,hkr⟩ := Finset.mem_sigma.mp hk
  have hmleg := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta hmt
  have hkleg := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta hkt
  have hparts := U1011StaticNativeTopFourExtension.actual_native_tuple_divisor_unique
    (Finset.mem_filter.mp hmt).1 (Finset.mem_filter.mp hkt).1
    (rowSupport_smallPrimeSupportedAt (hw m.1 hmt) hmr)
    (rowSupport_smallPrimeSupportedAt (hw k.1 hkt) hkr)
    hmleg.2.2.1 hkleg.2.2.1 hq
  exact Sigma.ext hparts.1 (heq_of_eq hparts.2)

theorem jointSigma_eq_row {n N:ℕ} {eta:ℚ} {w B:ℝ}
    (hN:1<N) (heta:0<eta) {E:ℕ×ℕ→Prop}
    (hw:∀t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    {m:Mark} (hm:m∈jointMarks n N eta w E) :
    jointPresievedSigma n N eta w B E (modulus m)=rowCoefficient n N eta w B m.1 m.2 := by
  have hf : (jointMarks n N eta w E).filter (fun k=>modulus k=modulus m)={m} := by
    ext k
    constructor
    · intro hk
      obtain ⟨hk,hq⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_singleton.mpr (joint_modulus_injective hN heta E hw hk hm hq)
    · intro hk
      have heq := Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_filter.mpr ⟨hm,rfl⟩
  simp only [jointPresievedSigma,hf,Finset.sum_singleton]

theorem jointSigma_zero_off_support (n N:ℕ) (eta:ℚ) (w B:ℝ) (E:ℕ×ℕ→Prop)
    {q:ℕ} (hq:q∉jointSupport n N eta w E) : jointPresievedSigma n N eta w B E q=0 := by
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm,hqm⟩ := Finset.mem_filter.mp hm
  exact (hq (Finset.mem_image.mpr ⟨m,hm,hqm⟩)).elim

theorem jointSigma_abs_le_one {n N:ℕ} {eta:ℚ} {w B:ℝ}
    (hN:1<N) (heta:0<eta) (E:ℕ×ℕ→Prop)
    (hw:∀t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) (q:ℕ) :
    |jointPresievedSigma n N eta w B E q|≤1 := by
  by_cases hq:q∈jointSupport n N eta w E
  · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hq
    rw [jointSigma_eq_row hN heta hw hm]
    exact rowCoefficient_abs_le_one n N eta w B m.1 m.2
  · rw [jointSigma_zero_off_support n N eta w B E hq]
    norm_num

theorem joint_exact_pushforward (n N:ℕ) (eta:ℚ) (w B:ℝ) (E:ℕ×ℕ→Prop) (F:ℕ→ℝ) :
    (∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      ∑r∈rowSupport n N eta w t,rowCoefficient n N eta w B t r*F(fullPrefix t*r)) =
    ∑q∈jointSupport n N eta w E,jointPresievedSigma n N eta w B E q*F q := by
  rw [←Finset.sum_sigma]
  change (∑m∈jointMarks n N eta w E,rowCoefficient n N eta w B m.1 m.2*F(modulus m))=_
  have hf := Finset.sum_fiberwise_of_maps_to (s:=jointMarks n N eta w E)
    (t:=jointSupport n N eta w E) (g:=modulus)
    (fun m hm=>Finset.mem_image_of_mem modulus hm)
    (fun m=>rowCoefficient n N eta w B m.1 m.2*F(modulus m))
  rw [←hf]
  apply Finset.sum_congr rfl
  intro q hq
  unfold jointPresievedSigma
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

theorem joint_row_upper {n N:ℕ} {eta:ℚ} {w B:ℝ} {E:ℕ×ℕ→Prop}
    (hN:1<N) (heta:0<eta) (hB:1<B) (hwB:w≤B) {t:Four}
    (ht:t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hw:w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    U11Adaptive.weight N t≤∑r∈rowSupport n N eta w t,rowCoefficient n N eta w B t r *
      (chenPrimeAPCount N N (fullPrefix t*r)-chenCentrePrimeAPCount N N (fullPrefix t*r)) := by
  have hs := (Finset.mem_filter.mp ht).1
  have hleg := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
  have hz2 : U1011OriginalSixteenJointNearCapCompiler.Z n N eta t≤(t.1.2:ℝ) :=
    hleg.2.2.1.trans (by exact_mod_cast (joint_carrier_order hs).2.2.2.2.1.le)
  have hweight : U11Adaptive.weight N t=
      ((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2:ℝ)).card:ℝ) := by
    rw [fullPrefix_eq_multiplier]
    rfl
  have hcount : U11Adaptive.weight N t≤
      ((chenSiftedQuotientPrimeSource N (fullPrefix t)
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)).card:ℝ) := by
    rw [hweight]
    exact_mod_cast Finset.card_le_card (U11LoweredRosser.siftedSource_subset_lowered N _ _ _ hz2)
  exact hcount.trans (quotient_upper
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N (fullPrefix t)
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) B hB hwB hw (Nat.le_ceil _))

def jointDensity (n N:ℕ) (eta:ℚ) (w B:ℝ) (E:ℕ×ℕ→Prop) : ℝ :=
  physicalDensitySum (jointSupport n N eta w E) (jointPresievedSigma n N eta w B E)

def jointAP (n N:ℕ) (eta:ℚ) (w B:ℝ) (E:ℕ×ℕ→Prop) : ℝ :=
  ∑q∈jointSupport n N eta w E,jointPresievedSigma n N eta w B E q *
    chenQuotientPrimeAPError N (trueLogarithmicIntegral N) q

def jointCentre (n N:ℕ) (eta:ℚ) (w B:ℝ) (E:ℕ×ℕ→Prop) : ℝ :=
  ∑q∈jointSupport n N eta w E,jointPresievedSigma n N eta w B E q*chenCentrePrimeAPCount N N q

/-- The FULL original U10+U11 source uses one genuine ALL16 presieved
coefficient; the original switched fallback remains exactly explicit. -/
theorem original_joint_source_upper {n N:ℕ} {eta:ℚ} {w B:ℝ}
    (hN:1<N) (heta:0<eta) (hB:1<B) (hwB:w≤B) (E:ℕ×ℕ→Prop)
    (hw:∀t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    currentChenUpsilon10 N+currentChenUpsilon11 N E≤
      (∑t∈U1011OriginalSixteenJointNearCapCompiler.fallbackTuples n N E,U11Adaptive.weight N t) +
      trueLogarithmicIntegral N*jointDensity n N eta w B E +
        jointAP n N eta w B E-jointCentre n N eta w B E := by
  rw [U1011OriginalFifteenJointNativeRows.joint_count_identity hN E,
    U1011OriginalSixteenJointNativeCompiler.source_partition n N E]
  have hrows := Finset.sum_le_sum (fun t ht=>joint_row_upper hN heta hB hwB ht (hw t ht))
  have hmain : (∑t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      ∑r∈rowSupport n N eta w t,rowCoefficient n N eta w B t r *
        (chenPrimeAPCount N N (fullPrefix t*r)-chenCentrePrimeAPCount N N (fullPrefix t*r))) =
      trueLogarithmicIntegral N*jointDensity n N eta w B E+
        jointAP n N eta w B E-jointCentre n N eta w B E := by
    rw [joint_exact_pushforward n N eta w B E]
    unfold jointDensity jointAP jointCentre physicalDensitySum
    rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    unfold chenQuotientPrimeAPError
    ring
  have h := add_le_add_left (hrows.trans_eq hmain)
    (∑t∈U1011OriginalSixteenJointNearCapCompiler.fallbackTuples n N E,U11Adaptive.weight N t)
  simpa only [add_sub_assoc,add_assoc] using h

end
end ImbalancedChen.P5Z.OriginalJointPresievedCompiler
