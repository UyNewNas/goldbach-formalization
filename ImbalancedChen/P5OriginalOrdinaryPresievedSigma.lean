import ImbalancedChen.P5OriginalOrdinaryCommonBetaModel

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

An explicitly named physical coefficient for the manuscript's ordinary
ROUGH-tree/common-beta construction. The original ordinary tuple, selected
policy, owner box, precision and full four-prime prefix are retained. Both
small beta functions have ONE cutoff and level, independent of the tuple.
The existing all-prime native sigma is not redefined or identified with it.
No native density/count/PP licence is transferred by this construction.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryPresievedSigma

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalSixteenArithmeticProducts
open OriginalOrdinaryCommonBetaModel

/-- Exactly the original ordinary branch, excluding the distinct W row. -/
def tuples (n N : ℕ) (E : ℕ×ℕ→Prop) : Finset Four :=
  (U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E).filter
    (fun t=>(U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t).val<15)

def rowSupport (n N : ℕ) (eta : ℚ) (w : ℝ) (t : Four) : Finset ℕ :=
  actualSmallRoughModuli
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)

def rowCoefficient (n N : ℕ) (eta : ℚ) (w B : ℝ) (t : Four) (r : ℕ) : ℝ :=
  presievedCoefficient N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    w (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) B r

abbrev Mark := Σ _ : Four, ℕ

/-- The full displayed carrier includes zero coefficients. -/
def marks (n N : ℕ) (eta : ℚ) (w : ℝ) (E : ℕ×ℕ→Prop) : Finset Mark :=
  (tuples n N E).sigma (rowSupport n N eta w)

def modulus (m : Mark) : ℕ := fullPrefix m.1*m.2

def physicalSupport (n N : ℕ) (eta : ℚ) (w : ℝ) (E : ℕ×ℕ→Prop) : Finset ℕ :=
  (marks n N eta w E).image modulus

/-- One physical coefficient, common to all later arithmetic tests. -/
def presievedSigma (n N : ℕ) (eta : ℚ) (w B : ℝ) (E : ℕ×ℕ→Prop) (q : ℕ) : ℝ :=
  ∑ m∈(marks n N eta w E).filter (fun m=>modulus m=q),
    rowCoefficient n N eta w B m.1 m.2

/-- The actual residual carrier lies below the original tuple's prime
ceiling, even though its product can exceed the old native strict level. -/
theorem rowSupport_smallPrimeSupportedAt {n N r : ℕ} {eta : ℚ} {w : ℝ} {t : Four}
    (hw : w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hr : r∈rowSupport n N eta w t) :
    SmallPrimeSupportedAt (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) r := by
  obtain ⟨⟨e,d⟩,hed,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨he,hd⟩ := Finset.mem_product.mp hed
  have heS := actualSmallRosserSupport_smallPrimeSupportedAt N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w he
  have hdSF := fixedRoughSupport_squarefree
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) hd
  refine ⟨mul_ne_zero heS.1 hdSF.ne_zero,?_⟩
  rw [Nat.primeFactors_mul heS.1 hdSF.ne_zero]
  intro p hp
  rcases Finset.mem_union.mp hp with hp|hp
  · exact (heS.2 p hp).trans_le hw
  · exact mem_roughPrimeUniverse_upper
      (fixedRoughSupport_primeFactors_mem
        (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) hd hp)

/-- Original top-four uniqueness still applies to this genuinely presieved
carrier; its proof requires prime ceilings rather than a native product cut. -/
theorem modulus_injective_on_marks {n N : ℕ} {eta : ℚ} {w : ℝ}
    (hN : 1<N) (heta : 0<eta) (E : ℕ×ℕ→Prop)
    (hw : ∀t∈tuples n N E,w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    Set.InjOn modulus (marks n N eta w E:Set Mark) := by
  intro m hm k hk hq
  obtain ⟨hmt,hmr⟩ := Finset.mem_sigma.mp hm
  obtain ⟨hkt,hkr⟩ := Finset.mem_sigma.mp hk
  have hmt' := (Finset.mem_filter.mp hmt).1
  have hkt' := (Finset.mem_filter.mp hkt).1
  have hmleg := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta hmt'
  have hkleg := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta hkt'
  have hparts := U1011StaticNativeTopFourExtension.actual_native_tuple_divisor_unique
    (Finset.mem_filter.mp hmt').1 (Finset.mem_filter.mp hkt').1
    (rowSupport_smallPrimeSupportedAt (hw m.1 hmt) hmr)
    (rowSupport_smallPrimeSupportedAt (hw k.1 hkt) hkr)
    hmleg.2.2.1 hkleg.2.2.1 hq
  exact Sigma.ext hparts.1 (heq_of_eq hparts.2)

theorem rowCoefficient_abs_le_one (n N : ℕ) (eta : ℚ) (w B : ℝ) (t : Four) (r : ℕ) :
    |rowCoefficient n N eta w B t r|≤1 :=
  actualSmallRoughRho_abs_le_one _ N _ w _ B r

/-- The new coefficient equals its actual common-beta row on every
displayed mark, including zero rows. There is no old-sigma premise. -/
theorem presievedSigma_eq_row {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop}
    (hw : ∀t∈tuples n N E,w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    {m : Mark} (hm : m∈marks n N eta w E) :
    presievedSigma n N eta w B E (modulus m)=rowCoefficient n N eta w B m.1 m.2 := by
  have hf : (marks n N eta w E).filter (fun k=>modulus k=modulus m)={m} := by
    ext k
    constructor
    · intro hk
      obtain ⟨hk,hq⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_singleton.mpr (modulus_injective_on_marks hN heta E hw hk hm hq)
    · intro hk
      have heq := Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_filter.mpr ⟨hm,rfl⟩
  simp only [presievedSigma,hf,Finset.sum_singleton]

theorem presievedSigma_eq_zero_off_support (n N : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ×ℕ→Prop) {q : ℕ} (hq : q∉physicalSupport n N eta w E) :
    presievedSigma n N eta w B E q=0 := by
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm,hqM⟩ := Finset.mem_filter.mp hm
  exact (hq (Finset.mem_image.mpr ⟨m,hm,hqM⟩)).elim

theorem presievedSigma_abs_le_one {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1<N) (heta : 0<eta) (E : ℕ×ℕ→Prop)
    (hw : ∀t∈tuples n N E,w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (q : ℕ) : |presievedSigma n N eta w B E q|≤1 := by
  by_cases hq : q∈physicalSupport n N eta w E
  · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hq
    rw [presievedSigma_eq_row hN heta hw hm]
    exact rowCoefficient_abs_le_one n N eta w B m.1 m.2
  · rw [presievedSigma_eq_zero_off_support n N eta w B E hq]
    norm_num

/-- Exact signed test identity for this ONE actual presieved coefficient.
Reciprocal totients, divisor tests and original prime AP errors are all
instances of F with the full physical modulus retained. -/
theorem exact_pushforward (n N : ℕ) (eta : ℚ) (w B : ℝ) (E : ℕ×ℕ→Prop) (F : ℕ→ℝ) :
    (∑t∈tuples n N E,∑r∈rowSupport n N eta w t,
      rowCoefficient n N eta w B t r*F(fullPrefix t*r)) =
    ∑q∈physicalSupport n N eta w E,presievedSigma n N eta w B E q*F q := by
  rw [←Finset.sum_sigma]
  change (∑m∈marks n N eta w E,rowCoefficient n N eta w B m.1 m.2*F(modulus m))=_
  have hf := Finset.sum_fiberwise_of_maps_to (s:=marks n N eta w E)
    (t:=physicalSupport n N eta w E) (g:=modulus)
    (fun m hm=>Finset.mem_image_of_mem modulus hm)
    (fun m=>rowCoefficient n N eta w B m.1 m.2*F(modulus m))
  rw [←hf]
  apply Finset.sum_congr rfl
  intro q hq
  unfold presievedSigma
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

end
end ImbalancedChen.P5Z.OriginalOrdinaryPresievedSigma
