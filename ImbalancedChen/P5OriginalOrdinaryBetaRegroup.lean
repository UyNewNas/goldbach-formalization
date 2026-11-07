import ImbalancedChen.P5ZU1011OriginalFifteenNearCapNative
import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapModulusConvolution
import ImbalancedChen.SmallRoughAttachment

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Exact presieve disintegration of the ORIGINAL ordinary native Rosser row.
The old row is on every allowed prime below Z. Its small/rough split has
the conditional coefficient lambda(e*d), not beta(e)*lambda(d). We retain
the conditional small-factor dependence rather than assuming it vanishes.
All signed tests, including the full-prefix physical divisor test and the
reciprocal-totient/AP tests, use the same finite coefficient.
This file asserts no density, distribution, or zero-defect licence.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryBetaRegroup

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts

def roughProduct (N cap : ℕ) (w Z : ℝ) : ℕ :=
  (roughPrimeFinset N cap w Z).prod id

def roughSupport (N cap : ℕ) (w Z : ℝ) : Finset ℕ :=
  (roughProduct N cap w Z).divisors

theorem prime_partition (N cap : ℕ) {w Z : ℝ} (hwZ : w ≤ Z) :
    actualSmallPrimeFinset N cap Z =
      actualSmallPrimeFinset N cap w ∪ roughPrimeFinset N cap w Z := by
  ext p
  simp only [mem_actualSmallPrimeFinset, Finset.mem_union, mem_roughPrimeFinset]
  constructor
  · rintro ⟨hp,hprime,hcop,hZ⟩
    by_cases hw : (p : ℝ) < w
    · exact Or.inl ⟨hp,hprime,hcop,hw⟩
    · exact Or.inr ⟨hp,hprime,hcop,le_of_not_gt hw,hZ⟩
  · rintro (⟨hp,hprime,hcop,hw⟩ | ⟨hp,hprime,hcop,_,hZ⟩)
    · exact ⟨hp,hprime,hcop,hw.trans_le hwZ⟩
    · exact ⟨hp,hprime,hcop,hZ⟩

theorem prime_partition_disjoint (N cap : ℕ) (w Z : ℝ) :
    Disjoint (actualSmallPrimeFinset N cap w) (roughPrimeFinset N cap w Z) := by
  apply Finset.disjoint_left.mpr
  intro p hs hr
  exact (not_lt_of_ge (mem_roughPrimeFinset.mp hr).2.2.2.1)
    (mem_actualSmallPrimeFinset.mp hs).2.2.2

theorem product_partition (N cap : ℕ) {w Z : ℝ} (hwZ : w ≤ Z) :
    actualSmallPrimeProduct N cap Z =
      actualSmallPrimeProduct N cap w * roughProduct N cap w Z := by
  unfold actualSmallPrimeProduct roughProduct
  rw [prime_partition N cap hwZ, Finset.prod_union (prime_partition_disjoint N cap w Z)]

theorem roughProduct_squarefree (N cap : ℕ) (w Z : ℝ) :
    Squarefree (roughProduct N cap w Z) := by
  apply MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.primeProduct_squarefree
  intro p hp
  exact (mem_roughPrimeFinset.mp hp).2.1

theorem roughSupport_rough {N cap d : ℕ} {w Z : ℝ}
    (hd : d ∈ roughSupport N cap w Z) : RoughPrimeSupportedAt w d := by
  have hM := roughProduct_squarefree N cap w Z
  have hdM : d ∣ roughProduct N cap w Z := (Nat.mem_divisors.mp hd).1
  have hd0 := (Squarefree.squarefree_of_dvd hdM hM).ne_zero
  refine ⟨hd0,?_⟩
  intro p hp
  have hpM := Nat.primeFactors_mono hdM hM.ne_zero hp
  have hprime : ∀ p ∈ roughPrimeFinset N cap w Z, Nat.Prime p :=
    fun p hp => (mem_roughPrimeFinset.mp hp).2.1
  have heq : (roughProduct N cap w Z).primeFactors = roughPrimeFinset N cap w Z := by
    simpa only [roughProduct,id_eq] using Nat.primeFactors_prod hprime
  rw [heq] at hpM
  exact (mem_roughPrimeFinset.mp hpM).2.2.2.1

/-- Exact divisor carrier, including the empty rough range and divisor 1.
The presieve wall belongs to the rough range. -/
theorem nativeSupport_eq_products (N cap : ℕ) {w Z : ℝ} (hwZ : w ≤ Z) :
    actualSmallRosserSupport N cap Z =
      smallRoughModuli (actualSmallRosserSupport N cap w) (roughSupport N cap w Z) := by
  have hs0 := actualSmallPrimeProduct_ne_zero N cap w
  have hr0 := (roughProduct_squarefree N cap w Z).ne_zero
  have hp := product_partition N cap hwZ
  ext d
  constructor
  · intro hd
    have hdM := (Nat.mem_divisors.mp hd).1
    rw [hp] at hdM
    obtain ⟨e,r,he,hr,her⟩ := Nat.dvd_mul.mp hdM
    exact Finset.mem_image.mpr ⟨(e,r),Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨he,hs0⟩,Nat.mem_divisors.mpr ⟨hr,hr0⟩⟩,her⟩
  · intro hd
    obtain ⟨⟨e,r⟩,her,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨he,hr⟩ := Finset.mem_product.mp her
    apply Nat.mem_divisors.mpr
    refine ⟨?_,actualSmallPrimeProduct_ne_zero N cap Z⟩
    rw [hp]
    exact mul_dvd_mul (Nat.mem_divisors.mp he).1 (Nat.mem_divisors.mp hr).1

/-- Full signed disintegration. The native coefficient is evaluated at
the full product e*d, with every Rosser prefix test unchanged. -/
theorem native_sum_split (N cap : ℕ) {w Z : ℝ} (hwZ : w ≤ Z)
    (L : ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ actualSmallRosserSupport N cap Z,
      actualSmallRosserPlus N cap Z L q * F q) =
    ∑ e ∈ actualSmallRosserSupport N cap w, ∑ d ∈ roughSupport N cap w Z,
      actualSmallRosserPlus N cap Z L (e*d) * F (e*d) := by
  rw [nativeSupport_eq_products N cap hwZ]
  rw [sum_smallRoughModuli
    (fun d hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun d hd => roughSupport_rough hd)]
  exact Finset.sum_product _ _ _

/-- The multiplication carrier uses the full original four-prime prefix;
no quotient scale or selected subproduct is substituted. -/
theorem ordinary_native_full_test (p : Policy) (hp : p.val < 15) (B : Box)
    (eta : ℚ) (N : ℕ) (t : Four) {w : ℝ}
    (hwZ : w ≤ U1011OriginalFifteenNearCapNative.Z p B eta N)
    (F : ℕ → ℝ) :
    (∑ q ∈ U1011OriginalFifteenNearCapNative.support p B eta N,
      U1011OriginalFifteenNearCapNative.coefficient p B eta N q * F (fullPrefix t*q)) =
    ∑ e ∈ actualSmallRosserSupport N
        (Nat.ceil (U1011OriginalFifteenNearCapNative.Z p B eta N)) w,
      ∑ d ∈ roughSupport N (Nat.ceil (U1011OriginalFifteenNearCapNative.Z p B eta N))
          w (U1011OriginalFifteenNearCapNative.Z p B eta N),
        U1011OriginalFifteenNearCapNative.coefficient p B eta N (e*d) *
          F (fullPrefix t*(e*d)) := by
  exact native_sum_split N _ hwZ _ (fun q => F (fullPrefix t*q))

/-- Both divisor gates, including n=0, are exact for the cutoff-separated
residual factors. No positivity of a beta polynomial is used. -/
theorem ordinary_residual_divisor_gate {N cap e d n : ℕ} {w Z : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ roughSupport N cap w Z) : e*d ∣ n ↔ e ∣ n ∧ d ∣ n :=
  smallRough_mul_dvd_iff
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he) (roughSupport_rough hd)

/-- This is uniqueness for the actual separated divisor carriers, not
an injectivity assumption about a subsequently defined physical weight. -/
theorem native_split_unique {N cap e d e' d' : ℕ} {w Z : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ roughSupport N cap w Z)
    (he' : e' ∈ actualSmallRosserSupport N cap w)
    (hd' : d' ∈ roughSupport N cap w Z)
    (hprod : e*d=e'*d') : e=e' ∧ d=d' := by
  have hpair := smallRough_factorization_unique
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he) (roughSupport_rough hd)
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he') (roughSupport_rough hd') hprod
  exact ⟨congrArg Prod.fst hpair,congrArg Prod.snd hpair⟩

/-- Extend the already-defined sigma/native binding to zero native rows
on the actual ordinary support. This is needed before splitting a full
divisor carrier: the split must not retain only active factors. -/
theorem ordinary_sigma_on_native_support {n N r : ℕ} {eta : ℚ}
    (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hp : (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t).val<15)
    (hr : r∈U1011OriginalSixteenJointNearCapCompiler.support n N eta t) :
    U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E
      (fullPrefix t*r) = U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t r := by
  by_cases hnz : U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t r≠0
  · have hm : (⟨t,r⟩ : U1011OriginalSixteenJointNearCapModulusConvolution.Mark)∈
        U1011OriginalSixteenJointNearCapModulusConvolution.marks n N eta E :=
      Finset.mem_sigma.mpr ⟨ht,Finset.mem_filter.mpr ⟨hr,hnz⟩⟩
    exact U1011OriginalSixteenJointNearCapModulusConvolution.sigma_eq_native_coefficient hN heta hm
  · have hz : U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t r=0 :=
      not_ne_iff.mp hnz
    rw [hz]
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hm,hq⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmt,hmd⟩ := Finset.mem_sigma.mp hm
    obtain ⟨hmd,hmnz⟩ := Finset.mem_filter.mp hmd
    have htleg := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
    have hmleg := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta hmt
    have hparts := U1011StaticNativeTopFourExtension.actual_native_tuple_divisor_unique
      (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp hmt).1
      (actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ hr)
      (actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ hmd)
      htleg.2.2.1 hmleg.2.2.1 hq.symm
    have hzero : U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta m.1 m.2=0 := by
      rw [←hparts.1,←hparts.2]
      exact hz
    exact (hmnz hzero).elim

/-- At an actual ordinary branch mark, the ALREADY DEFINED full
physical sigma is the conditional native value lambda(e*d). Neither beta
independence nor a sigma-equality premise occurs here. Zero coefficients
are included, rather than discarded before identifying the coefficient. -/
theorem ordinary_sigma_eq_conditional {n N e d : ℕ} {eta : ℚ}
    (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hp : (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t).val<15)
    {w : ℝ} (hwZ : w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (he : e∈actualSmallRosserSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w)
    (hd : d∈roughSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) :
    U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E
        (fullPrefix t*(e*d)) =
      U1011OriginalFifteenNearCapNative.coefficient
        (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
        (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta N (e*d) := by
  have hprod : e*d∈U1011OriginalSixteenJointNearCapCompiler.support n N eta t := by
    change e*d∈actualSmallRosserSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    rw [nativeSupport_eq_products N _ hwZ]
    exact Finset.mem_image.mpr ⟨(e,d),Finset.mem_product.mpr ⟨he,hd⟩,rfl⟩
  have hs := ordinary_sigma_on_native_support hN heta ht hp hprod
  have hb := U1011OriginalSixteenJointNearCapCompiler.ordinary_native_binding
    (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t) hp
    (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta N
  exact hs.trans (hb.2.2.2 (e*d))

/-- Exact multiplication-test reassembly against the EXISTING ONE sigma.
The source tuple, its selected policy/box, precision and full prefix all
remain unchanged. This is valid for signed F, without a norm or mean input. -/
theorem ordinary_same_sigma_test {n N : ℕ} {eta : ℚ}
    (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hp : (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t).val<15)
    {w : ℝ} (hwZ : w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (F : ℕ→ℝ) :
    (∑ q∈U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t q * F (fullPrefix t*q)) =
    ∑ e∈actualSmallRosserSupport N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w,
      ∑ d∈roughSupport N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
          w (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t),
        U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E
          (fullPrefix t*(e*d)) * F (fullPrefix t*(e*d)) := by
  have hsplit := native_sum_split N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) hwZ
    (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) (fun q=>F (fullPrefix t*q))
  change (∑ q∈U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t q * F (fullPrefix t*q)) = _ at hsplit
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro d hd
  have hprod : e*d∈U1011OriginalSixteenJointNearCapCompiler.support n N eta t := by
    change e*d∈actualSmallRosserSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    rw [nativeSupport_eq_products N _ hwZ]
    exact Finset.mem_image.mpr ⟨(e,d),Finset.mem_product.mpr ⟨he,hd⟩,rfl⟩
  rw [ordinary_sigma_on_native_support hN heta ht hp hprod]

/-- In particular the reciprocal-totient denominator is that of the FULL
physical modulus. No claim that it is a product of separate totients is
needed for this exact identity. -/
theorem ordinary_same_sigma_totient {n N : ℕ} {eta : ℚ}
    (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hp : (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t).val<15)
    {w : ℝ} (hwZ : w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    (∑ q∈U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t q /
        (Nat.totient (fullPrefix t*q):ℝ)) =
    ∑ e∈actualSmallRosserSupport N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w,
      ∑ d∈roughSupport N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
          w (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t),
        U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E
          (fullPrefix t*(e*d)) / (Nat.totient (fullPrefix t*(e*d)):ℝ) := by
  simpa only [one_div,div_eq_mul_inv] using
    ordinary_same_sigma_test hN heta ht hp hwZ (fun q=>1/(Nat.totient q:ℝ))

/-- Same sigma on the exact physical divisor carrier, including n0=0. -/
theorem ordinary_same_sigma_divisor {n N n0 : ℕ} {eta : ℚ}
    (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hp : (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t).val<15)
    {w : ℝ} (hwZ : w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    (∑ q∈U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      if fullPrefix t*q∣n0 then U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t q else 0) =
    ∑ e∈actualSmallRosserSupport N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w,
      ∑ d∈roughSupport N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
          w (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t),
        if fullPrefix t*(e*d)∣n0 then
          U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E (fullPrefix t*(e*d)) else 0 := by
  simpa only [mul_ite,mul_one,mul_zero] using
    ordinary_same_sigma_test hN heta ht hp hwZ (fun q=>if q∣n0 then (1:ℝ) else 0)

/-- The exact original conditional divisor identity at a native ordinary
row. It keeps the physical full prefix in the divisibility test, and is
valid for every integer argument n, including n=0. -/
theorem ordinary_native_divisor_test (p : Policy) (hp : p.val<15) (B : Box)
    (eta : ℚ) (N n : ℕ) (t : Four) {w : ℝ}
    (hwZ : w≤U1011OriginalFifteenNearCapNative.Z p B eta N) :
    (∑ q∈U1011OriginalFifteenNearCapNative.support p B eta N,
      if fullPrefix t*q∣n then U1011OriginalFifteenNearCapNative.coefficient p B eta N q else 0) =
    ∑ e∈actualSmallRosserSupport N (Nat.ceil (U1011OriginalFifteenNearCapNative.Z p B eta N)) w,
      ∑ d∈roughSupport N (Nat.ceil (U1011OriginalFifteenNearCapNative.Z p B eta N))
          w (U1011OriginalFifteenNearCapNative.Z p B eta N),
        if fullPrefix t*(e*d)∣n then
          U1011OriginalFifteenNearCapNative.coefficient p B eta N (e*d) else 0 := by
  simpa only [mul_ite,mul_one,mul_zero] using
    ordinary_native_full_test p hp B eta N t hwZ (fun q=>if q∣n then (1:ℝ) else 0)

end
end ImbalancedChen.P5Z.OriginalOrdinaryBetaRegroup
