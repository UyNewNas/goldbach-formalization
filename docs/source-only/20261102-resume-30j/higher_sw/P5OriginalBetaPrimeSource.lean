import ImbalancedChen.P5ComputedSingletonPrimeSWConsumer
import ImbalancedChen.P5ActualSmallBetaMonomialCost
import Mathlib.Data.Nat.ModEq

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original THIRD factor with one rough label and its entire signed
small-prime beta.  This is a convolution, not a prime coefficient.
The source is the existing attachedGamma, with its original rank parity,
strict beta level, common Ico alphabet, and p not dividing N.  Restriction
of the FULL product to (U,2U] pulls back to (U/e,2U/e] exactly.
-/

namespace ImbalancedChen.P5Z.OriginalBetaPrimeSource
noncomputable section
open Classical Finset Set
open scoped BigOperators
open ImbalancedChen ImbalancedChen.Part3
open All16MarkedCommonFineSource All16FineMeshGateScalar
open ActualAll16UnrestrictedResidualConvolution ActualInnerPerLabelGamma
open SameWholeAssignmentPerLabel OriginalSingletonPrimeSource
open ComputedSingletonPrimeSWConsumer
open PrimeMellinProfileVariation20261026b

/-- A constructed primitive residue, obtained by finite CRT and division.
It is not a chosen AP dictionary premise. -/
def pulledResidue (e q b : ℕ) : ℕ :=
  if h : e.Coprime q then (Nat.chineseRemainder h 0 b).val / e else 0

theorem pulledResidue_spec {e q b : ℕ} (he : e.Coprime q) :
    Nat.ModEq q (e * pulledResidue e q b) b := by
  let z := Nat.chineseRemainder he 0 b
  have hd : e ∣ z.val := Nat.modEq_zero_iff_dvd.mp z.property.1
  have hz : e * (z.val / e) = z.val := Nat.mul_div_cancel' hd
  simpa only [pulledResidue,dif_pos he,hz] using z.property.2

theorem pulledResidue_coprime {e q b : ℕ} (he : e.Coprime q)
    (hb : b.Coprime q) : (pulledResidue e q b).Coprime q := by
  have hh : (e * pulledResidue e q b).Coprime q := by
    change Nat.gcd (e * pulledResidue e q b) q = 1
    rw [(pulledResidue_spec he).gcd_eq]
    exact hb
  exact (Nat.coprime_mul_iff_left.mp hh).2

theorem product_congruent_iff {e q b : ℕ} (he : e.Coprime q) (p : ℕ) :
    Nat.ModEq q (e*p) b ↔ Nat.ModEq q p (pulledResidue e q b) := by
  constructor
  · intro hp
    exact Nat.ModEq.cancel_left_of_coprime he.symm
      (hp.trans (pulledResidue_spec he).symm)
  · intro hp
    exact (hp.mul_left e).trans (pulledResidue_spec he)

def exactKernel (q b n : ℕ) : ℂ :=
  (if Nat.ModEq q n b then 1 else 0) -
    (if n.Coprime q then 1 else 0) / (q.totient : ℂ)

theorem error_eq_kernel (S : Finset ℕ) (c : ℕ → ℂ) (q b : ℕ) :
    auxiliarySWError S c 1 q b = ∑ n ∈ S, c n * exactKernel q b n := by
  have hc : (∑ n ∈ S, if Nat.ModEq q n b then c n else 0) =
      ∑ n ∈ S, c n * (if Nat.ModEq q n b then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : Nat.ModEq q n b <;> simp [h]
  have hm : (∑ n ∈ S, if n.Coprime q then c n else 0) =
      ∑ n ∈ S, c n * (if n.Coprime q then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : n.Coprime q <;> simp [h]
  simp only [auxiliarySWError,Nat.coprime_one_right_eq_true,and_true,one_mul]
  rw [hc,hm]
  simp only [exactKernel,mul_sub,mul_div_assoc,Finset.sum_sub_distrib,Finset.sum_div]

/-- Both terms vanish at a nonunit multiplier.  The same totient mean
is retained at a unit multiplier, with the constructed primitive residue. -/
theorem exactKernel_product {q b : ℕ} (hb : b.Coprime q) (e p : ℕ) :
    exactKernel q b (e*p) =
      if e.Coprime q then exactKernel q (pulledResidue e q b) p else 0 := by
  by_cases he : e.Coprime q
  · simp only [if_pos he,exactKernel,product_congruent_iff he,
      Nat.coprime_mul_iff_left,he,true_and]
  · have hm : ¬Nat.ModEq q (e*p) b := by
      intro hm
      have hc : (e*p).Coprime q := by
        change Nat.gcd (e*p) q = 1
        rw [hm.gcd_eq]
        exact hb
      exact he (Nat.coprime_mul_iff_left.mp hc).1
    simp [he,hm,exactKernel,Nat.coprime_mul_iff_left]

def carrier (N cap m : ℕ) (i : Fin (m+1)) (w U : ℝ) : Finset ℕ :=
  (attachedSupport (commonAlphabet N m) [i] N cap w).filter
    (fun n => U < (n : ℝ) ∧ (n : ℝ) ≤ 2*U)

def value (N cap m r : ℕ) (i : Fin (m+1)) (w B : ℝ)
    (Phi : ℝ → ℝ) (t U : ℝ) (n : ℕ) : ℂ :=
  physicalProfile Phi t U n *
    (SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m) [i]
      N cap r w B n : ℂ)

theorem common_singleton_rough {N m : ℕ} (hN : 1 < N)
    (i : Fin (m+1)) {w : ℝ} (hw : w ≤ lower N m i) :
    ∀ p ∈ support (commonAlphabet N m) [i], RoughPrimeSupportedAt w p := by
  intro p hp
  apply support_rough (commonAlphabet N m) [i] w ?_ ?_ hp
  · intro j hj p hp
    exact ((mem_commonAlphabet_iff hN j).mp hp).1
  · intro j hj p hp
    have hj' : j = i := by simpa using hj
    subst j
    exact hw.trans ((mem_commonAlphabet_iff hN i).mp hp).2.2.1

theorem original_beta_prime_value {N cap m r : ℕ} (hN : 1 < N)
    (i : Fin (m+1)) {w B : ℝ} (hw : w ≤ lower N m i)
    {e p : ℕ} (he : e ∈ actualSmallRosserSupport N cap w)
    (hp : p ∈ commonAlphabet N m i) :
    SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m) [i]
      N cap r w B (e*p) = rawBetaWeight N cap r w B e := by
  have hp' : p ∈ support (commonAlphabet N m) [i] := by
    rwa [singleton_support]
  rw [SameWholeAssignmentPerLabel.attachedGamma,
    smallRoughRho_mul
      (fun d hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
      (common_singleton_rough hN i hw) _ _ _ he hp']
  simp only [smallRoughPairCoefficient,signAttachedCoefficient,ite_self,
    gamma_singleton,if_pos hp,one_mul]

/-- The inherited Ico endpoint convention is unchanged.  The displayed
source at scale U/e is the one to which I's ceil-minus-one bridge applies. -/
theorem full_dyadic_iff {e p : ℕ} (he : 0 < e) (U : ℝ) :
    U < ((e*p : ℕ) : ℝ) ∧ ((e*p : ℕ) : ℝ) ≤ 2*U ↔
      U/(e : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ 2*(U/(e : ℝ)) := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  rw [Nat.cast_mul,div_lt_iff₀ heR,
    show 2*(U/(e : ℝ)) = (2*U)/(e : ℝ) by ring,le_div_iff₀ heR]
  simp only [mul_comm (e : ℝ) (p : ℝ)]

theorem physicalProfile_product {e p : ℕ} (he : 0 < e)
    (Phi : ℝ → ℝ) (t U : ℝ) :
    physicalProfile Phi t U ((e*p : ℕ) : ℝ) =
      physicalProfile Phi t (U/(e : ℝ)) p := by
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  unfold physicalProfile
  congr 1
  rw [Nat.cast_mul,div_div_eq_mul_div]
  ring

/-- The full third-factor discrepancy is exactly a signed sum of prime
discrepancies. Neither its prime exclusion nor the beta/unit mean is lost. -/
theorem original_beta_prime_error {N cap m r : ℕ} (hN : 1 < N)
    (i : Fin (m+1)) {w B : ℝ} (hw : w ≤ lower N m i)
    (Phi : ℝ → ℝ) (t U : ℝ) {q b : ℕ} (hb : b.Coprime q) :
    auxiliarySWError (carrier N cap m i w U)
      (value N cap m r i w B Phi t U) 1 q b =
      ∑ e ∈ actualSmallRosserSupport N cap w,
        (rawBetaWeight N cap r w B e : ℂ) *
          if e.Coprime q then
            auxiliarySWError (source N m i (U/(e : ℝ)))
              (coefficient N m [i] Phi t (U/(e : ℝ))) 1 q (pulledResidue e q b)
          else 0 := by
  have hsmall := fun e (he : e ∈ actualSmallRosserSupport N cap w) =>
    actualSmallRosserSupport_smallPrimeSupportedAt N cap w he
  have hrough := common_singleton_rough hN i hw
  rw [error_eq_kernel]
  simp only [carrier,Finset.sum_filter,attachedSupport,smallRoughModuli]
  rw [Finset.sum_image (smallRough_mul_injOn hsmall hrough)]
  simp only [smallRoughPairs,Finset.sum_product,singleton_support]
  apply Finset.sum_congr rfl
  intro e he
  have hepos : 0 < e := Nat.pos_of_ne_zero (hsmall e he).1
  by_cases heq : e.Coprime q
  · rw [if_pos heq,error_eq_kernel]
    simp only [source,Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hvalue := original_beta_prime_value (r := r) (B := B) hN i hw he hp
    have hdy := full_dyadic_iff (p := p) hepos U
    simp only [value,hvalue,physicalProfile_product hepos,
      exactKernel_product hb,if_pos heq,coefficient,gamma_singleton,if_pos hp,
      Complex.ofReal_one,mul_one]
    by_cases hd : U/(e : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ 2*(U/(e : ℝ))
    · rw [if_pos (hdy.mpr hd),if_pos hd]
      ring
    · rw [if_neg (fun h => hd (hdy.mp h)),if_neg hd,mul_zero]
  · simp only [if_neg heq,mul_zero]
    apply Finset.sum_eq_zero
    intro p hp
    rw [exactKernel_product hb,if_neg heq,mul_zero]
    split_ifs <;> rfl

/-- This exact finite pushforward attaches the new class to arbitrary
physical tests, so marked prefixes and all count/mean tests remain external. -/
theorem original_beta_prime_test {N cap m r : ℕ} (hN : 1 < N)
    (i : Fin (m+1)) {w B : ℝ} (hw : w ≤ lower N m i) (F : ℕ → ℝ) :
    (∑ q3 ∈ attachedSupport (commonAlphabet N m) [i] N cap w,
      SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m) [i]
        N cap r w B q3 * F q3) =
      ∑ e ∈ actualSmallRosserSupport N cap w, ∑ p ∈ commonAlphabet N m i,
        rawBetaWeight N cap r w B e * F (e*p) := by
  rw [attached_fullq_sum]
  · rw [singleton_support]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro p hp
    simp only [gamma_singleton,if_pos hp,one_mul]
  · intro j hj p hp
    exact ((mem_commonAlphabet_iff hN j).mp hp).1
  · intro j hj p hp
    have hj' : j = i := by simpa using hj
    subst j
    exact hw.trans ((mem_commonAlphabet_iff hN i).mp hp).2.2.1

end
end ImbalancedChen.P5Z.OriginalBetaPrimeSource
