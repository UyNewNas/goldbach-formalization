import ImbalancedChen.P2OriginalSixthCommonScheduleAndFullQ
import ImbalancedChen.RoughAbsoluteDensity
import ImbalancedChen.SmallRoughMainTerm

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original eleven-prefix omitted set is lifted to an independently
defined restriction of the SAME actual rough-modulus support.  All
residual moduli containing an omitted prefix product are retained.  This
divisor cover can overcount a canonical prefix wall; positivity is used
only for its upper bound, never to redefine the original signed rho.
-/

namespace ImbalancedChen.P2OriginalElevenFullModulusOmittedCover
noncomputable section
open Classical
open scoped BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalSixthCompactArithmeticFibre P2OriginalSixthOmittedArithmeticMass
open P2OriginalSixthCommonScheduleAndFullQ P1ActualMovingAffineWallMass

def residualDivisors (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  ((roughPrimeFinset N cap w z).prod id).divisors

def residualMass (N cap : ℕ) (w z : ℝ) : ℝ :=
  ∑ r ∈ residualDivisors N cap w z, 1 / (Nat.totient r : ℝ)

def prefixFibre (ret : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (p : Fin 6 → ℕ) : Finset ℕ :=
  (fixedRoughSupport ret N cap w z).filter (fun b => roughProduct p ∣ b)

def omittedRough (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  (fixedRoughSupport ret N cap w z).filter
    (fun b => ∃ p ∈ omittedTuples c n N, roughProduct p ∣ b)

def omittedRho (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w) (omittedRough ret c n N cap w z)
    (fixedRoughCoefficient ret N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

def omittedModuli (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w) (omittedRough ret c n N cap w z)

theorem omittedRough_subset (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z : ℝ) :
    omittedRough ret c n N cap w z ⊆ fixedRoughSupport ret N cap w z :=
  Finset.filter_subset _ _

/-- This sufficient cover condition keeps the original target, source
tuple and entire actual residual rough product. -/
theorem actual_omitted_prefix_covered (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ)
    (w z : ℝ) {b : ℕ} (hb : b ∈ fixedRoughSupport ret N cap w z)
    {p : Fin 6 → ℕ} (hp : p ∈ omittedTuples c n N) (hdiv : roughProduct p ∣ b) :
    b ∈ omittedRough ret c n N cap w z := Finset.mem_filter.mpr ⟨hb,p,hp,hdiv⟩

/-- No per-prefix residual cut or unit bound replaces this full sum. -/
theorem prefixFibre_mass_le (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z : ℝ)
    (p : Fin 6 → ℕ) (hp : p ∈ omittedTuples c n N) :
    (∑ b ∈ prefixFibre ret N cap w z p, 1 / (Nat.totient b : ℝ)) ≤
      tupleWeight p * residualMass N cap w z := by
  let U := prefixFibre ret N cap w z p
  let T := U.image (fun b => b / roughProduct p)
  have hdiv (b : ℕ) (hb : b ∈ U) : roughProduct p ∣ b := (Finset.mem_filter.mp hb).2
  have hsub : T ⊆ residualDivisors N cap w z := by
    intro r hr
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hr
    have hbS := (Finset.mem_filter.mp hb).1
    have hbM := fixedRoughSupport_subset_primeProduct_divisors ret N cap w z hbS
    obtain ⟨hbdiv,hM⟩ := Nat.mem_divisors.mp hbM
    apply Nat.mem_divisors.mpr
    refine ⟨?_,hM⟩
    have hquot : b / roughProduct p ∣ b := by
      refine ⟨roughProduct p,?_⟩
      rw [mul_comm,Nat.mul_div_cancel' (hdiv b hb)]
    exact hquot.trans hbdiv
  have hinj : Set.InjOn (fun b => b / roughProduct p) (U : Set ℕ) := by
    intro b hb d hd heq
    calc
      b = roughProduct p * (b / roughProduct p) := (Nat.mul_div_cancel' (hdiv b hb)).symm
      _ = roughProduct p * (d / roughProduct p) := congrArg (fun r => roughProduct p*r) heq
      _ = d := Nat.mul_div_cancel' (hdiv d hd)
  have hsplit (b : ℕ) (hb : b ∈ U) :
      1 / (Nat.totient b : ℝ) = tupleWeight p * (1 / (Nat.totient (b / roughProduct p) : ℝ)) := by
    have hsf := fixedRoughSupport_squarefree ret N cap w z (Finset.mem_filter.mp hb).1
    have hsf' : Squarefree (roughProduct p * (b / roughProduct p)) := by
      rw [Nat.mul_div_cancel' (hdiv b hb)]
      exact hsf
    have hcop := Nat.coprime_of_squarefree_mul hsf'
    have hphi : Nat.totient b = Nat.totient (roughProduct p) * Nat.totient (b / roughProduct p) := by
      calc
        _ = Nat.totient (roughProduct p * (b / roughProduct p)) :=
          congrArg Nat.totient (Nat.mul_div_cancel' (hdiv b hb)).symm
        _ = _ := Nat.totient_mul hcop
    rw [hphi,Nat.cast_mul,original_tuple_weight_eq_reciprocalTotient c N
      (Finset.mem_filter.mp hp).1]
    simp only [one_div,mul_inv_rev]
    ring
  have hw : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  calc
    _ = ∑ b ∈ U, tupleWeight p * (1 / (Nat.totient (b / roughProduct p) : ℝ)) :=
      Finset.sum_congr rfl hsplit
    _ = tupleWeight p * ∑ r ∈ T, 1 / (Nat.totient r : ℝ) := by
      rw [Finset.sum_image hinj,Finset.mul_sum]
    _ ≤ tupleWeight p * residualMass N cap w z := by
      apply mul_le_mul_of_nonneg_left _ hw
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-- All residual rough moduli in the actual omitted cover, after the
complete modulus sum, are bounded by the TRUE residual Euler mass. -/
theorem omittedRough_mass_le (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z : ℝ) :
    (∑ b ∈ omittedRough ret c n N cap w z, 1 / (Nat.totient b : ℝ)) ≤
      omittedMass c n N * residualMass N cap w z := by
  let S := fixedRoughSupport ret N cap w z
  let O := omittedTuples c n N
  have hpoint (b : ℕ) (hb : b ∈ S) :
      (if ∃ p ∈ O, roughProduct p ∣ b then 1 / (Nat.totient b : ℝ) else 0) ≤
        ∑ p ∈ O, if roughProduct p ∣ b then 1 / (Nat.totient b : ℝ) else 0 := by
    have hnonneg (p : Fin 6 → ℕ) :
        0 ≤ (if roughProduct p ∣ b then 1 / (Nat.totient b : ℝ) else 0) := by
      split_ifs <;> positivity
    by_cases h : ∃ p ∈ O, roughProduct p ∣ b
    · obtain ⟨p,hp,hpd⟩ := h
      rw [if_pos (show ∃ p ∈ O, roughProduct p ∣ b from ⟨p,hp,hpd⟩)]
      simpa only [if_pos hpd] using Finset.single_le_sum (fun q _ => hnonneg q) hp
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun p _ => hnonneg p)
  calc
    _ = ∑ b ∈ S, if ∃ p ∈ O, roughProduct p ∣ b then 1 / (Nat.totient b : ℝ) else 0 := by
      rw [omittedRough,Finset.sum_filter]
    _ ≤ ∑ b ∈ S, ∑ p ∈ O, if roughProduct p ∣ b then 1 / (Nat.totient b : ℝ) else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ p ∈ O, ∑ b ∈ prefixFibre ret N cap w z p, 1 / (Nat.totient b : ℝ) := by
      rw [Finset.sum_comm]
      simp only [prefixFibre,Finset.sum_filter]
    _ ≤ ∑ p ∈ O, tupleWeight p * residualMass N cap w z :=
      Finset.sum_le_sum (fun p hp => prefixFibre_mass_le ret c n N cap w z p hp)
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- The coefficient restricted by its independently defined omitted
rough carrier is precisely the original physical coefficient at every
retained full q=e*b.  Unique small/rough decomposition discharges it. -/
theorem omittedRho_eq_actual_on_support (ret : List ℕ → Bool) (c : Cell)
    (n N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : q ∈ omittedModuli ret c n N cap w z) :
    omittedRho ret c n N cap w z L q = actualSmallRoughRho ret N cap w z L q := by
  obtain ⟨⟨e,b⟩,heb,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨he,hb⟩ := Finset.mem_product.mp heb
  have hbS := omittedRough_subset ret c n N cap w z hb
  rw [omittedRho,actualSmallRoughRho]
  rw [smallRoughRho_mul (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt ret N cap w z
      (omittedRough_subset ret c n N cap w z hd)) _ _ _ he hb]
  rw [smallRoughRho_mul (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt ret N cap w z hd) _ _ _ he hbS]

theorem omitted_actual_test_eq (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ)
    (w z L : ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ omittedModuli ret c n N cap w z, omittedRho ret c n N cap w z L q * F q) =
      ∑ q ∈ omittedModuli ret c n N cap w z, actualSmallRoughRho ret N cap w z L q * F q := by
  apply Finset.sum_congr rfl
  intro q hq
  rw [omittedRho_eq_actual_on_support ret c n N cap w z L hq]

end
end ImbalancedChen.P2OriginalElevenFullModulusOmittedCover
