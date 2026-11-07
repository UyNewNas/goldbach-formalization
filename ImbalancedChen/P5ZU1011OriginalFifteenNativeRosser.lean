import ImbalancedChen.P5ZU1011OriginalSixteenArithmeticEligibility
import ImbalancedChen.P5ZU11LoweredCutoffFiniteRosser

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Constructed native ordinary rows for original selected masks1..15. From
the complete true original gate we choose its strict midpoint nu, then
delta=min(3/4096,(nu-gate)/64,(cap-nu)/64), xi=min(w/2,delta), rho=delta.
The actual reduced cutoff and residual level retain these margins. All
positivity and native Rosser gates are proved before its finite count
theorem is used. Support, main, signed AP and centre subtraction use ONE
literal actualSmallRosserPlus coefficient at this constructed row.

No H248 evaluation, physical distribution license, adaptive mean or final
count supplier is assumed. The distinct W16 native construction is outside
this module's claims and remains separately owned.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenNativeRosser

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenInteriorArithmetic U1011OriginalSixteenArithmeticEligibility
open P5U1011JointOverlap
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

def nu (p : Policy) (N : ℕ) (t : Four) : ℝ := interior p (coordinates N t)
def delta (p : Policy) (N : ℕ) (t : Four) : ℝ :=
  min (3 / 4096) (min ((nu p N t - gate p (coordinates N t)) / 64)
    ((cap p (coordinates N t) - nu p N t) / 64))
def xi (p : Policy) (N : ℕ) (t : Four) : ℝ := min (coordinates N t 3 / 2) (delta p N t)
def residualExponent (p : Policy) (N : ℕ) (t : Four) : ℝ :=
  nu p N t - U11SelectedLargest.prefixSum (coordinates N t) - 20 * delta p N t
def cutoffExponent (p : Policy) (N : ℕ) (t : Four) : ℝ :=
  min (coordinates N t 3 - xi p N t) (residualExponent p N t / (2 + delta p N t))
def Z (p : Policy) (N : ℕ) (t : Four) : ℝ := (N : ℝ) ^ cutoffExponent p N t
def D (p : Policy) (N : ℕ) (t : Four) : ℝ := (N : ℝ) ^ residualExponent p N t

private theorem source_joint {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U11Adaptive.source N E) : t ∈ jointSelector N E := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hN)
  exact originalU11_mem_joint hNr ht

theorem smallest_positive {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U11Adaptive.source N E) : 0 < coordinates N t 3 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hp := (slots_prime (source_joint hN ht) 3).one_lt
  exact div_pos (Real.log_pos (by exact_mod_cast hp)) (Real.log_pos hNr)

theorem delta_positive (p : Policy) (N : ℕ) (t : Four)
    (he : TypedEligible p (coordinates N t)) : 0 < delta p N t := by
  have hg := gate_lt_cap p (coordinates N t) he
  have hgi : 0 < nu p N t - gate p (coordinates N t) := by unfold nu interior; linarith
  have hic : 0 < cap p (coordinates N t) - nu p N t := by unfold nu interior; linarith
  exact lt_min (by norm_num) (lt_min (div_pos hgi (by norm_num)) (div_pos hic (by norm_num)))

theorem delta_le_gate_margin (p : Policy) (N : ℕ) (t : Four) :
    delta p N t ≤ (nu p N t - gate p (coordinates N t)) / 64 :=
  (min_le_right _ _).trans (min_le_left _ _)

private theorem value_le_gate (p : Policy) (v : LogFour) (a : ℝ)
    (ha : a ∈ gateValues p v) : a ≤ gate p v := Finset.le_max' _ _ ha

/-- The fixed safety margin pays EVERY full and unselected-square test;
the complete set of original gates is used, not merely the last square. -/
theorem buffered_square_exponents (p : Policy) (hp : p.val < 15) (N : ℕ) (t : Four)
    (he : TypedEligible p (coordinates N t)) :
    (∀ j : Fin 4, fullSquare j (coordinates N t) + 20 * delta p N t < nu p N t) ∧
      (∀ j : Fin 4, ¬Selected p j → selectedSquare p j (coordinates N t) +
        20 * delta p N t < nu p N t) := by
  have hdelta := delta_le_gate_margin p N t
  have hgap : gate p (coordinates N t) < nu p N t := by
    have h := gate_lt_cap p (coordinates N t) he
    unfold nu interior
    linarith
  constructor
  · intro j
    have hj : fullSquare j (coordinates N t) ≤ gate p (coordinates N t) := by
      apply value_le_gate
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)))
    linarith
  · intro j hj
    have hle : selectedSquare p j (coordinates N t) ≤ gate p (coordinates N t) := by
      apply value_le_gate
      apply Finset.mem_insert.mpr
      apply Or.inr
      apply Finset.mem_union_right
      simp only [if_pos hp]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩
    linarith

/-- All native row parameters are constructed. In particular, the real
cutoff is below the actual smallest specified prime, and both strict
Rosser legality conditions are conclusions. -/
theorem native_legality {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U11Adaptive.source N E) (p : Policy) (hp : p.val < 15)
    (he : TypedEligible p (coordinates N t)) :
    0 < delta p N t ∧ 0 < xi p N t ∧ 0 < cutoffExponent p N t ∧
      1 < D p N t ∧ Z p N t ≤ (t.1.1 : ℝ) ∧ Z p N t ≤ D p N t := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hjoint := source_joint hN ht
  have hw := smallest_positive hN ht
  have hd := delta_positive p N t he
  have hxi : 0 < xi p N t := lt_min (div_pos hw (by norm_num)) hd
  have hxile : xi p N t ≤ coordinates N t 3 / 2 := min_le_left _ _
  have hsmall : 0 < coordinates N t 3 - xi p N t := by linarith
  have hlast := (buffered_square_exponents p hp N t he).1 (3 : Fin 4)
  rw [fullSquare_last] at hlast
  have hmargin : 20 * delta p N t < nu p N t - U11SelectedLargest.prefixSum (coordinates N t) := by
    linarith
  have hre : 0 < residualExponent p N t := by unfold residualExponent; linarith
  have hce : 0 < cutoffExponent p N t :=
    lt_min hsmall (div_pos hre (by linarith))
  have hleg := U11LoweredRosser.reduced_physical_level_legal N hNr
    (coordinates N t) (coordinates N t) (nu p N t) (delta p N t) (xi p N t) (delta p N t)
    hsmall hmargin hd
  have hleg' : 1 < D p N t ∧ Z p N t ≤ D p N t := by
    simpa only [D,Z,cutoffExponent,residualExponent,U11SelectedLargest.reducedCutoff] using hleg
  have hzsmall : Z p N t ≤ (t.1.1 : ℝ) := by
    have hpow := slot_rpow hN hjoint (3 : Fin 4)
    have hexp : cutoffExponent p N t ≤ coordinates N t 3 :=
      (min_le_left _ _).trans (by linarith)
    have h := Real.rpow_le_rpow_of_exponent_le hNr.le hexp
    simpa only [Z,slots,Matrix.cons_val_three] using h.trans_eq hpow
  exact ⟨hd,hxi,hce,hleg'.1,hzsmall,hleg'.2⟩

/-- Exact reflection also pays the integer square gates at the buffered
physical total level nu-20delta, with the selected slots unchanged. -/
theorem native_buffered_square_products {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E)
    (p : Policy) (hp : p.val < 15) (he : TypedEligible p (coordinates N t)) :
    (∀ j : Fin 4, (prefixProduct j t : ℝ) * (slots t j : ℝ) ^ 2 <
      (N : ℝ) ^ (nu p N t - 20 * delta p N t)) ∧
    (∀ j : Fin 4, ¬Selected p j → (selectedProduct p t : ℝ) *
      (earlierRemainderProduct p j t : ℝ) * (slots t j : ℝ) ^ 2 <
        (N : ℝ) ^ (nu p N t - 20 * delta p N t)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hs := buffered_square_exponents p hp N t he
  have hjoint := source_joint hN ht
  constructor
  · intro j
    rw [← fullSquare_rpow hN hjoint j]
    exact Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith [hs.1 j])
  · intro j hj
    rw [← selectedSquare_rpow hN hjoint p j]
    exact Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith [hs.2 j hj])

def support (p : Policy) (N : ℕ) (t : Four) : Finset ℕ :=
  actualSmallRosserSupport N (Nat.ceil (Z p N t)) (Z p N t)
def coefficient (p : Policy) (N : ℕ) (t : Four) (d : ℕ) : ℝ :=
  actualSmallRosserPlus N (Nat.ceil (Z p N t)) (Z p N t) (D p N t) d
def main (p : Policy) (N : ℕ) (t : Four) : ℝ :=
  trueLogarithmicIntegral N / (Nat.totient (fullPrefix t) : ℝ) *
    actualSmallRosserPlusDensity N (Nat.ceil (Z p N t)) (Z p N t) (D p N t)
def signedAP (p : Policy) (N : ℕ) (t : Four) : ℝ :=
  ∑ d ∈ support p N t, coefficient p N t d *
    chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (fullPrefix t * d)
def signedCentre (p : Policy) (N : ℕ) (t : Four) : ℝ :=
  ∑ d ∈ support p N t, coefficient p N t d * chenCentrePrimeAPCount N N (fullPrefix t * d)
def estimator (p : Policy) (N : ℕ) (t : Four) : ℝ :=
  ∑ d ∈ support p N t, coefficient p N t d *
    (chenPrimeAPCount N N (fullPrefix t * d) - chenCentrePrimeAPCount N N (fullPrefix t * d))

/-- Every active physical full modulus has the original constructed
total cap. This is a support fact, not an AP distribution license. -/
theorem active_full_modulus_cap {N d : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E)
    (p : Policy) (_hp : p.val < 15) (hactive : coefficient p N t d ≠ 0) :
    ((fullPrefix t * d : ℕ) : ℝ) < (N : ℝ) ^ (nu p N t - 20 * delta p N t) := by
  have hjoint := source_joint hN ht
  have hb : (0 : ℝ) < fullPrefix t := by
    rw [fullPrefix_eq_multiplier]
    exact_mod_cast joint_multiplier_pos hjoint
  have hd : (d : ℝ) < D p N t := (actualSmallRosserPlus_active hactive).2.1
  have hD : D p N t = (N : ℝ) ^ (nu p N t - 20 * delta p N t) / (fullPrefix t : ℝ) := by
    unfold D residualExponent
    rw [show nu p N t - U11SelectedLargest.prefixSum (coordinates N t) - 20 * delta p N t =
      (nu p N t - 20 * delta p N t) - U11SelectedLargest.prefixSum (coordinates N t) by ring]
    exact actual_residual_level hN hjoint _
  rw [Nat.cast_mul]
  calc
    (fullPrefix t : ℝ) * d < (fullPrefix t : ℝ) * D p N t := mul_lt_mul_of_pos_left hd hb
    _ = _ := by
      rw [hD,mul_comm]
      exact div_mul_cancel₀ _ hb.ne'

/-- The constructed cutoff gives the exact same-rho prime-AP/main/centre
dictionary. No distribution estimate or scalar density lower/upper bound
is substituted for the actual finite density. -/
theorem estimator_same_coefficient {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E)
    (p : Policy) (hp : p.val < 15) (he : TypedEligible p (coordinates N t)) :
    estimator p N t = main p N t + signedAP p N t - signedCentre p N t := by
  have hleg := native_legality hN ht p hp he
  have hZ : Z p N t ≤ (slots t 3 : ℝ) := by simpa only [slots,Matrix.cons_val_three] using hleg.2.2.2.2.1
  have hcop := fullPrefix_coprime_lowered_sieve (source_joint hN ht) hZ
  exact currentChen_quotient_actualRosser_plus_main_and_errors N (fullPrefix t)
    (Nat.ceil (Z p N t)) (Z p N t) (D p N t) (Nat.le_ceil _) hcop

/-- Concrete original-mask native row upper bound. The cutoff inclusion
and actual Rosser upper theorem are both proved inputs, not caller-supplied
count or density bounds. All three terms retain the constructed coefficient. -/
theorem native_row_upper {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E)
    (p : Policy) (hp : p.val < 15) (he : TypedEligible p (coordinates N t)) :
    U11Adaptive.weight N t ≤ main p N t + signedAP p N t - signedCentre p N t := by
  have hleg := native_legality hN ht p hp he
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hN)
  have h12 := (U11LoweredRosser.original_carrier_order hNr ht).2.2.2.2.1
  have hZ2 : Z p N t ≤ (t.1.2 : ℝ) :=
    hleg.2.2.2.2.1.trans (by exact_mod_cast h12.le)
  have hweight : U11Adaptive.weight N t =
      ((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2 : ℝ)).card : ℝ) := by
    rw [fullPrefix_eq_multiplier]
    rfl
  have hcount : U11Adaptive.weight N t ≤
      ((chenSiftedQuotientPrimeSource N (fullPrefix t) (Z p N t)).card : ℝ) := by
    rw [hweight]
    exact_mod_cast Finset.card_le_card
      (U11LoweredRosser.siftedSource_subset_lowered N (fullPrefix t) (Z p N t) (t.1.2 : ℝ) hZ2)
  have hup := currentChen_quotient_actualRosser_upper N (fullPrefix t) (Nat.ceil (Z p N t))
    (Z p N t) (D p N t) (Nat.le_ceil _) hleg.2.2.2.1 hleg.2.2.2.2.2
  exact (hcount.trans hup).trans_eq (estimator_same_coefficient hN ht p hp he)

end
end ImbalancedChen.P5Z.U1011OriginalFifteenNativeRosser
