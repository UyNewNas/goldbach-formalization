import ImbalancedChen.P5ZU1011OriginalSixteenArithmeticEligibility
import ImbalancedChen.P5ZU1011OriginalSixteenBoxCertificates
import ImbalancedChen.P5ZU11LoweredCutoffFiniteRosser

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

One FIXED rational ordinary level and fixed residual Rosser coefficient for
an entire positive original-mask box. All parameters below depend only on
the policy and rational box, before N and before every prime tuple. A true
whole-box finite Boolean certificate constructs the separation; no uniform
physical family, density bound, AP estimate or count conclusion is assumed.

This uses the separate gate-upper/cap-lower certificate. Correlated positive
pointwise margins alone are not claimed to separate a box's gate supremum
from its cap infimum. W16 has separate ownership and is excluded here.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenFixedCellNative

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenInteriorArithmetic
open U1011OriginalSixteenArithmeticEligibility P5U1011JointOverlap
open P2OriginalFourthCapProducerInterface
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

def gateUpperValues (p : Policy) (B : Box) : Finset ℚ :=
  insert (1 / 2) ((Finset.univ.image (fun j : Fin 4 => (fullSquarePiece j).upper B.lo B.hi)) ∪
    ((Finset.univ.filter (fun j : Fin 4 => ¬Selected p j)).image
      (fun j => (selectedSquarePiece p j).upper B.lo B.hi)))
theorem gateUpperValues_nonempty (p : Policy) (B : Box) : (gateUpperValues p B).Nonempty :=
  ⟨1 / 2,Finset.mem_insert_self _ _⟩
def G (p : Policy) (B : Box) : ℚ := (gateUpperValues p B).max' (gateUpperValues_nonempty p B)
def nu (p : Policy) (B : Box) : ℚ := (G p B + capLower p B) / 2
def delta (p : Policy) (B : Box) : ℚ :=
  min (3 / 4096) (min ((nu p B - G p B) / 64) ((capLower p B - nu p B) / 64))
def xi (p : Policy) (B : Box) : ℚ := min (B.lo 3 / 2) (delta p B)
def rho (p : Policy) (B : Box) : ℚ := delta p B
def Tplus (B : Box) : ℚ := B.hi 0 + B.hi 1 + B.hi 2 + B.hi 3
def residualExponent (p : Policy) (B : Box) : ℚ := nu p B - Tplus B - 20 * delta p B
def cutoffExponent (p : Policy) (B : Box) : ℚ :=
  min (B.lo 3 - xi p B) (residualExponent p B / (2 + rho p B))
def Z (p : Policy) (B : Box) (N : ℕ) : ℝ := (N : ℝ) ^ (cutoffExponent p B : ℝ)
def D (p : Policy) (B : Box) (N : ℕ) : ℝ := (N : ℝ) ^ (residualExponent p B : ℝ)

theorem G_lt_capLower (p : Policy) (hp : p.val < 15) (B : Box)
    (htest : wholeBoxEligibleTest p B = true) : G p B < capLower p B := by
  have h : WholeBoxEligible p B := of_decide_eq_true htest
  have hextra : ∀ j : Fin 4, ¬Selected p j →
      (selectedSquarePiece p j).upper B.lo B.hi < capLower p B := by
    simpa only [if_pos hp] using h.2.2
  have hall : ∀ a ∈ gateUpperValues p B, a < capLower p B := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact h.1
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
        exact h.2.1 j
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
        exact hextra j (Finset.mem_filter.mp hj).2
  exact hall _ (Finset.max'_mem _ _)

theorem half_lt_nu (p : Policy) (hp : p.val < 15) (B : Box)
    (htest : wholeBoxEligibleTest p B = true) : (1 / 2 : ℚ) < nu p B := by
  have hh : (1 / 2 : ℚ) ≤ G p B := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hc := G_lt_capLower p hp B htest
  unfold nu
  linarith

private theorem fullUpper_le_G (p : Policy) (B : Box) (j : Fin 4) :
    (fullSquarePiece j).upper B.lo B.hi ≤ G p B := by
  apply Finset.le_max'
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)))

private theorem selectedUpper_le_G (p : Policy) (B : Box) (j : Fin 4) (hj : ¬Selected p j) :
    (selectedSquarePiece p j).upper B.lo B.hi ≤ G p B := by
  apply Finset.le_max'
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩)))

theorem lastUpper_eq_Tplus (B : Box) :
    (fullSquarePiece 3).upper B.lo B.hi = Tplus B + B.hi 3 := by
  norm_num [fullSquarePiece,Affine.upper,Affine.neg,Affine.lower,Tplus,Fin.sum_univ_succ]
  <;> ring

/-- Every rational row parameter is fixed from the certificate before N.
The last full square pays the residual margin at the UPPER prefix sum. -/
theorem rational_parameters (p : Policy) (hp : p.val < 15) (B : Box)
    (hvalid : B.Valid) (hpositive : 0 < B.lo 3) (htest : wholeBoxEligibleTest p B = true) :
    G p B < nu p B ∧ nu p B < capLower p B ∧ 0 < delta p B ∧
      0 < xi p B ∧ 0 < rho p B ∧ 0 < residualExponent p B ∧ 0 < cutoffExponent p B := by
  have hgc := G_lt_capLower p hp B htest
  have hgn : G p B < nu p B := by unfold nu; linarith
  have hnc : nu p B < capLower p B := by unfold nu; linarith
  have hd : 0 < delta p B := lt_min (by norm_num)
    (lt_min (div_pos (sub_pos.mpr hgn) (by norm_num)) (div_pos (sub_pos.mpr hnc) (by norm_num)))
  have hx : 0 < xi p B := lt_min (div_pos hpositive (by norm_num)) hd
  have hdle : delta p B ≤ (nu p B - G p B) / 64 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hlast := fullUpper_le_G p B (3 : Fin 4)
  rw [lastUpper_eq_Tplus] at hlast
  have hhi : 0 < B.hi 3 := hpositive.trans_le (hvalid 3)
  have hre : 0 < residualExponent p B := by unfold residualExponent; linarith
  have hsmall : 0 < B.lo 3 - xi p B := by
    have hxi : xi p B ≤ B.lo 3 / 2 := min_le_left _ _
    linarith
  have hcut : 0 < cutoffExponent p B :=
    lt_min hsmall (div_pos hre (by change 0 < 2 + delta p B; linarith))
  exact ⟨hgn,hnc,hd,hx,hd,hre,hcut⟩

/-- A single certified midpoint and safety reserve work at EVERY point of
the closed box, including its arithmetic boundary points. -/
theorem whole_box_margins (p : Policy) (hp : p.val < 15) (B : Box)
    (htest : wholeBoxEligibleTest p B = true) {v : LogFour} (hv : v ∈ B.region) :
    (nu p B : ℝ) < cap p v ∧
      (∀ j : Fin 4, fullSquare j v + 20 * (delta p B : ℝ) < (nu p B : ℝ)) ∧
      (∀ j : Fin 4, ¬Selected p j → selectedSquare p j v + 20 * (delta p B : ℝ) < (nu p B : ℝ)) := by
  have hgc := G_lt_capLower p hp B htest
  have hgapQ : G p B < nu p B := by unfold nu; linarith
  have hnuQ : nu p B < capLower p B := by unfold nu; linarith
  have hgap : (G p B : ℝ) < (nu p B : ℝ) := by exact_mod_cast hgapQ
  have hnuR : (nu p B : ℝ) < (capLower p B : ℝ) := by exact_mod_cast hnuQ
  have hdQ : delta p B ≤ (nu p B - G p B) / 64 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hd : (delta p B : ℝ) ≤ ((nu p B : ℝ) - (G p B : ℝ)) / 64 := by exact_mod_cast hdQ
  refine ⟨hnuR.trans_le (cap_bounds p B hv).1,?_,?_⟩
  · intro j
    have hsq := (fullSquarePiece j).eval_le_upper B.lo B.hi v hv.1 hv.2
    rw [fullSquarePiece_eval] at hsq
    have hG : ((fullSquarePiece j).upper B.lo B.hi : ℝ) ≤ (G p B : ℝ) := by
      exact_mod_cast fullUpper_le_G p B j
    linarith
  · intro j hj
    have hsq := (selectedSquarePiece p j).eval_le_upper B.lo B.hi v hv.1 hv.2
    rw [selectedSquarePiece_eval] at hsq
    have hG : ((selectedSquarePiece p j).upper B.lo B.hi : ℝ) ≤ (G p B : ℝ) := by
      exact_mod_cast selectedUpper_le_G p B j hj
    linarith

private theorem source_joint {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U11Adaptive.source N E) : t ∈ jointSelector N E := by
  exact originalU11_mem_joint (by exact_mod_cast (Nat.le_of_lt hN)) ht

/-- The row support is common to the whole box. In particular it is NOT
the tuple-dependent midpoint coefficient of the preceding native caller. -/
def support (p : Policy) (B : Box) (N : ℕ) : Finset ℕ :=
  actualSmallRosserSupport N (Nat.ceil (Z p B N)) (Z p B N)
def coefficient (p : Policy) (B : Box) (N d : ℕ) : ℝ :=
  actualSmallRosserPlus N (Nat.ceil (Z p B N)) (Z p B N) (D p B N) d
def main (p : Policy) (B : Box) (N : ℕ) (t : Four) : ℝ :=
  trueLogarithmicIntegral N / (Nat.totient (fullPrefix t) : ℝ) *
    actualSmallRosserPlusDensity N (Nat.ceil (Z p B N)) (Z p B N) (D p B N)
def signedAP (p : Policy) (B : Box) (N : ℕ) (t : Four) : ℝ :=
  ∑ d ∈ support p B N, coefficient p B N d *
    chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (fullPrefix t * d)
def signedCentre (p : Policy) (B : Box) (N : ℕ) (t : Four) : ℝ :=
  ∑ d ∈ support p B N, coefficient p B N d * chenCentrePrimeAPCount N N (fullPrefix t * d)
def estimator (p : Policy) (B : Box) (N : ℕ) (t : Four) : ℝ :=
  ∑ d ∈ support p B N, coefficient p B N d *
    (chenPrimeAPCount N N (fullPrefix t * d) - chenCentrePrimeAPCount N N (fullPrefix t * d))

theorem native_legality {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U11Adaptive.source N E) (p : Policy) (hp : p.val < 15) (B : Box)
    (hvalid : B.Valid) (hpositive : 0 < B.lo 3) (htest : wholeBoxEligibleTest p B = true)
    (hbox : coordinates N t ∈ B.region) :
    0 < Z p B N ∧ 1 < D p B N ∧ Z p B N ≤ (t.1.1 : ℝ) ∧ Z p B N ≤ D p B N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hpar := rational_parameters p hp B hvalid hpositive htest
  have hre : (0 : ℝ) < (residualExponent p B : ℝ) := by exact_mod_cast hpar.2.2.2.2.2.1
  have hrho : (0 : ℝ) < (rho p B : ℝ) := by exact_mod_cast hpar.2.2.2.2.1
  have hcutle : (cutoffExponent p B : ℝ) ≤ (residualExponent p B : ℝ) := by
    have hq : (residualExponent p B : ℝ) / (2 + (rho p B : ℝ)) ≤ (residualExponent p B : ℝ) := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    have hminQ : cutoffExponent p B ≤ residualExponent p B / (2 + rho p B) := min_le_right _ _
    have hminR : (cutoffExponent p B : ℝ) ≤ (residualExponent p B : ℝ) / (2 + (rho p B : ℝ)) := by
      exact_mod_cast hminQ
    exact hminR.trans hq
  have hZfirst : Z p B N ≤ (t.1.1 : ℝ) := by
    have hx : (0 : ℝ) ≤ (xi p B : ℝ) := by exact_mod_cast hpar.2.2.2.1.le
    have hc : (cutoffExponent p B : ℝ) ≤ (B.lo 3 : ℝ) := by
      have h : cutoffExponent p B ≤ B.lo 3 - xi p B := min_le_left _ _
      have h' : (cutoffExponent p B : ℝ) ≤ (B.lo 3 : ℝ) - (xi p B : ℝ) := by exact_mod_cast h
      linarith
    have hpow := slot_rpow hN (source_joint hN ht) (3 : Fin 4)
    have h := Real.rpow_le_rpow_of_exponent_le hNr.le (hc.trans (hbox.1 3))
    simpa only [Z,slots,Matrix.cons_val_three] using h.trans_eq hpow
  exact ⟨Real.rpow_pos_of_pos hNpos _,Real.one_lt_rpow hNr hre,hZfirst,
    Real.rpow_le_rpow_of_exponent_le hNr.le hcutle⟩

/-- The whole fixed coefficient family has the buffered physical full
modulus cap, proved from the box upper prefix and coefficient activity.
This remains a support fact and supplies no distribution theorem. -/
theorem active_full_modulus_cap {N d : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E)
    (p : Policy) (_hp : p.val < 15) (B : Box) (hbox : coordinates N t ∈ B.region)
    (hactive : coefficient p B N d ≠ 0) :
    ((fullPrefix t * d : ℕ) : ℝ) < (N : ℝ) ^ ((nu p B : ℝ) - 20 * (delta p B : ℝ)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hsum : U11SelectedLargest.prefixSum (coordinates N t) ≤ (Tplus B : ℝ) := by
    simp only [U11SelectedLargest.prefixSum,Tplus,Rat.cast_add]
    linarith [hbox.2 0,hbox.2 1,hbox.2 2,hbox.2 3]
  have hb : (fullPrefix t : ℝ) ≤ (N : ℝ) ^ (Tplus B : ℝ) := by
    rw [← fullPrefix_rpow hN (source_joint hN ht)]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le hsum
  have hd : (d : ℝ) < D p B N := (actualSmallRosserPlus_active hactive).2.1
  rw [Nat.cast_mul]
  calc
    (fullPrefix t : ℝ) * d ≤ (N : ℝ) ^ (Tplus B : ℝ) * d :=
      mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)
    _ < (N : ℝ) ^ (Tplus B : ℝ) * D p B N :=
      mul_lt_mul_of_pos_left hd (Real.rpow_pos_of_pos hNpos _)
    _ = _ := by
      rw [D,← Real.rpow_add hNpos]
      congr 1
      simp only [residualExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
      ring

/-- Both the selected natural critical interval and all buffered raw
square gates are uniform at the ONE fixed rational nu of the box. -/
theorem native_selected_and_squares {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E)
    (p : Policy) (hp : p.val < 15) (B : Box) (htest : wholeBoxEligibleTest p B = true)
    (hbox : coordinates N t ∈ B.region) :
    ((N : ℝ) ^ (2 * (nu p B : ℝ) - 1) < (selectedProduct p t : ℝ) ∧
      (selectedProduct p t : ℝ) < (N : ℝ) ^ ((19 / 32 : ℝ) - (2 / 3 : ℝ) * (nu p B : ℝ))) ∧
    (∀ j : Fin 4, (prefixProduct j t : ℝ) * (slots t j : ℝ) ^ 2 <
      (N : ℝ) ^ ((nu p B : ℝ) - 20 * (delta p B : ℝ))) ∧
    (∀ j : Fin 4, ¬Selected p j → (selectedProduct p t : ℝ) *
      (earlierRemainderProduct p j t : ℝ) * (slots t j : ℝ) ^ 2 <
        (N : ℝ) ^ ((nu p B : ℝ) - 20 * (delta p B : ℝ))) := by
  have hm := whole_box_margins p hp B htest hbox
  have hjoint := source_joint hN ht
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  refine ⟨actual_selected_critical_interval hN hjoint p hp hm.1,?_,?_⟩
  · intro j
    rw [← fullSquare_rpow hN hjoint j]
    exact Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith [hm.2.1 j])
  · intro j hj
    rw [← selectedSquare_rpow hN hjoint p j]
    exact Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith [hm.2.2 j hj])

theorem estimator_same_coefficient {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E)
    (p : Policy) (hp : p.val < 15) (B : Box) (hvalid : B.Valid) (hpositive : 0 < B.lo 3)
    (htest : wholeBoxEligibleTest p B = true) (hbox : coordinates N t ∈ B.region) :
    estimator p B N t = main p B N t + signedAP p B N t - signedCentre p B N t := by
  have hleg := native_legality hN ht p hp B hvalid hpositive htest hbox
  have hZ : Z p B N ≤ (slots t 3 : ℝ) := by simpa only [slots,Matrix.cons_val_three] using hleg.2.2.1
  have hcop := fullPrefix_coprime_lowered_sieve (source_joint hN ht) hZ
  exact currentChen_quotient_actualRosser_plus_main_and_errors N (fullPrefix t)
    (Nat.ceil (Z p B N)) (Z p B N) (D p B N) (Nat.le_ceil _) hcop

theorem native_row_upper {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E)
    (p : Policy) (hp : p.val < 15) (B : Box) (hvalid : B.Valid) (hpositive : 0 < B.lo 3)
    (htest : wholeBoxEligibleTest p B = true) (hbox : coordinates N t ∈ B.region) :
    U11Adaptive.weight N t ≤ main p B N t + signedAP p B N t - signedCentre p B N t := by
  have hleg := native_legality hN ht p hp B hvalid hpositive htest hbox
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hN)
  have h12 := (U11LoweredRosser.original_carrier_order hNr ht).2.2.2.2.1
  have hZ2 : Z p B N ≤ (t.1.2 : ℝ) := hleg.2.2.1.trans (by exact_mod_cast h12.le)
  have hweight : U11Adaptive.weight N t =
      ((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2 : ℝ)).card : ℝ) := by
    rw [fullPrefix_eq_multiplier]
    rfl
  have hcount : U11Adaptive.weight N t ≤
      ((chenSiftedQuotientPrimeSource N (fullPrefix t) (Z p B N)).card : ℝ) := by
    rw [hweight]
    exact_mod_cast Finset.card_le_card
      (U11LoweredRosser.siftedSource_subset_lowered N (fullPrefix t) (Z p B N) (t.1.2 : ℝ) hZ2)
  have hup := currentChen_quotient_actualRosser_upper N (fullPrefix t) (Nat.ceil (Z p B N))
    (Z p B N) (D p B N) (Nat.le_ceil _) hleg.2.1 hleg.2.2.2
  exact (hcount.trans hup).trans_eq
    (estimator_same_coefficient hN ht p hp B hvalid hpositive htest hbox)

/-- An arbitrary literal finite subfamily inside this box uses the same
fixed coefficient. No hUniformFamily or analytic counting supplier occurs. -/
theorem fixed_family_upper {N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop)
    (T : Finset Four) (hT : T ⊆ U11Adaptive.source N E)
    (p : Policy) (hp : p.val < 15) (B : Box) (hvalid : B.Valid) (hpositive : 0 < B.lo 3)
    (htest : wholeBoxEligibleTest p B = true)
    (hbox : ∀ t ∈ T, coordinates N t ∈ B.region) :
    (∑ t ∈ T, U11Adaptive.weight N t) ≤
      (∑ t ∈ T, main p B N t) + (∑ t ∈ T, signedAP p B N t) - ∑ t ∈ T, signedCentre p B N t := by
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  exact native_row_upper hN (hT ht) p hp B hvalid hpositive htest (hbox t ht)

/-- The actual density is common before tuples are summed. This exact
identity exposes the fixed-box prime-harmonic mean without assuming it. -/
theorem sum_main_eq_common_density (p : Policy) (B : Box) (N : ℕ) (T : Finset Four) :
    (∑ t ∈ T, main p B N t) =
      (trueLogarithmicIntegral N *
        actualSmallRosserPlusDensity N (Nat.ceil (Z p B N)) (Z p B N) (D p B N)) *
      ∑ t ∈ T, 1 / (Nat.totient (fullPrefix t) : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  unfold main
  ring

end
end ImbalancedChen.P5Z.U1011OriginalFifteenFixedCellNative
