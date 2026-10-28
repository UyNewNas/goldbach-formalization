import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted
import ImbalancedChen.P2OriginalSelectedNativeSmallExtension

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual negative-single children of the ORIGINAL 21-term mother:
  M=N, a=(Q/d)^(50/227), upper exponents 5/11,10/29,25/61.
Original p|d rows remain present. The old source mask is d*N, not d*p*N.

The child square and its ordinary residual cutoff-square are proved from
these actual windows. The existing native lower Rosser support theorem
then supplies its real residual prime word. Old selected labels, full and
selected-complement squares and one Q persist on the complete child word.
No ordinary rho is identified with an enhanced H248 density.
-/
namespace ImbalancedChen.P2OriginalNegativeSingleSameQSupport
noncomputable section
open scoped Classical BigOperators
open Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalSelectedIntegerPrefixSquares P2OriginalSelectedNativeSmallExtension
open P2EnhancedNativeLowerAtomSupport

/-- The three distinct original negative windows, in literal RHS order. -/
def negativeParameter (j : Fin 3) : ℝ :=
  ![11/5,29/10,61/25] j

def lowerCutoff (Q : ℝ) (d : ℕ) : ℝ := cutoff Q d (227/50)

def negativeWindow (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 3) : Finset ℕ :=
  primeWindow N (lowerCutoff Q d) (cutoff Q d (negativeParameter j))

def childLevel (Q : ℝ) (d p : ℕ) : ℝ := Q / ((d*p : ℕ) : ℝ)

/-- Literal ordinary lower coefficient on the actual child source.
    The original old d*N mask, cutoff a and level Q/(d*p) are retained. -/
def ordinaryChildLower (N : ℕ) (Q : ℝ) (d p k : ℕ) : ℝ :=
  actualSmallRosserMinus (d*N) (Nat.ceil (lowerCutoff Q d))
    (lowerCutoff Q d) (childLevel Q d p) k

private theorem negative_parameter_ge_two (j : Fin 3) : 2 ≤ negativeParameter j := by
  fin_cases j <;> norm_num [negativeParameter]

private theorem negative_exponent_budget (j : Fin 3) :
    (2/(227/50 : ℝ)) + 1/negativeParameter j ≤ 1 := by
  fin_cases j <;> norm_num [negativeParameter]

private theorem rpow_sq (R e : ℝ) (hR : 0 < R) : (R^e)^2 = R^(2*e) := by
  rw [mul_comm (2 : ℝ) e, Real.rpow_mul hR.le]
  norm_num

/-- The small/ordinary cutoff at the ORIGINAL 227/50 query is >1. -/
theorem lowerCutoff_one_lt {Q : ℝ} {d : ℕ} (hR : 1 < Q/(d : ℝ)) :
    1 < lowerCutoff Q d := by
  exact Real.one_lt_rpow hR (by norm_num : (0 : ℝ) < 1/(227/50 : ℝ))

/-- The actual prime window alone pays the child p-square. -/
theorem negative_prime_square {Q : ℝ} {d p : ℕ} (hd : 0 < d)
    (hR : 1 < Q/(d : ℝ)) (j : Fin 3)
    (hp : (p : ℝ) < cutoff Q d (negativeParameter j)) :
    (d : ℝ) * (p : ℝ)^2 < Q := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hw : 0 < negativeParameter j := lt_of_lt_of_le (by norm_num) (negative_parameter_ge_two j)
  have hexp : 1/negativeParameter j ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hw).mpr
    linarith [negative_parameter_ge_two j]
  have hcut : cutoff Q d (negativeParameter j) ≤ Real.sqrt (Q/(d : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hR.le hexp
  have hsquare : (p : ℝ)^2 < Q/(d : ℝ) :=
    (Real.lt_sqrt (Nat.cast_nonneg p)).mp (hp.trans_le hcut)
  calc
    (d : ℝ) * (p : ℝ)^2 < (d : ℝ) * (Q/(d : ℝ)) :=
      mul_lt_mul_of_pos_left hsquare hdR
    _ = Q := by field_simp [hdR.ne']

/-- Crucial ordinary-residual head bound, proved for ALL three actual
    windows. Worst exponent is 100/227+5/11<1, not a new licence. -/
theorem negative_child_cutoff_square {Q : ℝ} {d p : ℕ} (hd : 0 < d)
    (hR : 1 < Q/(d : ℝ)) (j : Fin 3) (hpPrime : p.Prime)
    (hp : (p : ℝ) < cutoff Q d (negativeParameter j)) :
    (lowerCutoff Q d)^2 < childLevel Q d p := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hpPrime.pos
  have hres : 0 < Q/(d : ℝ) := zero_lt_one.trans hR
  have ha0 : 0 < lowerCutoff Q d := zero_lt_one.trans (lowerCutoff_one_lt hR)
  have ha2 : (lowerCutoff Q d)^2 = (Q/(d : ℝ))^(2/(227/50 : ℝ)) := by
    dsimp [lowerCutoff,cutoff]
    rw [rpow_sq _ _ hres]
    congr 1
    ring
  have hprod : (lowerCutoff Q d)^2 * (p : ℝ) < Q/(d : ℝ) := by
    calc
      _ < (lowerCutoff Q d)^2 * cutoff Q d (negativeParameter j) :=
        mul_lt_mul_of_pos_left hp (sq_pos_of_pos ha0)
      _ = (Q/(d : ℝ))^((2/(227/50 : ℝ))+1/negativeParameter j) := by
        rw [ha2,cutoff,← Real.rpow_add hres]
      _ ≤ (Q/(d : ℝ))^1 :=
        Real.rpow_le_rpow_of_exponent_le hR.le (negative_exponent_budget j)
      _ = Q/(d : ℝ) := by simp
  unfold childLevel
  rw [Nat.cast_mul,← div_div]
  exact (lt_div_iff₀ hpR).mpr hprod

/-- A genuine nonzero native ordinary coefficient therefore supplies
    its actual residual prime word, without assuming residual D-well. -/
theorem negative_ordinary_residual_well (N : ℕ) {Q : ℝ} {d p k : ℕ}
    (hd : 0 < d) (hR : 1 < Q/(d : ℝ)) (j : Fin 3)
    (hp : p ∈ negativeWindow N Q d j)
    (hk : ordinaryChildLower N Q d p k ≠ 0) :
    actualDwellSupport (childLevel Q d p) k.primeFactorsList.reverse := by
  have hpData := mem_primeWindow.mp hp
  exact actual_minus_residual_well hk
    (negative_child_cutoff_square hd hR j hpData.1 hpData.2.2.2).le

/-- The same actual nonzero coefficient also pays the COMPLETE physical
    modulus, including k=1. The level is the old common Q divided by d*p. -/
theorem negative_native_physical_support {N : ℕ} {Q : ℝ} {d p k : ℕ}
    (hd : 0 < d) (hp : p.Prime) (hk : ordinaryChildLower N Q d p k ≠ 0) :
    (((d*p)*k : ℕ) : ℝ) < Q := by
  have hdp : 0 < ((d*p : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hd hp.pos)
  have hklevel : (k : ℝ) < childLevel Q d p :=
    (actualSmallRosserMinus_active hk).2.1
  calc
    (((d*p)*k : ℕ) : ℝ) = ((d*p : ℕ) : ℝ) * (k : ℝ) := by rw [Nat.cast_mul]
    _ < ((d*p : ℕ) : ℝ) * childLevel Q d p := mul_lt_mul_of_pos_left hklevel hdp
    _ = Q := by unfold childLevel; field_simp [hdp.ne']

/-- Below the selected new prime, the INDEPENDENT original unscaled
    source and quotient carriers really coincide at the unchanged d*N
    mask. This holds even when p|d; those original bad rows are not erased. -/
theorem negative_child_source_eq_quotient (N d p : ℕ) (a : ℝ)
    (hp : p.Prime) (hap : a ≤ (p : ℝ)) :
    sourceSieveCarrier N (d*p) (d*N) a = sieveCarrier N (d*p) (d*N) a := by
  rw [sourceSieveCarrier_eq_ite, if_pos]
  apply (sifted_mul_iff (d*N) d p a).mpr
  constructor
  · intro q hq hc hz hqd
    exact siftedLE_of_dvd_modulus (dvd_mul_right d N) a q hq hc hz.le hqd
  · exact sifted_prime_of_le hp hap

/-- Literal mother single term, with actual original windows and mask.
    No centre-prime, p|d or unit contribution is silently removed. -/
theorem negative_mother_eq_quotient_sum (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 3) :
    fourthRowMotherSingle N d N (lowerCutoff Q d) (cutoff Q d (negativeParameter j)) =
      ∑ p ∈ negativeWindow N Q d j,
        (sieveCount N (d*p) (d*N) (lowerCutoff Q d) : ℝ) := by
  unfold fourthRowMotherSingle negativeWindow
  apply Finset.sum_congr rfl
  intro p hp
  have hpData := mem_primeWindow.mp hp
  simp only [sourceSieveCount,sieveCount,
    negative_child_source_eq_quotient N d p _ hpData.1 hpData.2.2.1]

/-- Reuse the external exact original-window bad-prime split; the
    squarefree good side is not substituted for the full negative row. -/
theorem negative_mother_good_bad (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 3) :
    fourthRowMotherSingle N d N (lowerCutoff Q d) (cutoff Q d (negativeParameter j)) =
      fourthRowMotherSingle N d (d*N) (lowerCutoff Q d) (cutoff Q d (negativeParameter j)) +
        fourthRowMotherBadPrime N d (lowerCutoff Q d) (cutoff Q d (negativeParameter j)) :=
  fourthRowMother_negative_split N d _ _

/-- Complete actual negative child d*p*k: BOTH integer gate systems at
    the same Q=N^cap, unchanged original selected labels and exact product.
    Input gates belong only to the old original root, not to a candidate
    output or an invented H248 rho. -/
theorem negative_single_native_complete_gates (N : ℕ) (cap : ℝ) {d p k : ℕ}
    (hd : 0 < d) (hR : 1 < (N : ℝ)^cap/(d : ℝ)) (j : Fin 3)
    (hp : p ∈ negativeWindow N ((N : ℝ)^cap) d j)
    (hk : ordinaryChildLower N ((N : ℝ)^cap) d p k ≠ 0)
    (old : List (ℕ × Bool)) (holdprod : (old.map Prod.fst).prod = d)
    (hfull : IntegerSquareGates N cap 1 (old.map Prod.fst))
    (hselected : IntegerSquareGates N cap (selectedPrimes old).prod (remainingPrimes old)) :
    let afterP := appendUnselected old [p]
    let whole := appendUnselected afterP k.primeFactorsList.reverse
    IntegerSquareGates N cap 1 (whole.map Prod.fst) ∧
      IntegerSquareGates N cap (selectedPrimes whole).prod (remainingPrimes whole) ∧
      selectedPrimes whole = selectedPrimes old ∧
      (whole.map Prod.fst).prod = (d*p)*k ∧
      (((d*p)*k : ℕ) : ℝ) < (N : ℝ)^cap := by
  let Q := (N : ℝ)^cap
  have hpData := mem_primeWindow.mp hp
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hsq := negative_prime_square hd hR j hpData.2.2.2
  have hresP : actualDwellSupport (Q/(d : ℝ)) [p] := by
    intro i hi
    have hi0 : i=0 := by simp only [List.length_singleton] at hi; omega
    subst i
    have hsq' : (p : ℝ)^2 ≤ Q/(d : ℝ) :=
      ((lt_div_iff₀ hdR).mpr (by simpa only [mul_comm] using hsq)).le
    simpa using hsq'
  have hbudgetP : ((old.map Prod.fst).prod : ℝ) * (Q/(d : ℝ)) ≤ (N : ℝ)^cap := by
    rw [holdprod]
    have heq : (d : ℝ) * (Q/(d : ℝ)) = Q := by field_simp [hdR.ne']
    exact heq.le
  have hP := append_unselected_same_cap old [p] hfull hselected hresP hbudgetP
  let afterP := appendUnselected old [p]
  have hprodP : (afterP.map Prod.fst).prod = d*p := by
    simpa only [List.prod_singleton,holdprod] using hP.2.2.2
  have hkactive := actualSmallRosserMinus_active hk
  have hksf := actualSmallRosserSupport_squarefree (d*N)
    (Nat.ceil (lowerCutoff Q d)) (lowerCutoff Q d) hkactive.1
  have hkprod : k.primeFactorsList.reverse.prod = k := by
    rw [List.prod_reverse,Nat.prod_primeFactorsList hksf.ne_zero]
  have hwellK := negative_ordinary_residual_well N hd hR j hp hk
  have hdpR : 0 < ((d*p : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hd hpData.1.pos)
  have hbudgetK : ((afterP.map Prod.fst).prod : ℝ) * childLevel Q d p ≤ (N : ℝ)^cap := by
    rw [hprodP]
    have heq : ((d*p : ℕ) : ℝ) * childLevel Q d p = Q := by
      unfold childLevel
      field_simp [hdpR.ne']
    exact heq.le
  have hWhole := append_unselected_same_cap afterP k.primeFactorsList.reverse
    hP.1 hP.2.1 hwellK hbudgetK
  exact ⟨hWhole.1,hWhole.2.1,hWhole.2.2.1.trans hP.2.2.1,
    by simpa only [hprodP,hkprod] using hWhole.2.2.2,
    negative_native_physical_support hd hpData.1 hk⟩

end
end ImbalancedChen.P2OriginalNegativeSingleSameQSupport
