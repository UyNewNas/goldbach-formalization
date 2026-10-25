import ImbalancedChen.P5ZU1011OriginalW16NearCapNative
import ImbalancedChen.P5ZU1011OriginalW16AttachedWellSupport

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Physical input support for one FIXED original W16 box family. The common
residual level is frozen at the box UPPER prefix. Four specified prime
squares are proved at that same level; primitive residual well support is
then attached without replacing the level by a pointwise midpoint. The
original first-two initialization is verified with these fixed parameters.
No desired full-vector support or uniform family estimate is an input.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16NearCapSupport
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalW16NearCapNative
open U1011OriginalW16FixedCellNative (Tplus)
open U1011OriginalW16NativeInitialization (firstThree)
open U1011OriginalW16AttachedWellSupport (specified specified_product)
open P5U1011JointOverlap
open Part3.ActualWThreeCapacityRun
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
open scoped BigOperators

def runLevel (B : Box) (eta : ℚ) (N : ℕ) : ℝ := (N:ℝ)^((nu B eta:ℝ)-2*(delta B eta:ℝ))
def middleCapacity (B : Box) (eta : ℚ) (N : ℕ) : ℝ := (N:ℝ)^(2*(nu B eta:ℝ)-1)
def rightCapacity (B : Box) (eta : ℚ) (N : ℕ) (A : ℝ) : ℝ :=
  (N:ℝ)^(1-(nu B eta:ℝ)-2*(delta B eta:ℝ))/A

theorem specified_well_support {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    actualDwellSupport (runLevel B eta N) (specified t) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hdQ := (rational_parameters B eta heta hvalid hpositive htest).2.2.1
  have hd : (0:ℝ)<(delta B eta:ℝ) := by exact_mod_cast hdQ
  have hs : ∀j:Fin 4,(prefixProduct j t:ℝ)*(slots t j:ℝ)^2≤runLevel B eta N := by
    intro j
    exact (native_full_squares hN ht B eta heta htest hbox j).trans
      (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [runLevel]; linarith))
  intro i hi
  have hi4 : i<4 := by simpa only [specified,List.length_cons,List.length_nil] using hi
  interval_cases i
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using hs 0
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using hs 1
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using hs 2
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using hs 3

/-- The actual prefix is allowed to move inside the box; the residual
level is not. Its common UPPER prefix still pays all later squares. -/
theorem prefix_residual_budget {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    ((specified t).prod:ℝ)*D B eta N≤(N:ℝ)^((nu B eta:ℝ)-20*(delta B eta:ℝ)) ∧
      ((specified t).prod:ℝ)*D B eta N≤runLevel B eta N := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hdQ := (rational_parameters B eta heta hvalid hpositive htest).2.2.1
  have hd : (0:ℝ)<(delta B eta:ℝ) := by exact_mod_cast hdQ
  have hsum : U11SelectedLargest.prefixSum (coordinates N t)≤(Tplus B:ℝ) := by
    simp only [U11SelectedLargest.prefixSum,Tplus,Rat.cast_add]
    linarith [hbox.2 0,hbox.2 1,hbox.2 2,hbox.2 3]
  have hb : ((specified t).prod:ℝ)≤(N:ℝ)^(Tplus B:ℝ) := by
    rw [specified_product,←fullPrefix_rpow hN ht]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hsum
  have hbudget : ((specified t).prod:ℝ)*D B eta N≤(N:ℝ)^((nu B eta:ℝ)-20*(delta B eta:ℝ)) := by
    calc
      _ ≤ (N:ℝ)^(Tplus B:ℝ)*D B eta N :=
        mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hp.le _)
      _ = _ := by
        rw [D,←Real.rpow_add hp]
        congr 1
        simp only [residualExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
        ring
  exact ⟨hbudget,hbudget.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [runLevel]; linarith))⟩

/-- The primitive residual well vector is promoted to the full original
four-prime vector, at one box-fixed level. In particular this is not a
full-prefix support premise passed to the W completion theorem. -/
theorem attached_well_support {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region)
    (tail : List ℕ) (hresidual : actualDwellSupport (D B eta N) tail) :
    actualDwellSupport (runLevel B eta N) (specified t++tail) := by
  have hf := specified_well_support hN ht B eta heta hvalid hpositive htest hbox
  have hbudget := (prefix_residual_budget hN ht B eta heta hvalid hpositive htest hbox).2
  revert hresidual
  induction tail using List.reverseRecOn with
  | nil => intro hr; simpa using hf
  | append_singleton tail q ih =>
    intro hr
    obtain ⟨htail,hlast⟩ :=
      (prefixSquareBound_append_singleton_iff (fun n:ℕ => (n:ℝ)) (D B eta N) tail q).1 hr
    rw [←List.append_assoc]
    apply (prefixSquareBound_append_singleton_iff (fun n:ℕ => (n:ℝ))
      (runLevel B eta N) (specified t++tail) q).2
    refine ⟨ih htail,?_⟩
    have hmul := mul_le_mul_of_nonneg_left hlast (Nat.cast_nonneg (specified t).prod : (0:ℝ)≤(specified t).prod)
    calc
      _ = ((specified t).prod:ℝ)*((tail.map (fun n:ℕ => (n:ℝ))).prod*(q:ℝ)^2) := by
        rw [List.map_append,List.prod_append,actualNatList_cast_prod]
        ring
      _ ≤ ((specified t).prod:ℝ)*D B eta N := hmul
      _ ≤ runLevel B eta N := hbudget

/-- Original W first-two initialization with fixed box capacities. The
third and fourth specified primes stay unread in their original order. -/
theorem fixed_initialization {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) :
    1≤middleCapacity B eta N ∧ 1≤rightCapacity B eta N A ∧
      A*middleCapacity B eta N*rightCapacity B eta N A=runLevel B eta N ∧
      total (fun n:ℕ => (n:ℝ)) (initialBins A (firstThree t))=(slots t 0:ℝ)*slots t 1 ∧
      Bounded (fun n:ℕ => (n:ℝ)) A (middleCapacity B eta N) (rightCapacity B eta N A)
        (initialBins A (firstThree t)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hApos : 0<A := zero_lt_one.trans_le hA
  have hm := whole_box_margins B eta heta htest hbox
  have hz := (U1011OriginalW16NativeInitialization.coordinate_pos hN ht 2).le
  have hcap := hm.2.2.1
  rw [U1011OriginalW16NativeInitialization.W_cap] at hcap
  have hnu : (nu B eta:ℝ)≤153/256 := by linarith
  let P := (N:ℝ)^(1-(nu B eta:ℝ)-2*(delta B eta:ℝ))
  have hP : A≤P := hAupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by
    dsimp [P]
    linarith [hm.2.1]))
  have hC : 1≤rightCapacity B eta N A := (le_div_iff₀ hApos).2 (by simpa [rightCapacity,P] using hP)
  have hAC : A*rightCapacity B eta N A=P := by
    dsimp [rightCapacity,P]
    field_simp [hApos.ne'] <;> ring
  have hc := native_W_critical hN ht B eta heta hvalid hpositive htest hbox
  have hs : actualDwellSupport (A*rightCapacity B eta N A) [slots t 1] := by
    intro i hi
    have hi0 : i=0 := by simp only [List.length_singleton] at hi; omega
    subst i
    simpa only [hAC,List.take_zero,List.map_nil,List.prod_nil,List.getElem_cons_zero,one_mul,P] using hc.2.1
  obtain ⟨hprod,hleft,hright⟩ := actualTwoCapacityFactors_correct hA hC [slots t 1] hs
  have hdQ := (rational_parameters B eta heta hvalid hpositive htest).2.2.1
  have hd : (0:ℝ)<(delta B eta:ℝ) := by exact_mod_cast hdQ
  have hB : 1≤middleCapacity B eta N := Real.one_le_rpow hn.le (by dsimp [middleCapacity]; linarith [hm.1])
  have hfirst : (slots t 0:ℝ)≤middleCapacity B eta N := hc.1.trans
    (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [middleCapacity]; linarith))
  refine ⟨hB,hC,?_,?_,?_,?_,?_⟩
  · calc
      A*middleCapacity B eta N*rightCapacity B eta N A=middleCapacity B eta N*P := by rw [←hAC]; ring
      _ = runLevel B eta N := by
        dsimp [middleCapacity,P,runLevel]
        rw [←Real.rpow_add hp]
        congr 1
        ring
  · have hh := initialBins_product A (firstThree t) hA hC (by simpa [firstThree] using hs)
    simpa [wp,firstThree] using hh
  · simpa [initialBins,firstThree,wp,actualTwoCapacityFactors,actualNatList_cast_prod] using hleft
  · simpa [initialBins,firstThree,wp] using hfirst
  · simpa [initialBins,firstThree,wp,actualTwoCapacityFactors,actualNatList_cast_prod] using hright

end
end ImbalancedChen.P5Z.U1011OriginalW16NearCapSupport

