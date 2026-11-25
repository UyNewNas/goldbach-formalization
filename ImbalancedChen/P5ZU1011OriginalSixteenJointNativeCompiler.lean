import ImbalancedChen.P5ZU1011OriginalFifteenJointNativeRows
import ImbalancedChen.P5ZU1011OriginalW16JointNative

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The STATIC sixteen-policy native plan on the literal JOINT U10/U11 source.
The low fourth-prime band has no E mask; the high band has the original E
complement. All row parameters are the existing fixed rational box plan,
chosen before N and tuple. This extends the actual finite carrier and its
physical legality, rather than asserting that low tuples belong to U11.
The original p2 quotient cutoff is lowered to Z<=p1 before coprimality.
Tag0 retains its actual joint count. Density/table/AP/PP licenses remain OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenJointNativeCompiler
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalSixteenInteriorArithmetic
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler P5U1011JointOverlap
open U1011OriginalFifteenJointNativeRows (joint_coordinates_cube joint_count_identity)

def ordinaryTuples (n N : ℕ) (E : ℕ×ℕ→Prop) : Finset Four :=
  (jointSelector N E).filter (fun t=>tupleTag n N t≠0)

def fallbackTuples (n N : ℕ) (E : ℕ×ℕ→Prop) : Finset Four :=
  (jointSelector N E).filter (fun t=>tupleTag n N t=0)

/-- One policy per geometric cell, with source membership still literal. -/
def selectedCellTuples (n N : ℕ) (E : ℕ×ℕ→Prop) (j : Grid n) : Finset Four :=
  (ordinaryTuples n N E).filter (fun t=>owner n (coordinates N t)=j)

theorem selectedCellTuples_unique {n N : ℕ} {E : ℕ×ℕ→Prop} {j k : Grid n} {t : Four}
    (hj : t∈selectedCellTuples n N E j) (hk : t∈selectedCellTuples n N E k) : j=k :=
  (Finset.mem_filter.mp hj).2.symm.trans (Finset.mem_filter.mp hk).2

theorem selectedCellTuples_geometry {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop}
    {j : Grid n} {t : Four} (ht : t∈selectedCellTuples n N E j) : coordinates N t∈cell n j := by
  obtain ⟨ht,ho⟩ := Finset.mem_filter.mp ht
  have hg := owner_mem n (joint_coordinates_cube hN (Finset.mem_filter.mp ht).1)
  rwa [ho] at hg

theorem selectedCellTuples_static {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop}
    {j : Grid n} {t : Four} (ht : t∈selectedCellTuples n N E j) :
    selectedPolicy n N t=boxPolicy (gridBox n j) ∧
      support n N t=rowSupport (boxPolicy (gridBox n j)) (gridBox n j) N ∧
      ∀d,coefficient n N t d=rowCoefficient (boxPolicy (gridBox n j)) (gridBox n j) N d :=
  compiled_row_static_on_cell n N (selectedCellTuples_geometry hN ht)

theorem exact_cell_reindex (n N : ℕ) (E : ℕ×ℕ→Prop) (F : Four→ℝ) :
    (∑t∈ordinaryTuples n N E,F t)=∑j : Grid n,∑t∈selectedCellTuples n N E j,F t := by
  have h := Finset.sum_fiberwise_of_maps_to (s:=ordinaryTuples n N E)
    (t:=(Finset.univ : Finset (Grid n))) (g:=fun t=>owner n (coordinates N t))
    (fun _ _=>Finset.mem_univ _) F
  exact h.symm

theorem joint_row_legality {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (B : Box) (hv : B.Valid) (hw : 0<B.lo 3)
    (hc : wholeBoxEligibleTest p B=true) (hb : coordinates N t∈B.region) :
    0<rowZ p B N ∧ 1<rowD p B N ∧ rowZ p B N≤(t.1.1:ℝ) ∧ rowZ p B N≤rowD p B N := by
  by_cases hp : p.val<15
  · simpa only [rowZ,rowD,if_pos hp] using
      U1011OriginalFifteenJointNativeRows.joint_native_legality hN ht p hp B hv hw hc hb
  · have heq : p=wPolicy := by apply Fin.ext; have h:=p.isLt; change p.val=15; omega
    subst p
    simpa only [rowZ,rowD,wPolicy,show ¬(15:ℕ)<15 by omega,if_false] using
      U1011OriginalW16JointNative.midpoint_legality hN ht B hv hw hc hb

/-- The coefficient's literal residual level, common to the two genuine
native branches. No source assumption is needed for this identity. -/
theorem rowD_exact (p : Policy) (B : Box) (N : ℕ) :
    rowD p B N=(N:ℝ)^((rowNu p B:ℝ)-(U1011OriginalFifteenFixedCellNative.Tplus B:ℝ)-20*(rowDelta p B:ℝ)) := by
  by_cases hp : p.val<15
  · simp only [rowD,rowNu,rowDelta,if_pos hp,U1011OriginalFifteenFixedCellNative.D,
      U1011OriginalFifteenFixedCellNative.residualExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
  · simp only [rowD,rowNu,rowDelta,if_neg hp,U1011OriginalW16FixedCellNative.D,
      U1011OriginalW16FixedCellNative.residualExponent,U1011OriginalW16FixedCellNative.Tplus,
      U1011OriginalFifteenFixedCellNative.Tplus,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]

theorem joint_row_active_full_modulus_cap {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop}
    {t : Four} (ht : t∈jointSelector N E) (p : Policy) (B : Box)
    (hb : coordinates N t∈B.region) (hd : rowCoefficient p B N d≠0) :
    ((fullPrefix t*d:ℕ):ℝ)<(N:ℝ)^((rowNu p B:ℝ)-20*(rowDelta p B:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := zero_lt_one.trans hn
  have hs : U11SelectedLargest.prefixSum (coordinates N t)≤(U1011OriginalFifteenFixedCellNative.Tplus B:ℝ) := by
    simp only [U11SelectedLargest.prefixSum,U1011OriginalFifteenFixedCellNative.Tplus,Rat.cast_add]
    linarith [hb.2 0,hb.2 1,hb.2 2,hb.2 3]
  have hbprod : (fullPrefix t:ℝ)≤(N:ℝ)^(U1011OriginalFifteenFixedCellNative.Tplus B:ℝ) := by
    rw [←fullPrefix_rpow hN ht]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hs
  have hdlt : (d:ℝ)<rowD p B N := (actualSmallRosserPlus_active hd).2.1
  rw [Nat.cast_mul]
  calc
    (fullPrefix t:ℝ)*d≤(N:ℝ)^(U1011OriginalFifteenFixedCellNative.Tplus B:ℝ)*d :=
      mul_le_mul_of_nonneg_right hbprod (Nat.cast_nonneg _)
    _ < (N:ℝ)^(U1011OriginalFifteenFixedCellNative.Tplus B:ℝ)*rowD p B N :=
      mul_lt_mul_of_pos_left hdlt (Real.rpow_pos_of_pos hn0 _)
    _ = _ := by rw [rowD_exact,←Real.rpow_add hn0]; congr 1; ring

theorem compiled_legality {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈ordinaryTuples n N E) :
    0<Z n N t ∧ 1<D n N t ∧ Z n N t≤(t.1.1:ℝ) ∧ Z n N t≤D n N t := by
  obtain ⟨hs,hne⟩ := Finset.mem_filter.mp ht
  have hc := (boxPolicy_certificate (ownerBox n N t) hne).2
  have hg := owner_mem n (joint_coordinates_cube hN hs)
  exact joint_row_legality hN hs _ _ (gridBox_valid n _) (gridBox_lower_positive n _ 3)
    hc (cell_subset_closed_box n _ hg)

theorem compiled_estimator_identity {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈ordinaryTuples n N E) : estimator n N t=main n N t+signedAP n N t-signedCentre n N t := by
  have hs := (Finset.mem_filter.mp ht).1
  have hl := compiled_legality hN ht
  have hz : Z n N t≤(slots t 3:ℝ) := by simpa only [slots,Matrix.cons_val_three] using hl.2.2.1
  exact currentChen_quotient_actualRosser_plus_main_and_errors N (fullPrefix t)
    (Nat.ceil (Z n N t)) (Z n N t) (D n N t) (Nat.le_ceil _) (fullPrefix_coprime_lowered_sieve hs hz)

theorem compiled_row_upper {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈ordinaryTuples n N E) : U11Adaptive.weight N t≤main n N t+signedAP n N t-signedCentre n N t := by
  have hs := (Finset.mem_filter.mp ht).1
  have hl := compiled_legality hN ht
  have h12 := (joint_carrier_order hs).2.2.2.2.1
  have hz2 : Z n N t≤(t.1.2:ℝ) := hl.2.2.1.trans (by exact_mod_cast h12.le)
  have hw : U11Adaptive.weight N t=((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2:ℝ)).card:ℝ) := by
    rw [fullPrefix_eq_multiplier]; rfl
  have hcount : U11Adaptive.weight N t≤((chenSiftedQuotientPrimeSource N (fullPrefix t) (Z n N t)).card:ℝ) := by
    rw [hw]
    exact_mod_cast Finset.card_le_card (U11LoweredRosser.siftedSource_subset_lowered N _ _ _ hz2)
  have hu := currentChen_quotient_actualRosser_upper N (fullPrefix t) (Nat.ceil (Z n N t))
    (Z n N t) (D n N t) (Nat.le_ceil _) hl.2.1 hl.2.2.2
  exact (hcount.trans hu).trans_eq (compiled_estimator_identity hN ht)

theorem source_partition (n N : ℕ) (E : ℕ×ℕ→Prop) (F : Four→ℝ) :
    (∑t∈jointSelector N E,F t)=(∑t∈fallbackTuples n N E,F t)+∑t∈ordinaryTuples n N E,F t :=
  (Finset.sum_filter_add_sum_filter_not (jointSelector N E) (fun t=>tupleTag n N t=0) F).symm

theorem original_joint_source_upper {n N : ℕ} (hN : 1<N) (E : ℕ×ℕ→Prop) :
    currentChenUpsilon10 N+currentChenUpsilon11 N E≤(∑t∈fallbackTuples n N E,U11Adaptive.weight N t)+
      ∑t∈ordinaryTuples n N E,main n N t+signedAP n N t-signedCentre n N t := by
  rw [joint_count_identity hN E,source_partition n N E]
  apply add_le_add_left
  exact Finset.sum_le_sum (fun t ht=>compiled_row_upper hN ht)

end
end ImbalancedChen.P5Z.U1011OriginalSixteenJointNativeCompiler
