import ImbalancedChen.P5ZU1011OriginalSixteenBoxCertificates
import ImbalancedChen.P5ZU1011OriginalSixteenArithmeticEligibility
import ImbalancedChen.P5ZU1011OriginalW16NativeInitialization

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The original W16 policy has one decreasing z cap and TWO extra gates.
Here its parameters are rational functions of a certified CLOSED BOX,
chosen before N and before any prime tuple. In particular W is never
treated as an ordinary mask with an empty selected product. The fixed
residual support, coefficient and native upper row use exactly these
parameters. No uniform-family, density, AP or counting estimate is an
input. Analytic distribution and the original W policy licence remain
separate obligations. This does not claim coverage of boxes whose test
is false.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16FixedCellNative

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open P5U1011JointOverlap P2OriginalFourthCapProducerInterface

def gateUpperValues (B : Box) : Finset ℚ :=
  insert (1/2) (insert (wExtraPiece.upper B.lo B.hi)
    (Finset.univ.image (fun j : Fin 4 => (fullSquarePiece j).upper B.lo B.hi)))
theorem gateUpperValues_nonempty (B : Box) : (gateUpperValues B).Nonempty :=
  ⟨1/2,Finset.mem_insert_self _ _⟩
def G (B : Box) : ℚ := (gateUpperValues B).max' (gateUpperValues_nonempty B)
def nu (B : Box) : ℚ := (G B + capLower wPolicy B)/2
def delta (B : Box) : ℚ := min (3/4096)
  (min ((nu B-G B)/64) ((capLower wPolicy B-nu B)/64))
def xi (B : Box) : ℚ := min (B.lo 3/2) (delta B)
def rho (B : Box) : ℚ := delta B
def Tplus (B : Box) : ℚ := B.hi 0+B.hi 1+B.hi 2+B.hi 3
def residualExponent (B : Box) : ℚ := nu B-Tplus B-20*delta B
def cutoffExponent (B : Box) : ℚ :=
  min (B.lo 3-xi B) (residualExponent B/(2+rho B))
def Z (B : Box) (N : ℕ) : ℝ := (N:ℝ)^(cutoffExponent B:ℝ)
def D (B : Box) (N : ℕ) : ℝ := (N:ℝ)^(residualExponent B:ℝ)
def support (B : Box) (N : ℕ) : Finset ℕ :=
  actualSmallRosserSupport N (Nat.ceil (Z B N)) (Z B N)
def coefficient (B : Box) (N d : ℕ) : ℝ :=
  actualSmallRosserPlus N (Nat.ceil (Z B N)) (Z B N) (D B N) d
def main (B : Box) (N : ℕ) (t : Four) : ℝ :=
  U11LoweredRosser.mainTerm N t (Z B N) (D B N)
def signedAP (B : Box) (N : ℕ) (t : Four) : ℝ :=
  U11LoweredRosser.signedAP N t (Z B N) (D B N)
def signedCentre (B : Box) (N : ℕ) (t : Four) : ℝ :=
  U11LoweredRosser.signedCentre N t (Z B N) (D B N)

theorem W_capLower (B : Box) : capLower wPolicy B=153/256-(3/8:ℚ)*B.hi 2 := by
  simp [capLower,wPolicy]

theorem half_le_G (B : Box) : (1/2:ℚ)≤G B :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)
theorem extraUpper_le_G (B : Box) : wExtraPiece.upper B.lo B.hi≤G B := by
  apply Finset.le_max'
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
theorem fullUpper_le_G (B : Box) (j : Fin 4) :
    (fullSquarePiece j).upper B.lo B.hi≤G B := by
  apply Finset.le_max'
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr
    (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))))

theorem G_lt_capLower (B : Box) (htest : wholeBoxEligibleTest wPolicy B=true) :
    G B<capLower wPolicy B := by
  have ht : WholeBoxEligible wPolicy B := of_decide_eq_true htest
  have hw : wExtraPiece.upper B.lo B.hi<capLower wPolicy B ∧ B.hi 0<(25/128:ℚ) := by
    simpa only [wPolicy,show ¬(15:ℕ)<15 by omega,if_false] using ht.2.2
  have hall : ∀ a∈gateUpperValues B,a<capLower wPolicy B := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact ht.1
    · rcases Finset.mem_insert.mp ha with rfl|ha
      · exact hw.1
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
        exact ht.2.1 j
  exact hall _ (Finset.max'_mem _ _)

theorem lastUpper_eq_Tplus (B : Box) :
    (fullSquarePiece 3).upper B.lo B.hi=Tplus B+B.hi 3 := by
  norm_num [fullSquarePiece,Affine.upper,Affine.neg,Affine.lower,Tplus,Fin.sum_univ_succ]
  <;> ring

/-- The residual margin uses the UPPER prefix, not the current point's
prefix. This is what makes one native Rosser level legal for the box. -/
theorem rational_parameters (B : Box) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) :
    G B<nu B ∧ nu B<capLower wPolicy B ∧ 0<delta B ∧ 0<xi B ∧
      0<rho B ∧ 0<residualExponent B ∧ 0<cutoffExponent B := by
  have hgc := G_lt_capLower B htest
  have hgn : G B<nu B := by unfold nu; linarith
  have hnc : nu B<capLower wPolicy B := by unfold nu; linarith
  have hd : 0<delta B := lt_min (by norm_num)
    (lt_min (div_pos (sub_pos.mpr hgn) (by norm_num))
      (div_pos (sub_pos.mpr hnc) (by norm_num)))
  have hx : 0<xi B := lt_min (div_pos hpositive (by norm_num)) hd
  have hdle : delta B≤(nu B-G B)/64 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hlast := fullUpper_le_G B (3:Fin 4)
  rw [lastUpper_eq_Tplus] at hlast
  have hhi : 0<B.hi 3 := hpositive.trans_le (hvalid 3)
  have hre : 0<residualExponent B := by unfold residualExponent; linarith
  have hsmall : 0<B.lo 3-xi B := by
    have hxi : xi B≤B.lo 3/2 := min_le_left _ _
    linarith
  have hcut : 0<cutoffExponent B :=
    lt_min hsmall (div_pos hre (by change 0<2+delta B; linarith))
  exact ⟨hgn,hnc,hd,hx,hd,hre,hcut⟩

/-- All four full-square gates and W's A(x) gate have the same reserve;
the independent x<mu gate is retained literally. -/
theorem whole_box_margins (B : Box) (htest : wholeBoxEligibleTest wPolicy B=true)
    {v : LogFour} (hv : v∈B.region) :
    (1/2:ℝ)<(nu B:ℝ) ∧ (delta B:ℝ)≤3/4096 ∧
      (nu B:ℝ)+64*(delta B:ℝ)≤cap wPolicy v ∧
      (∀ j : Fin 4,fullSquare j v+64*(delta B:ℝ)≤(nu B:ℝ)) ∧
      (1+v 0)/2+64*(delta B:ℝ)≤(nu B:ℝ) ∧ v 0<(25/128:ℝ) := by
  have hgc := G_lt_capLower B htest
  have hhQ := half_le_G B
  have hnuQ : (1/2:ℚ)<nu B := by unfold nu; linarith
  have hd0Q : delta B≤(3/4096:ℚ) := min_le_left _ _
  have hd1Q : delta B≤(nu B-G B)/64 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hd2Q : delta B≤(capLower wPolicy B-nu B)/64 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hd1 : (delta B:ℝ)≤((nu B:ℝ)-(G B:ℝ))/64 := by exact_mod_cast hd1Q
  have hd2 : (delta B:ℝ)≤((capLower wPolicy B:ℝ)-(nu B:ℝ))/64 := by exact_mod_cast hd2Q
  have hcap := (cap_bounds wPolicy B hv).1
  have ht : WholeBoxEligible wPolicy B := of_decide_eq_true htest
  have hw : wExtraPiece.upper B.lo B.hi<capLower wPolicy B ∧ B.hi 0<(25/128:ℚ) := by
    simpa only [wPolicy,show ¬(15:ℕ)<15 by omega,if_false] using ht.2.2
  refine ⟨by exact_mod_cast hnuQ,by exact_mod_cast hd0Q,by linarith,?_,?_,?_⟩
  · intro j
    have hs := (fullSquarePiece j).eval_le_upper B.lo B.hi v hv.1 hv.2
    rw [fullSquarePiece_eval] at hs
    have hg : ((fullSquarePiece j).upper B.lo B.hi:ℝ)≤(G B:ℝ) := by
      exact_mod_cast fullUpper_le_G B j
    linarith
  · have hs := wExtraPiece.eval_le_upper B.lo B.hi v hv.1 hv.2
    rw [wExtraPiece_eval] at hs
    have hg : (wExtraPiece.upper B.lo B.hi:ℝ)≤(G B:ℝ) := by
      exact_mod_cast extraUpper_le_G B
    linarith
  · have hx : (B.hi 0:ℝ)<(25/128:ℝ) := by exact_mod_cast hw.2
    exact (hv.2 0).trans_lt hx

/-- This is W's genuine third-prime critical geometry at a fixed box
level. Both members of the spectral min are paid, before any N. -/
theorem W_fixed_critical (B : Box) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) {v : LogFour} (hv : v∈B.region)
    (hz : 0≤v 2) (hyx : v 1≤v 0) :
    (1/2:ℝ)<(nu B:ℝ) ∧ (nu B:ℝ)<5/8 ∧
      v 0≤2*(nu B:ℝ)-1-(delta B:ℝ) ∧
      2*v 1≤1-(nu B:ℝ)-2*(delta B:ℝ) ∧
      v 2<(51/32:ℝ)-(8/3:ℝ)*(nu B:ℝ) ∧
      v 2+(2*(nu B:ℝ)-1)+(delta B:ℝ)≤actualSelectedSubproductUpper 1 (nu B:ℝ) := by
  have hm := whole_box_margins B htest hv
  have hdQ := (rational_parameters B hvalid hpositive htest).2.2.1
  have hd : (0:ℝ)<(delta B:ℝ) := by exact_mod_cast hdQ
  have hcap := hm.2.2.1
  rw [U1011OriginalW16NativeInitialization.W_cap] at hcap
  have hΛ : (nu B:ℝ)≤153/256 := by linarith
  have hB : 153/256-(3/8:ℝ)*v 2≤(66-34*v 2)/107 := by linarith
  refine ⟨hm.1,by linarith,by linarith [hm.2.2.2.2.1],?_,by linarith,?_⟩
  · linarith [hm.2.1,hm.2.2.2.2.2]
  · unfold actualSelectedSubproductUpper
    apply le_min <;> linarith

/-- Literal natural prime inputs for the repaired W initialization,
uniform for all source tuples lying in the certified box. -/
theorem native_W_critical {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    (slots t 0:ℝ)≤(N:ℝ)^(2*(nu B:ℝ)-1-(delta B:ℝ)) ∧
      (slots t 1:ℝ)^2≤(N:ℝ)^(1-(nu B:ℝ)-2*(delta B:ℝ)) ∧
      (slots t 2:ℝ)<(N:ℝ)^((51/32:ℝ)-(8/3:ℝ)*(nu B:ℝ)) ∧
      (slots t 2:ℝ)≤(N:ℝ)^(actualSelectedSubproductUpper 1 (nu B:ℝ)-
        (2*(nu B:ℝ)-1)-(delta B:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hz := (U1011OriginalW16NativeInitialization.coordinate_pos hN ht 2).le
  have hyx : coordinates N t 1≤coordinates N t 0 :=
    (coordinates_strictAnti hN ht).antitone (by norm_num : (0:Fin 4)≤1)
  have hc := W_fixed_critical B hvalid hpositive htest hbox hz hyx
  have hr := actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht)
  refine ⟨?_,?_,?_,?_⟩
  · rw [←hr 0]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hc.2.2.1
  · rw [←hr 1,←Real.rpow_mul_natCast hp.le]
    exact Real.rpow_le_rpow_of_exponent_le hn.le (by simpa only [Nat.cast_ofNat] using hc.2.2.2.1)
  · rw [←hr 2]
    exact Real.rpow_lt_rpow_of_exponent_lt hn hc.2.2.2.2.1
  · rw [←hr 2]
    exact Real.rpow_le_rpow_of_exponent_le hn.le (by linarith [hc.2.2.2.2.2])

theorem native_full_squares {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (htest : wholeBoxEligibleTest wPolicy B=true)
    (hbox : coordinates N t∈B.region) (j : Fin 4) :
    (prefixProduct j t:ℝ)*(slots t j:ℝ)^2≤(N:ℝ)^((nu B:ℝ)-64*(delta B:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hm := (whole_box_margins B htest hbox).2.2.2.1 j
  rw [←fullSquare_rpow hN ht j]
  exact Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)

private theorem source_joint {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) : t∈jointSelector N E :=
  originalU11_mem_joint (by exact_mod_cast (Nat.le_of_lt hN)) ht

theorem native_legality {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (B : Box) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    0<Z B N ∧ 1<D B N ∧ Z B N≤(t.1.1:ℝ) ∧ Z B N≤D B N := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hpar := rational_parameters B hvalid hpositive htest
  have hre : (0:ℝ)<(residualExponent B:ℝ) := by exact_mod_cast hpar.2.2.2.2.2.1
  have hrho : (0:ℝ)<(rho B:ℝ) := by exact_mod_cast hpar.2.2.2.2.1
  have hcutle : (cutoffExponent B:ℝ)≤(residualExponent B:ℝ) := by
    have hq : (residualExponent B:ℝ)/(2+(rho B:ℝ))≤(residualExponent B:ℝ) := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    have hminQ : cutoffExponent B≤residualExponent B/(2+rho B) := min_le_right _ _
    have hminR : (cutoffExponent B:ℝ)≤(residualExponent B:ℝ)/(2+(rho B:ℝ)) := by
      exact_mod_cast hminQ
    exact hminR.trans hq
  have hfirst : Z B N≤(t.1.1:ℝ) := by
    have hx : (0:ℝ)≤(xi B:ℝ) := by exact_mod_cast hpar.2.2.2.1.le
    have hc : (cutoffExponent B:ℝ)≤(B.lo 3:ℝ) := by
      have h : cutoffExponent B≤B.lo 3-xi B := min_le_left _ _
      have h' : (cutoffExponent B:ℝ)≤(B.lo 3:ℝ)-(xi B:ℝ) := by exact_mod_cast h
      linarith
    have hpow := slot_rpow hN (source_joint hN ht) (3:Fin 4)
    have h := Real.rpow_le_rpow_of_exponent_le hn.le (hc.trans (hbox.1 3))
    simpa only [Z,slots,Matrix.cons_val_three] using h.trans_eq hpow
  exact ⟨Real.rpow_pos_of_pos hp _,Real.one_lt_rpow hn hre,hfirst,
    Real.rpow_le_rpow_of_exponent_le hn.le hcutle⟩

/-- Coefficient activity supplies the literal residual-support bound;
the upper prefix makes the entire fixed family obey one full modulus cap. -/
theorem active_full_modulus_cap {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (B : Box) (hbox : coordinates N t∈B.region)
    (hactive : coefficient B N d≠0) :
    (d:ℝ)<D B N ∧ ((fullPrefix t*d:ℕ):ℝ)<(N:ℝ)^((nu B:ℝ)-20*(delta B:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hsum : U11SelectedLargest.prefixSum (coordinates N t)≤(Tplus B:ℝ) := by
    simp only [U11SelectedLargest.prefixSum,Tplus,Rat.cast_add]
    linarith [hbox.2 0,hbox.2 1,hbox.2 2,hbox.2 3]
  have hb : (fullPrefix t:ℝ)≤(N:ℝ)^(Tplus B:ℝ) := by
    rw [←fullPrefix_rpow hN (source_joint hN ht)]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hsum
  have hd : (d:ℝ)<D B N := (actualSmallRosserPlus_active hactive).2.1
  refine ⟨hd,?_⟩
  rw [Nat.cast_mul]
  calc
    (fullPrefix t:ℝ)*d≤(N:ℝ)^(Tplus B:ℝ)*d := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)
    _ < (N:ℝ)^(Tplus B:ℝ)*D B N := mul_lt_mul_of_pos_left hd (Real.rpow_pos_of_pos hp _)
    _ = _ := by
      rw [D,←Real.rpow_add hp]
      congr 1
      simp only [residualExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
      ring

theorem native_row_upper {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (B : Box) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    U11Adaptive.weight N t≤main B N t+signedAP B N t-signedCentre B N t := by
  have hleg := native_legality hN ht B hvalid hpositive htest hbox
  exact U11LoweredRosser.row_upper (by exact_mod_cast (Nat.le_of_lt hN)) ht
    (Z B N) (D B N) hleg.2.2.1 hleg.2.1 hleg.2.2.2

/-- Summation preserves one fixed original coefficient. Neither a
uniform family estimate nor a density upper bound has been assumed. -/
theorem fixed_family_upper {N : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop)
    (T : Finset Four) (hT : T⊆U11Adaptive.source N E) (B : Box)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest wPolicy B=true)
    (hbox : ∀t∈T,coordinates N t∈B.region) :
    (∑t∈T,U11Adaptive.weight N t)≤
      (∑t∈T,main B N t)+(∑t∈T,signedAP B N t)-∑t∈T,signedCentre B N t := by
  rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  exact native_row_upper hN (hT ht) B hvalid hpositive htest (hbox t ht)

end
end ImbalancedChen.P5Z.U1011OriginalW16FixedCellNative
