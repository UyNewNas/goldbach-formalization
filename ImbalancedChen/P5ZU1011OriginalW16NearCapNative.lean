import ImbalancedChen.P5ZU1011OriginalW16FixedCellNative
import ImbalancedChen.P5ZU1011NearCapRationalParameters

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Original W16 near-cap rational native family. Eta is selected BEFORE N
and before every prime tuple. The actual W cap lower U and full/extra
gate upper G construct nu=U-min(eta,(U-G)/2), with the same true 64delta
buffers. All small parameters vanish with eta; the fixed residual level
uses the common UPPER prefix. The native row, first-two prime geometry
and full squares are derived without a W density, H248 or AP licence.
No midpoint source is changed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16NearCapNative
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open P5U1011JointOverlap P2OriginalFourthCapProducerInterface
open U1011OriginalW16FixedCellNative (G G_lt_capLower half_le_G fullUpper_le_G extraUpper_le_G lastUpper_eq_Tplus Tplus)

def nu (B : Box) (eta : ℚ) : ℚ := NearCapRationalParameters.level (G B) (capLower wPolicy B) eta
def delta (B : Box) (eta : ℚ) : ℚ := NearCapRationalParameters.delta (G B) (capLower wPolicy B) eta
def xi (B : Box) (eta : ℚ) : ℚ := NearCapRationalParameters.xi (G B) (capLower wPolicy B) eta (B.lo 3)
def rho (B : Box) (eta : ℚ) : ℚ := NearCapRationalParameters.rho (G B) (capLower wPolicy B) eta
def residualExponent (B : Box) (eta : ℚ) : ℚ := nu B eta-Tplus B-20*delta B eta
def cutoffExponent (B : Box) (eta : ℚ) : ℚ := min (B.lo 3-xi B eta) (residualExponent B eta/(2+rho B eta))
def Z (B : Box) (eta : ℚ) (N : ℕ) : ℝ := (N:ℝ)^(cutoffExponent B eta:ℝ)
def D (B : Box) (eta : ℚ) (N : ℕ) : ℝ := (N:ℝ)^(residualExponent B eta:ℝ)
def support (B : Box) (eta : ℚ) (N : ℕ) : Finset ℕ := actualSmallRosserSupport N (Nat.ceil (Z B eta N)) (Z B eta N)
def coefficient (B : Box) (eta : ℚ) (N d : ℕ) : ℝ := actualSmallRosserPlus N (Nat.ceil (Z B eta N)) (Z B eta N) (D B eta N) d
def main (B : Box) (eta : ℚ) (N : ℕ) (t : Four) : ℝ := U11LoweredRosser.mainTerm N t (Z B eta N) (D B eta N)
def signedAP (B : Box) (eta : ℚ) (N : ℕ) (t : Four) : ℝ := U11LoweredRosser.signedAP N t (Z B eta N) (D B eta N)
def signedCentre (B : Box) (eta : ℚ) (N : ℕ) (t : Four) : ℝ := U11LoweredRosser.signedCentre N t (Z B eta N) (D B eta N)
theorem rational_parameters (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) :
    G B<nu B eta ∧ nu B eta<capLower wPolicy B ∧ 0<delta B eta ∧ 0<xi B eta ∧
      0<rho B eta ∧ 0<residualExponent B eta ∧ 0<cutoffExponent B eta := by
  have hgc := G_lt_capLower B htest
  have hgn : G B<nu B eta := NearCapRationalParameters.gate_lt_level hgc
  have hnc : nu B eta<capLower wPolicy B := NearCapRationalParameters.level_lt_cap hgc heta
  have hd : 0<delta B eta := lt_min (by norm_num)
    (lt_min (div_pos (sub_pos.mpr hgn) (by norm_num))
      (div_pos (sub_pos.mpr hnc) (by norm_num)))
  have hx : 0<xi B eta := lt_min (div_pos hpositive (by norm_num)) hd
  have hdle : delta B eta≤(nu B eta-G B)/64 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hlast := fullUpper_le_G B (3:Fin 4)
  rw [lastUpper_eq_Tplus] at hlast
  have hhi : 0<B.hi 3 := hpositive.trans_le (hvalid 3)
  have hre : 0<residualExponent B eta := by unfold residualExponent; linarith
  have hsmall : 0<B.lo 3-xi B eta := by
    have hxi : xi B eta≤B.lo 3/2 := min_le_left _ _
    linarith
  have hcut : 0<cutoffExponent B eta :=
    lt_min hsmall (div_pos hre (by change 0<2+delta B eta; linarith))
  exact ⟨hgn,hnc,hd,hx,hd,hre,hcut⟩

/-- All four full-square gates and W's A(x) gate have the same reserve;
the independent x<mu gate is retained literally. -/
theorem whole_box_margins (B : Box) (eta : ℚ) (heta : 0<eta) (htest : wholeBoxEligibleTest wPolicy B=true)
    {v : LogFour} (hv : v∈B.region) :
    (1/2:ℝ)<(nu B eta:ℝ) ∧ (delta B eta:ℝ)≤3/4096 ∧
      (nu B eta:ℝ)+64*(delta B eta:ℝ)≤cap wPolicy v ∧
      (∀ j : Fin 4,fullSquare j v+64*(delta B eta:ℝ)≤(nu B eta:ℝ)) ∧
      (1+v 0)/2+64*(delta B eta:ℝ)≤(nu B eta:ℝ) ∧ v 0<(25/128:ℝ) := by
  have hgc := G_lt_capLower B htest
  have hhQ := half_le_G B
  have hnuQ : (1/2:ℚ)<nu B eta := hhQ.trans_lt (NearCapRationalParameters.gate_lt_level hgc)
  have hd0Q : delta B eta≤(3/4096:ℚ) := min_le_left _ _
  have hd1Q : delta B eta≤(nu B eta-G B)/64 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hd2Q : delta B eta≤(capLower wPolicy B-nu B eta)/64 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hd1 : (delta B eta:ℝ)≤((nu B eta:ℝ)-(G B:ℝ))/64 := by exact_mod_cast hd1Q
  have hd2 : (delta B eta:ℝ)≤((capLower wPolicy B:ℝ)-(nu B eta:ℝ))/64 := by exact_mod_cast hd2Q
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
theorem W_fixed_critical (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) {v : LogFour} (hv : v∈B.region)
    (hz : 0≤v 2) (hyx : v 1≤v 0) :
    (1/2:ℝ)<(nu B eta:ℝ) ∧ (nu B eta:ℝ)<5/8 ∧
      v 0≤2*(nu B eta:ℝ)-1-(delta B eta:ℝ) ∧
      2*v 1≤1-(nu B eta:ℝ)-2*(delta B eta:ℝ) ∧
      v 2<(51/32:ℝ)-(8/3:ℝ)*(nu B eta:ℝ) ∧
      v 2+(2*(nu B eta:ℝ)-1)+(delta B eta:ℝ)≤actualSelectedSubproductUpper 1 (nu B eta:ℝ) := by
  have hm := whole_box_margins B eta heta htest hv
  have hdQ := (rational_parameters B eta heta hvalid hpositive htest).2.2.1
  have hd : (0:ℝ)<(delta B eta:ℝ) := by exact_mod_cast hdQ
  have hcap := hm.2.2.1
  rw [U1011OriginalW16NativeInitialization.W_cap] at hcap
  have hΛ : (nu B eta:ℝ)≤153/256 := by linarith
  have hB : 153/256-(3/8:ℝ)*v 2≤(66-34*v 2)/107 := by linarith
  refine ⟨hm.1,by linarith,by linarith [hm.2.2.2.2.1],?_,by linarith,?_⟩
  · linarith [hm.2.1,hm.2.2.2.2.2]
  · unfold actualSelectedSubproductUpper
    apply le_min <;> linarith

/-- Literal natural prime inputs for the repaired W initialization,
uniform for all source tuples lying in the certified box. -/
theorem native_W_critical {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    (slots t 0:ℝ)≤(N:ℝ)^(2*(nu B eta:ℝ)-1-(delta B eta:ℝ)) ∧
      (slots t 1:ℝ)^2≤(N:ℝ)^(1-(nu B eta:ℝ)-2*(delta B eta:ℝ)) ∧
      (slots t 2:ℝ)<(N:ℝ)^((51/32:ℝ)-(8/3:ℝ)*(nu B eta:ℝ)) ∧
      (slots t 2:ℝ)≤(N:ℝ)^(actualSelectedSubproductUpper 1 (nu B eta:ℝ)-
        (2*(nu B eta:ℝ)-1)-(delta B eta:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hz := (U1011OriginalW16NativeInitialization.coordinate_pos hN ht 2).le
  have hyx : coordinates N t 1≤coordinates N t 0 :=
    (coordinates_strictAnti hN ht).antitone (by norm_num : (0:Fin 4)≤1)
  have hc := W_fixed_critical B eta heta hvalid hpositive htest hbox hz hyx
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
    (ht : t∈jointSelector N E) (B : Box) (eta : ℚ) (heta : 0<eta) (htest : wholeBoxEligibleTest wPolicy B=true)
    (hbox : coordinates N t∈B.region) (j : Fin 4) :
    (prefixProduct j t:ℝ)*(slots t j:ℝ)^2≤(N:ℝ)^((nu B eta:ℝ)-64*(delta B eta:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hm := (whole_box_margins B eta heta htest hbox).2.2.2.1 j
  rw [←fullSquare_rpow hN ht j]
  exact Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)

private theorem source_joint {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) : t∈jointSelector N E :=
  originalU11_mem_joint (by exact_mod_cast (Nat.le_of_lt hN)) ht

theorem native_legality {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    0<Z B eta N ∧ 1<D B eta N ∧ Z B eta N≤(t.1.1:ℝ) ∧ Z B eta N≤D B eta N := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hpar := rational_parameters B eta heta hvalid hpositive htest
  have hre : (0:ℝ)<(residualExponent B eta:ℝ) := by exact_mod_cast hpar.2.2.2.2.2.1
  have hrho : (0:ℝ)<(rho B eta:ℝ) := by exact_mod_cast hpar.2.2.2.2.1
  have hcutle : (cutoffExponent B eta:ℝ)≤(residualExponent B eta:ℝ) := by
    have hq : (residualExponent B eta:ℝ)/(2+(rho B eta:ℝ))≤(residualExponent B eta:ℝ) := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    have hminQ : cutoffExponent B eta≤residualExponent B eta/(2+rho B eta) := min_le_right _ _
    have hminR : (cutoffExponent B eta:ℝ)≤(residualExponent B eta:ℝ)/(2+(rho B eta:ℝ)) := by
      exact_mod_cast hminQ
    exact hminR.trans hq
  have hfirst : Z B eta N≤(t.1.1:ℝ) := by
    have hx : (0:ℝ)≤(xi B eta:ℝ) := by exact_mod_cast hpar.2.2.2.1.le
    have hc : (cutoffExponent B eta:ℝ)≤(B.lo 3:ℝ) := by
      have h : cutoffExponent B eta≤B.lo 3-xi B eta := min_le_left _ _
      have h' : (cutoffExponent B eta:ℝ)≤(B.lo 3:ℝ)-(xi B eta:ℝ) := by exact_mod_cast h
      linarith
    have hpow := slot_rpow hN (source_joint hN ht) (3:Fin 4)
    have h := Real.rpow_le_rpow_of_exponent_le hn.le (hc.trans (hbox.1 3))
    simpa only [Z,slots,Matrix.cons_val_three] using h.trans_eq hpow
  exact ⟨Real.rpow_pos_of_pos hp _,Real.one_lt_rpow hn hre,hfirst,
    Real.rpow_le_rpow_of_exponent_le hn.le hcutle⟩

/-- Coefficient activity supplies the literal residual-support bound;
the upper prefix makes the entire fixed family obey one full modulus cap. -/
theorem active_full_modulus_cap {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hbox : coordinates N t∈B.region)
    (hactive : coefficient B eta N d≠0) :
    (d:ℝ)<D B eta N ∧ ((fullPrefix t*d:ℕ):ℝ)<(N:ℝ)^((nu B eta:ℝ)-20*(delta B eta:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hsum : U11SelectedLargest.prefixSum (coordinates N t)≤(Tplus B:ℝ) := by
    simp only [U11SelectedLargest.prefixSum,Tplus,Rat.cast_add]
    linarith [hbox.2 0,hbox.2 1,hbox.2 2,hbox.2 3]
  have hb : (fullPrefix t:ℝ)≤(N:ℝ)^(Tplus B:ℝ) := by
    rw [←fullPrefix_rpow hN (source_joint hN ht)]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hsum
  have hd : (d:ℝ)<D B eta N := (actualSmallRosserPlus_active hactive).2.1
  refine ⟨hd,?_⟩
  rw [Nat.cast_mul]
  calc
    (fullPrefix t:ℝ)*d≤(N:ℝ)^(Tplus B:ℝ)*d := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)
    _ < (N:ℝ)^(Tplus B:ℝ)*D B eta N := mul_lt_mul_of_pos_left hd (Real.rpow_pos_of_pos hp _)
    _ = _ := by
      rw [D,←Real.rpow_add hp]
      congr 1
      simp only [residualExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
      ring

theorem native_row_upper {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region) :
    U11Adaptive.weight N t≤main B eta N t+signedAP B eta N t-signedCentre B eta N t := by
  have hleg := native_legality hN ht B eta heta hvalid hpositive htest hbox
  exact U11LoweredRosser.row_upper (by exact_mod_cast (Nat.le_of_lt hN)) ht
    (Z B eta N) (D B eta N) hleg.2.2.1 hleg.2.1 hleg.2.2.2

/-- Summation preserves one fixed original coefficient. Neither a
uniform family estimate nor a density upper bound has been assumed. -/
theorem fixed_family_upper {N : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop)
    (T : Finset Four) (hT : T⊆U11Adaptive.source N E) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest wPolicy B=true)
    (hbox : ∀t∈T,coordinates N t∈B.region) :
    (∑t∈T,U11Adaptive.weight N t)≤
      (∑t∈T,main B eta N t)+(∑t∈T,signedAP B eta N t)-∑t∈T,signedCentre B eta N t := by
  rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  exact native_row_upper hN (hT ht) B eta heta hvalid hpositive htest (hbox t ht)

/-- Quantitative precision of the physical level and ALL small native
parameters. This is a native-parameter statement, not a density or H248
kernel comparison. -/
theorem precision_parameters (B : Box) (eta : ℚ) (heta : 0<eta)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest wPolicy B=true) :
    (0<capLower wPolicy B-nu B eta ∧ capLower wPolicy B-nu B eta≤eta) ∧
      (0<delta B eta ∧ delta B eta≤eta/64) ∧
      (0<xi B eta ∧ xi B eta≤eta/64) ∧ (0<rho B eta ∧ rho B eta≤eta/64) := by
  have hp := rational_parameters B eta heta hvalid hpositive htest
  have he := NearCapRationalParameters.level_error (G_lt_capLower B htest) heta
  have hsmall := NearCapRationalParameters.small_parameter_bounds (G B) (capLower wPolicy B) eta (B.lo 3)
  exact ⟨he,⟨hp.2.2.1,NearCapRationalParameters.delta_le_eta _ _ _⟩,
    ⟨hp.2.2.2.1,hsmall.2⟩,⟨hp.2.2.2.2.1,hsmall.1⟩⟩

/-- Explicit epsilon modulus for nu -> U as eta -> 0 from above. The
SAME eta also controls delta, xi and rho, before N and every tuple. -/
theorem precision_modulus (B : Box) (eta epsilon : ℚ) (heta : 0<eta)
    (hsmall : eta<epsilon) (htest : wholeBoxEligibleTest wPolicy B=true) :
    |nu B eta-capLower wPolicy B|<epsilon ∧
      delta B eta<epsilon/64 ∧ xi B eta<epsilon/64 ∧ rho B eta<epsilon/64 := by
  have he := NearCapRationalParameters.level_error (G_lt_capLower B htest) heta
  have hd := NearCapRationalParameters.delta_le_eta (G B) (capLower wPolicy B) eta
  have hs := NearCapRationalParameters.small_parameter_bounds (G B) (capLower wPolicy B) eta (B.lo 3)
  refine ⟨?_,by change NearCapRationalParameters.delta _ _ _<_; linarith,
    by change NearCapRationalParameters.xi _ _ _ _<_; linarith,
    by change NearCapRationalParameters.rho _ _ _<_; linarith⟩
  change |NearCapRationalParameters.level (G B) (capLower wPolicy B) eta-capLower wPolicy B|<epsilon
  rw [abs_sub_comm,abs_of_pos he.1]
  exact he.2.trans_lt hsmall

/-- Primitive immutable cell data only. No support, factorization,
monomial, row, density or count conclusion is stored as a premise. -/
structure NativeData where
  B : Box
  hvalid : B.Valid
  hpositive : 0<B.lo 3
  htest : wholeBoxEligibleTest wPolicy B=true
  eta : ℚ
  heta : 0<eta

def NativeData.nu (d : NativeData) : ℚ := nu d.B d.eta
def NativeData.delta (d : NativeData) : ℚ := delta d.B d.eta
def NativeData.xi (d : NativeData) : ℚ := xi d.B d.eta
def NativeData.rho (d : NativeData) : ℚ := rho d.B d.eta
def NativeData.Z (d : NativeData) (N : ℕ) : ℝ := Z d.B d.eta N
def NativeData.D (d : NativeData) (N : ℕ) : ℝ := D d.B d.eta N
def NativeData.support (d : NativeData) (N : ℕ) : Finset ℕ := support d.B d.eta N
def NativeData.coefficient (d : NativeData) (N e : ℕ) : ℝ := coefficient d.B d.eta N e

theorem NativeData.row_upper (d : NativeData) {N : ℕ} (hN : 1<N)
    {E : ℕ×ℕ → Prop} {t : Four} (ht : t∈U11Adaptive.source N E)
    (hbox : coordinates N t∈d.B.region) :
    U11Adaptive.weight N t≤main d.B d.eta N t+signedAP d.B d.eta N t-signedCentre d.B d.eta N t :=
  native_row_upper hN ht d.B d.eta d.heta d.hvalid d.hpositive d.htest hbox

end
end ImbalancedChen.P5Z.U1011OriginalW16NearCapNative

