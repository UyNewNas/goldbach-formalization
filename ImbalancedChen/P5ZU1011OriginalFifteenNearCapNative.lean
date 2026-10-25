import ImbalancedChen.P5ZU1011OriginalFifteenFixedCellNative
import ImbalancedChen.P5ZU1011NearCapRationalParameters

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual original15 ordinary native families with rational near-cap precision
eta chosen BEFORE N and every tuple. Existing actual whole-box upper gates
G and cap lower U give nu=U-min(eta,(U-G)/2); all64-unit buffers and smaller
xi/rho are inherited from the proved rational constructor. The actual Z,D,
support and rho are NEW precision-dependent native objects, not the old
midpoint coefficient under a new name.

Every legality, buffered raw square, critical interval and same-rho finite
count/main/AP/centre statement follows from primitive valid positive box,
concrete WholeBoxTest=true and eta>0. W and ALL16 residual/profile error
geometry are separately owned. No density/mean/AP/table licence is supplied.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenNearCapNative

noncomputable section
open scoped BigOperators Topology
open Classical Filter Set
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalSixteenInteriorArithmetic P5U1011JointOverlap
open P2OriginalFourthCapProducerInterface
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

def G (p : Policy) (B : Box) : ℚ := U1011OriginalFifteenFixedCellNative.G p B
def U (p : Policy) (B : Box) : ℚ := capLower p B
def nu (p : Policy) (B : Box) (eta : ℚ) : ℚ := NearCapRationalParameters.level (G p B) (U p B) eta
def delta (p : Policy) (B : Box) (eta : ℚ) : ℚ := NearCapRationalParameters.delta (G p B) (U p B) eta
def xi (p : Policy) (B : Box) (eta : ℚ) : ℚ := NearCapRationalParameters.xi (G p B) (U p B) eta (B.lo 3)
def rho (p : Policy) (B : Box) (eta : ℚ) : ℚ := NearCapRationalParameters.rho (G p B) (U p B) eta
def Tplus (B : Box) : ℚ := U1011OriginalFifteenFixedCellNative.Tplus B
def residualExponent (p : Policy) (B : Box) (eta : ℚ) : ℚ := nu p B eta-Tplus B-20*delta p B eta
def cutoffExponent (p : Policy) (B : Box) (eta : ℚ) : ℚ :=
  min (B.lo 3-xi p B eta) (residualExponent p B eta/(2+rho p B eta))
def Z (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) : ℝ := (N:ℝ)^(cutoffExponent p B eta:ℝ)
def D (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) : ℝ := (N:ℝ)^(residualExponent p B eta:ℝ)
def support (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) : Finset ℕ :=
  actualSmallRosserSupport N (Nat.ceil (Z p B eta N)) (Z p B eta N)
def coefficient (p : Policy) (B : Box) (eta : ℚ) (N d : ℕ) : ℝ :=
  actualSmallRosserPlus N (Nat.ceil (Z p B eta N)) (Z p B eta N) (D p B eta N) d

/-- Only primitive finite certificate data enter this native constructor;
N and arithmetic tuples are deliberately absent from the structure. -/
structure NativeData where
  policy : Policy
  isMask : policy.val<15
  box : Box
  valid : box.Valid
  positive : 0<box.lo 3
  test : wholeBoxEligibleTest policy box=true
  eta : ℚ
  eta_pos : 0<eta

theorem gate_cap_gap (p : Policy) (hp : p.val<15) (B : Box)
    (htest : wholeBoxEligibleTest p B=true) : G p B<U p B :=
  U1011OriginalFifteenFixedCellNative.G_lt_capLower p hp B htest

theorem precision_bounds (p : Policy) (hp : p.val<15) (B : Box)
    (htest : wholeBoxEligibleTest p B=true) {eta : ℚ} (heta : 0<eta) (hw : 0<B.lo 3) :
    G p B<nu p B eta ∧ nu p B eta<U p B ∧
      0<U p B-nu p B eta ∧ U p B-nu p B eta≤eta ∧
      0<delta p B eta ∧ 0<xi p B eta ∧ 0<rho p B eta ∧
      delta p B eta≤eta/64 ∧ xi p B eta≤eta/64 ∧ rho p B eta≤eta/64 := by
  have hgap := gate_cap_gap p hp B htest
  have he := NearCapRationalParameters.level_error hgap heta
  have hs := NearCapRationalParameters.small_parameter_bounds (G p B) (U p B) eta (B.lo 3)
  exact ⟨NearCapRationalParameters.gate_lt_level hgap,NearCapRationalParameters.level_lt_cap hgap heta,
    he.1,he.2,NearCapRationalParameters.delta_pos hgap heta,
    NearCapRationalParameters.xi_pos hgap heta hw,NearCapRationalParameters.delta_pos hgap heta,
    NearCapRationalParameters.delta_le_eta _ _ _,hs.2,hs.1⟩

private theorem full_le_G (p : Policy) (B : Box) (j : Fin 4) : (fullSquarePiece j).upper B.lo B.hi≤G p B := by
  apply Finset.le_max'
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)))
private theorem selected_le_G (p : Policy) (B : Box) (j : Fin 4) (hj : ¬Selected p j) :
    (selectedSquarePiece p j).upper B.lo B.hi≤G p B := by
  apply Finset.le_max'
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩)))

theorem parameter_positivity (p : Policy) (hp : p.val<15) (B : Box) (hv : B.Valid)
    (hw : 0<B.lo 3) (htest : wholeBoxEligibleTest p B=true) {eta : ℚ} (heta : 0<eta) :
    0<delta p B eta ∧ 0<xi p B eta ∧ 0<rho p B eta ∧
      0<residualExponent p B eta ∧ 0<cutoffExponent p B eta := by
  have hgap := gate_cap_gap p hp B htest
  have hd := NearCapRationalParameters.delta_pos hgap heta
  have hx := NearCapRationalParameters.xi_pos hgap heta hw
  have hlast := full_le_G p B (3:Fin 4)
  rw [U1011OriginalFifteenFixedCellNative.lastUpper_eq_Tplus] at hlast
  have hGlower : Tplus B+B.lo 3≤G p B := by change U1011OriginalFifteenFixedCellNative.Tplus B+B.lo 3≤G p B; linarith [hv 3]
  have hlower := NearCapRationalParameters.residual_lower (G p B) (U p B) eta (Tplus B) (B.lo 3) hGlower
  have hlower' : B.lo 3+44*delta p B eta≤residualExponent p B eta := hlower
  have hre : 0<residualExponent p B eta := by linarith
  have hsmall : 0<B.lo 3-xi p B eta := by
    have h := NearCapRationalParameters.xi_le_half (G p B) (U p B) eta (B.lo 3)
    change xi p B eta≤B.lo 3/2 at h
    linarith
  have hrho : 0<rho p B eta := hd
  exact ⟨hd,hx,hrho,hre,lt_min hsmall (div_pos hre (by linarith))⟩

/-- Every point of the same closed cell uses the same near-cap nu and
64buffer reserve. Its20buffer square gates remain strict. -/
theorem whole_box_native_margins (p : Policy) (hp : p.val<15) (B : Box)
    (htest : wholeBoxEligibleTest p B=true) {eta : ℚ} (heta : 0<eta)
    {v : LogFour} (hv : v∈B.region) :
    (nu p B eta:ℝ)<cap p v ∧
      (∀ j:Fin 4,fullSquare j v+20*(delta p B eta:ℝ)<(nu p B eta:ℝ)) ∧
      (∀ j:Fin 4,¬Selected p j→selectedSquare p j v+20*(delta p B eta:ℝ)<(nu p B eta:ℝ)) := by
  have hgap := gate_cap_gap p hp B htest
  have hnQ := NearCapRationalParameters.level_lt_cap hgap heta
  have hn : (nu p B eta:ℝ)<(U p B:ℝ) := by exact_mod_cast hnQ
  have hdQ := NearCapRationalParameters.delta_pos hgap heta
  have hd : (0:ℝ)<(delta p B eta:ℝ) := by exact_mod_cast hdQ
  have hbQ := NearCapRationalParameters.gate_buffer (G p B) (U p B) eta
  have hb : (G p B:ℝ)+64*(delta p B eta:ℝ)≤(nu p B eta:ℝ) := by exact_mod_cast hbQ
  refine ⟨hn.trans_le (cap_bounds p B hv).1,?_,?_⟩
  · intro j
    have hs := (fullSquarePiece j).eval_le_upper B.lo B.hi v hv.1 hv.2
    rw [fullSquarePiece_eval] at hs
    have hg : ((fullSquarePiece j).upper B.lo B.hi:ℝ)≤(G p B:ℝ) := by exact_mod_cast full_le_G p B j
    linarith
  · intro j hj
    have hs := (selectedSquarePiece p j).eval_le_upper B.lo B.hi v hv.1 hv.2
    rw [selectedSquarePiece_eval] at hs
    have hg : ((selectedSquarePiece p j).upper B.lo B.hi:ℝ)≤(G p B:ℝ) := by exact_mod_cast selected_le_G p B j hj
    linarith

private theorem source_joint {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) : t∈jointSelector N E := originalU11_mem_joint (by exact_mod_cast (Nat.le_of_lt hN)) ht

theorem native_legality {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (A : NativeData) (hbox : coordinates N t∈A.box.region) :
    0<Z A.policy A.box A.eta N ∧ 1<D A.policy A.box A.eta N ∧
      Z A.policy A.box A.eta N≤(t.1.1:ℝ) ∧ Z A.policy A.box A.eta N≤D A.policy A.box A.eta N := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := zero_lt_one.trans hn
  have hpar := parameter_positivity A.policy A.isMask A.box A.valid A.positive A.test A.eta_pos
  have hr : (0:ℝ)<(residualExponent A.policy A.box A.eta:ℝ) := by exact_mod_cast hpar.2.2.2.1
  have hp : (0:ℝ)<(rho A.policy A.box A.eta:ℝ) := by exact_mod_cast hpar.2.2.1
  have hcle : (cutoffExponent A.policy A.box A.eta:ℝ)≤(residualExponent A.policy A.box A.eta:ℝ) := by
    have hq : (residualExponent A.policy A.box A.eta:ℝ)/(2+(rho A.policy A.box A.eta:ℝ))≤(residualExponent A.policy A.box A.eta:ℝ) := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    have hmQ : cutoffExponent A.policy A.box A.eta≤residualExponent A.policy A.box A.eta/(2+rho A.policy A.box A.eta) := min_le_right _ _
    have hmR : (cutoffExponent A.policy A.box A.eta:ℝ)≤(residualExponent A.policy A.box A.eta:ℝ)/(2+(rho A.policy A.box A.eta:ℝ)) := by exact_mod_cast hmQ
    exact hmR.trans hq
  have hfirst : Z A.policy A.box A.eta N≤(t.1.1:ℝ) := by
    have hx : (0:ℝ)≤(xi A.policy A.box A.eta:ℝ) := by exact_mod_cast hpar.2.1.le
    have hcQ : cutoffExponent A.policy A.box A.eta≤A.box.lo 3-xi A.policy A.box A.eta := min_le_left _ _
    have hcR : (cutoffExponent A.policy A.box A.eta:ℝ)≤(A.box.lo 3:ℝ)-(xi A.policy A.box A.eta:ℝ) := by exact_mod_cast hcQ
    have hc : (cutoffExponent A.policy A.box A.eta:ℝ)≤coordinates N t 3 := by linarith [hbox.1 3]
    have h := Real.rpow_le_rpow_of_exponent_le hn.le hc
    simpa only [Z,slots,Matrix.cons_val_three] using h.trans_eq (slot_rpow hN (source_joint hN ht) 3)
  exact ⟨Real.rpow_pos_of_pos hn0 _,Real.one_lt_rpow hn hr,hfirst,Real.rpow_le_rpow_of_exponent_le hn.le hcle⟩

theorem native_critical_and_squares {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (A : NativeData) (hbox : coordinates N t∈A.box.region) :
    ((N:ℝ)^(2*(nu A.policy A.box A.eta:ℝ)-1)<(selectedProduct A.policy t:ℝ) ∧
      (selectedProduct A.policy t:ℝ)<(N:ℝ)^((19/32:ℝ)-(2/3:ℝ)*(nu A.policy A.box A.eta:ℝ))) ∧
    (∀ j:Fin 4,(prefixProduct j t:ℝ)*(slots t j:ℝ)^2<(N:ℝ)^((nu A.policy A.box A.eta:ℝ)-20*(delta A.policy A.box A.eta:ℝ))) ∧
    (∀ j:Fin 4,¬Selected A.policy j→(selectedProduct A.policy t:ℝ)*(earlierRemainderProduct A.policy j t:ℝ)*(slots t j:ℝ)^2<
      (N:ℝ)^((nu A.policy A.box A.eta:ℝ)-20*(delta A.policy A.box A.eta:ℝ))) := by
  have hm := whole_box_native_margins A.policy A.isMask A.box A.test A.eta_pos hbox
  have hjoint := source_joint hN ht
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  refine ⟨actual_selected_critical_interval hN hjoint A.policy A.isMask hm.1,?_,?_⟩
  · intro j
    rw [←fullSquare_rpow hN hjoint j]
    exact Real.rpow_lt_rpow_of_exponent_lt hn (by linarith [hm.2.1 j])
  · intro j hj
    rw [←selectedSquare_rpow hN hjoint A.policy j]
    exact Real.rpow_lt_rpow_of_exponent_lt hn (by linarith [hm.2.2 j hj])

theorem active_full_modulus_cap {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (A : NativeData) (hbox : coordinates N t∈A.box.region)
    (hd : coefficient A.policy A.box A.eta N d≠0) :
    ((fullPrefix t*d:ℕ):ℝ)<(N:ℝ)^((nu A.policy A.box A.eta:ℝ)-20*(delta A.policy A.box A.eta:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := zero_lt_one.trans hn
  have hs : U11SelectedLargest.prefixSum (coordinates N t)≤(Tplus A.box:ℝ) := by
    simp only [U11SelectedLargest.prefixSum,Tplus,U1011OriginalFifteenFixedCellNative.Tplus,Rat.cast_add]
    linarith [hbox.2 0,hbox.2 1,hbox.2 2,hbox.2 3]
  have hb : (fullPrefix t:ℝ)≤(N:ℝ)^(Tplus A.box:ℝ) := by
    rw [←fullPrefix_rpow hN (source_joint hN ht)]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hs
  have hactive : (d:ℝ)<D A.policy A.box A.eta N := (actualSmallRosserPlus_active hd).2.1
  rw [Nat.cast_mul]
  calc
    (fullPrefix t:ℝ)*d≤(N:ℝ)^(Tplus A.box:ℝ)*d := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)
    _ < (N:ℝ)^(Tplus A.box:ℝ)*D A.policy A.box A.eta N := mul_lt_mul_of_pos_left hactive (Real.rpow_pos_of_pos hn0 _)
    _ = _ := by
      rw [D,←Real.rpow_add hn0]
      congr 1
      simp only [residualExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
      ring

def main (A : NativeData) (N : ℕ) (t : Four) : ℝ := trueLogarithmicIntegral N/(Nat.totient (fullPrefix t):ℝ)*
  actualSmallRosserPlusDensity N (Nat.ceil (Z A.policy A.box A.eta N)) (Z A.policy A.box A.eta N) (D A.policy A.box A.eta N)
def signedAP (A : NativeData) (N : ℕ) (t : Four) : ℝ := ∑ d∈support A.policy A.box A.eta N,coefficient A.policy A.box A.eta N d*
  chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (fullPrefix t*d)
def signedCentre (A : NativeData) (N : ℕ) (t : Four) : ℝ := ∑ d∈support A.policy A.box A.eta N,coefficient A.policy A.box A.eta N d*
  chenCentrePrimeAPCount N N (fullPrefix t*d)
def estimator (A : NativeData) (N : ℕ) (t : Four) : ℝ := ∑ d∈support A.policy A.box A.eta N,coefficient A.policy A.box A.eta N d*
  (chenPrimeAPCount N N (fullPrefix t*d)-chenCentrePrimeAPCount N N (fullPrefix t*d))

theorem estimator_same_coefficient {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (A : NativeData) (hbox : coordinates N t∈A.box.region) :
    estimator A N t=main A N t+signedAP A N t-signedCentre A N t := by
  have hl := native_legality hN ht A hbox
  have hz : Z A.policy A.box A.eta N≤(slots t 3:ℝ) := by simpa only [slots,Matrix.cons_val_three] using hl.2.2.1
  have hcop := fullPrefix_coprime_lowered_sieve (source_joint hN ht) hz
  exact currentChen_quotient_actualRosser_plus_main_and_errors N (fullPrefix t) (Nat.ceil (Z A.policy A.box A.eta N))
    (Z A.policy A.box A.eta N) (D A.policy A.box A.eta N) (Nat.le_ceil _) hcop

theorem native_row_upper {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (A : NativeData) (hbox : coordinates N t∈A.box.region) :
    U11Adaptive.weight N t≤main A N t+signedAP A N t-signedCentre A N t := by
  have hl := native_legality hN ht A hbox
  have h12 := (U11LoweredRosser.original_carrier_order (by exact_mod_cast (Nat.le_of_lt hN)) ht).2.2.2.2.1
  have hz2 : Z A.policy A.box A.eta N≤(t.1.2:ℝ) := hl.2.2.1.trans (by exact_mod_cast h12.le)
  have hweight : U11Adaptive.weight N t=((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2:ℝ)).card:ℝ) := by
    rw [fullPrefix_eq_multiplier]
    rfl
  have hcount : U11Adaptive.weight N t≤((chenSiftedQuotientPrimeSource N (fullPrefix t) (Z A.policy A.box A.eta N)).card:ℝ) := by
    rw [hweight]
    exact_mod_cast Finset.card_le_card (U11LoweredRosser.siftedSource_subset_lowered N _ _ _ hz2)
  exact (hcount.trans (currentChen_quotient_actualRosser_upper N (fullPrefix t) (Nat.ceil (Z A.policy A.box A.eta N))
    (Z A.policy A.box A.eta N) (D A.policy A.box A.eta N) (Nat.le_ceil _) hl.2.1 hl.2.2.2)).trans_eq
      (estimator_same_coefficient hN ht A hbox)

theorem native_family_upper {N : ℕ} (hN : 1<N) (E : ℕ×ℕ→Prop) (T : Finset Four)
    (hT : T⊆U11Adaptive.source N E) (A : NativeData) (hbox : ∀t∈T,coordinates N t∈A.box.region) :
    (∑t∈T,U11Adaptive.weight N t)≤(∑t∈T,main A N t)+(∑t∈T,signedAP A N t)-∑t∈T,signedCentre A N t := by
  rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun t ht=>native_row_upper hN (hT ht) A (hbox t ht))

theorem nu_at_zero (p : Policy) (hp : p.val<15) (B : Box) (htest : wholeBoxEligibleTest p B=true) : nu p B 0=U p B := by
  have hgap := gate_cap_gap p hp B htest
  change U p B-min 0 ((U p B-G p B)/2)=U p B
  rw [min_eq_left (by linarith),sub_zero]

theorem delta_at_zero (p : Policy) (hp : p.val<15) (B : Box) (htest : wholeBoxEligibleTest p B=true) : delta p B 0=0 := by
  have hgap := gate_cap_gap p hp B htest
  change min (3/4096:ℚ) (min ((nu p B 0-G p B)/64) ((U p B-nu p B 0)/64))=0
  rw [nu_at_zero p hp B htest,sub_self,zero_div,min_eq_right (by linarith),min_eq_right (by norm_num)]

theorem tendsto_precision_parameters (p : Policy) (hp : p.val<15) (B : Box)
    (htest : wholeBoxEligibleTest p B=true) (hw : 0<B.lo 3) :
    Tendsto (nu p B) (𝓝[>] (0:ℚ)) (𝓝 (U p B)) ∧ Tendsto (delta p B) (𝓝[>] (0:ℚ)) (𝓝 0) ∧
      Tendsto (xi p B) (𝓝[>] (0:ℚ)) (𝓝 0) ∧ Tendsto (rho p B) (𝓝[>] (0:ℚ)) (𝓝 0) := by
  have hn : Continuous (nu p B) := by unfold nu NearCapRationalParameters.level NearCapRationalParameters.capLoss; fun_prop
  have hd : Continuous (delta p B) := by unfold delta NearCapRationalParameters.delta NearCapRationalParameters.level NearCapRationalParameters.capLoss; fun_prop
  have hx : Continuous (xi p B) := by unfold xi NearCapRationalParameters.xi NearCapRationalParameters.delta NearCapRationalParameters.level NearCapRationalParameters.capLoss; fun_prop
  have hz : xi p B 0=0 := by
    change min (B.lo 3/2) (delta p B 0)=0
    rw [delta_at_zero p hp B htest,min_eq_right (by linarith)]
  have hnlim : Tendsto (nu p B) (𝓝 (0:ℚ)) (𝓝 (nu p B 0)) := hn.continuousAt
  have hdlim : Tendsto (delta p B) (𝓝 (0:ℚ)) (𝓝 (delta p B 0)) := hd.continuousAt
  have hxlim : Tendsto (xi p B) (𝓝 (0:ℚ)) (𝓝 (xi p B 0)) := hx.continuousAt
  rw [nu_at_zero p hp B htest] at hnlim
  rw [delta_at_zero p hp B htest] at hdlim
  rw [hz] at hxlim
  exact ⟨hnlim.mono_left nhdsWithin_le_nhds,hdlim.mono_left nhdsWithin_le_nhds,
    hxlim.mono_left nhdsWithin_le_nhds,hdlim.mono_left nhdsWithin_le_nhds⟩

end
end ImbalancedChen.P5Z.U1011OriginalFifteenNearCapNative
