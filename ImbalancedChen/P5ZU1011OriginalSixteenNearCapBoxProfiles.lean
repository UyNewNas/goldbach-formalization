import ImbalancedChen.P5ZU1011NearCapRationalParameters
import ImbalancedChen.P5ZU1011OriginalFifteenFixedCellNative
import ImbalancedChen.P5ZU1011OriginalW16FixedCellNative
import ImbalancedChen.P5ZU1011OriginalSixteenOscillation
import ImbalancedChen.P5ZU1011BufferedOrdinaryClamp

/-!
Actual all16 fixed rational near-cap box profiles. G is the ORIGINAL15
native gate maximum or the distinct original W16 gate maximum. The new
precision eta uses the genuine near-cap rational parameter circuit.
Every parameter is fixed by policy, box and eta before N or any tuple.

The real source point supplies only its actual cap and prefix. Their
endpoint errors give tau>=0 and tau<=5/2 times the L1 box diameter plus
21eta/16. Effective xi is the actual coordinate minus the fixed lower
cutoff wall. The exact native residual/cutoff ratio is the real buffered
physicalQuery. This is a parameter/profile dictionary, not a source count,
AP estimate, H248 licence or density conclusion.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenNearCapBoxProfiles

open Set
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenOscillation
open U1011OriginalSixteenPolicyBank.BoxCertificates
open P2OriginalFourthCapProducerInterface
open scoped BigOperators

noncomputable section

def G (p : Policy) (B : Box) : ℚ :=
  if p.val<15 then U1011OriginalFifteenFixedCellNative.G p B else U1011OriginalW16FixedCellNative.G B

def Tplus (B : Box) : ℚ := U1011OriginalFifteenFixedCellNative.Tplus B

def nu (p : Policy) (B : Box) (eta : ℚ) : ℚ :=
  NearCapRationalParameters.level (G p B) (capLower p B) eta

def delta (p : Policy) (B : Box) (eta : ℚ) : ℚ :=
  NearCapRationalParameters.delta (G p B) (capLower p B) eta

def xi (p : Policy) (B : Box) (eta : ℚ) : ℚ :=
  NearCapRationalParameters.xi (G p B) (capLower p B) eta (B.lo 3)

def rho (p : Policy) (B : Box) (eta : ℚ) : ℚ :=
  NearCapRationalParameters.rho (G p B) (capLower p B) eta

def physicalResidual (p : Policy) (B : Box) (eta : ℚ) : ℚ := nu p B eta-Tplus B-20*delta p B eta

def cutoffExponent (p : Policy) (B : Box) (eta : ℚ) : ℚ :=
  min (B.lo 3-xi p B eta) (physicalResidual p B eta/(2+rho p B eta))

/-- `diameterQ` is the sum of the four coordinate widths. Thus a box
with each coordinate width<=h has diameter<=4h. -/
def diameterQ (B : Box) : ℚ := ∑ i : Fin 4,B.hi i-B.lo i

def diameter (B : Box) : ℝ := (diameterQ B:ℝ)

theorem diameterQ_nonneg (B : Box) (hvalid : B.Valid) : 0≤diameterQ B :=
  Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hvalid i))

theorem coordinateWidth_le_diameterQ (B : Box) (hvalid : B.Valid) (j : Fin 4) :
    B.hi j-B.lo j≤diameterQ B :=
  Finset.single_le_sum (fun i _=>sub_nonneg.mpr (hvalid i)) (Finset.mem_univ j)

theorem diameter_nonneg (B : Box) (hvalid : B.Valid) : 0≤diameter B := by
  change (0:ℝ)≤(diameterQ B:ℝ)
  exact_mod_cast diameterQ_nonneg B hvalid

theorem G_lt_capLower (p : Policy) (B : Box) (htest : wholeBoxEligibleTest p B=true) :
    G p B<capLower p B := by
  by_cases hp : p.val<15
  · simpa only [G,if_pos hp] using U1011OriginalFifteenFixedCellNative.G_lt_capLower p hp B htest
  · have hpW : p=wPolicy := by apply Fin.ext;have hp16:=p.isLt;dsimp [wPolicy];omega
    unfold G
    rw [if_neg hp]
    rw [hpW] at htest ⊢
    exact U1011OriginalW16FixedCellNative.G_lt_capLower B htest

theorem half_le_G (p : Policy) (B : Box) : (1/2:ℚ)≤G p B := by
  by_cases hp : p.val<15
  · simp only [G,if_pos hp,U1011OriginalFifteenFixedCellNative.G]
    exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · simpa only [G,if_neg hp] using U1011OriginalW16FixedCellNative.half_le_G B

theorem fullUpper_le_G (p : Policy) (B : Box) (j : Fin 4) :
    (fullSquarePiece j).upper B.lo B.hi≤G p B := by
  by_cases hp : p.val<15
  · simp only [G,if_pos hp,U1011OriginalFifteenFixedCellNative.G]
    apply Finset.le_max'
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)))
  · simpa only [G,if_neg hp] using U1011OriginalW16FixedCellNative.fullUpper_le_G B j

theorem selectedUpper_le_G (p : Policy) (hp : p.val<15) (B : Box) (j : Fin 4)
    (hj : ¬Selected p j) : (selectedSquarePiece p j).upper B.lo B.hi≤G p B := by
  simp only [G,if_pos hp,U1011OriginalFifteenFixedCellNative.G]
  apply Finset.le_max'
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩)))

theorem W_extraUpper_le_G (B : Box) : wExtraPiece.upper B.lo B.hi≤G wPolicy B := by
  simpa only [G,wPolicy,show ¬(15:ℕ)<15 by omega,if_false] using
    U1011OriginalW16FixedCellNative.extraUpper_le_G B

theorem lastUpper_eq_Tplus (B : Box) : (fullSquarePiece 3).upper B.lo B.hi=Tplus B+B.hi 3 :=
  U1011OriginalFifteenFixedCellNative.lastUpper_eq_Tplus B

theorem Tplus_eq_sum (B : Box) : Tplus B=∑ i : Fin 4,B.hi i := by
  simp [Tplus,U1011OriginalFifteenFixedCellNative.Tplus,Fin.sum_univ_succ]
  <;> ring

private theorem selected_width_bounds (p : Policy) (B : Box) (hvalid : B.Valid) :
    0≤selectedMassQ p B.hi-selectedMassQ p B.lo ∧
      selectedMassQ p B.hi-selectedMassQ p B.lo≤diameterQ B := by
  unfold selectedMassQ
  rw [←Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro i _
    by_cases hi : Selected p i
    · simpa only [if_pos hi] using sub_nonneg.mpr (hvalid i)
    · simp only [if_neg hi,sub_self,le_refl]
  · apply Finset.sum_le_sum
    intro i _
    by_cases hi : Selected p i
    · simp only [if_pos hi]
      exact le_rfl
    · simp only [if_neg hi,sub_self]
      exact sub_nonneg.mpr (hvalid i)

/-- Actual separate cap endpoints, including crossed selected tent
branches and the distinct W reversed-z branch, have this true diameter bound. -/
theorem capWidth_le (p : Policy) (B : Box) (hvalid : B.Valid) :
    capUpper p B-capLower p B≤(3/2:ℚ)*diameterQ B := by
  have hd:=diameterQ_nonneg B hvalid
  have hm:=selected_width_bounds p B hvalid
  by_cases hp : p.val<15
  · have hA : |(1+selectedMassQ p B.hi)/2-(1+selectedMassQ p B.lo)/2|≤(3/2:ℚ)*diameterQ B := by
      rw [show (1+selectedMassQ p B.hi)/2-(1+selectedMassQ p B.lo)/2=
        (1/2:ℚ)*(selectedMassQ p B.hi-selectedMassQ p B.lo) by ring,abs_mul,abs_of_nonneg hm.1]
      norm_num <;> nlinarith
    have hC : |(57/64-(3/2:ℚ)*selectedMassQ p B.lo)-(57/64-(3/2:ℚ)*selectedMassQ p B.hi)|≤
        (3/2:ℚ)*diameterQ B := by
      rw [show (57/64-(3/2:ℚ)*selectedMassQ p B.lo)-(57/64-(3/2:ℚ)*selectedMassQ p B.hi)=
        (3/2:ℚ)*(selectedMassQ p B.hi-selectedMassQ p B.lo) by ring,abs_mul,abs_of_nonneg hm.1]
      norm_num <;> nlinarith
    simp only [capUpper,capLower,if_pos hp]
    exact (le_abs_self _).trans ((abs_min_sub_min_le_max _ _ _ _).trans (max_le hA hC))
  · have hw:=coordinateWidth_le_diameterQ B hvalid 2
    simp only [capUpper,capLower,if_neg hp]
    nlinarith [sub_nonneg.mpr (hvalid 2)]

/-- Genuine fixed rational physical positivity from the actual last full
square. Every parameter is chosen before N and all source points. -/
theorem rational_parameters (p : Policy) (B : Box) (eta : ℚ)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest p B=true)
    (heta : 0<eta) :
    G p B<nu p B eta ∧ nu p B eta<capLower p B ∧ 0<delta p B eta ∧
      0<xi p B eta ∧ 0<rho p B eta ∧ 0<physicalResidual p B eta ∧ 0<cutoffExponent p B eta := by
  have hGU:=G_lt_capLower p B htest
  have hgn : G p B<nu p B eta:=NearCapRationalParameters.gate_lt_level hGU
  have hnc : nu p B eta<capLower p B:=NearCapRationalParameters.level_lt_cap hGU heta
  have hd : 0<delta p B eta:=NearCapRationalParameters.delta_pos hGU heta
  have hx : 0<xi p B eta:=NearCapRationalParameters.xi_pos hGU heta hpositive
  have hrho : 0<rho p B eta:=hd
  have hlast:=fullUpper_le_G p B (3:Fin 4)
  rw [lastUpper_eq_Tplus] at hlast
  have hG : Tplus B+B.lo 3≤G p B:=by linarith [hvalid 3]
  have hR:=NearCapRationalParameters.residual_lower (G p B) (capLower p B) eta (Tplus B) (B.lo 3) hG
  change B.lo 3+44*delta p B eta≤physicalResidual p B eta at hR
  have hRpos : 0<physicalResidual p B eta:=by linarith
  have hxhalf : xi p B eta≤B.lo 3/2:=NearCapRationalParameters.xi_le_half _ _ _ _
  have hsmall : 0<B.lo 3-xi p B eta:=by linarith
  have hcut : 0<cutoffExponent p B eta:=lt_min hsmall (div_pos hRpos (by linarith))
  exact ⟨hgn,hnc,hd,hx,hrho,hRpos,hcut⟩

theorem small_parameter_bounds (p : Policy) (B : Box) (eta : ℚ) :
    rho p B eta≤eta/64 ∧ xi p B eta≤eta/64 :=
  NearCapRationalParameters.small_parameter_bounds _ _ _ _

/-- All actual full/selected/W gates share the near-cap64-unit reserve.
This is fixed-box geometry, without a count or distribution conclusion. -/
theorem whole_box_nearcap_margins (p : Policy) (B : Box) (eta : ℚ)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest p B=true)
    (heta : 0<eta) (v : LogFour) (hv : v∈B.region) :
    (1/2:ℝ)<(nu p B eta:ℝ) ∧ (delta p B eta:ℝ)≤3/4096 ∧
      (nu p B eta:ℝ)+64*(delta p B eta:ℝ)≤cap p v ∧
      (∀ j : Fin 4,fullSquare j v+64*(delta p B eta:ℝ)≤(nu p B eta:ℝ)) ∧
      (if p.val<15 then ∀ j : Fin 4,¬Selected p j →
        selectedSquare p j v+64*(delta p B eta:ℝ)≤(nu p B eta:ℝ)
      else (1+v 0)/2+64*(delta p B eta:ℝ)≤(nu p B eta:ℝ) ∧ v 0<(25/128:ℝ)) := by
  have hpars:=rational_parameters p B eta hvalid hpositive htest heta
  have hhQ : (1/2:ℚ)<nu p B eta:=lt_of_le_of_lt (half_le_G p B) hpars.1
  have hdQ : delta p B eta≤(3/4096:ℚ):=NearCapRationalParameters.delta_le_cap _ _ _
  have hgQ : G p B+64*delta p B eta≤nu p B eta:=NearCapRationalParameters.gate_buffer _ _ _
  have hcQ : nu p B eta+64*delta p B eta≤capLower p B:=NearCapRationalParameters.cap_buffer _ _ _
  have hg : (G p B:ℝ)+64*(delta p B eta:ℝ)≤(nu p B eta:ℝ):=by exact_mod_cast hgQ
  have hc : (nu p B eta:ℝ)+64*(delta p B eta:ℝ)≤(capLower p B:ℝ):=by exact_mod_cast hcQ
  refine ⟨by exact_mod_cast hhQ,by exact_mod_cast hdQ,hc.trans (cap_bounds p B hv).1,?_,?_⟩
  · intro j
    have hs:=(fullSquarePiece j).eval_le_upper B.lo B.hi v hv.1 hv.2
    rw [fullSquarePiece_eval] at hs
    have hG : ((fullSquarePiece j).upper B.lo B.hi:ℝ)≤(G p B:ℝ):=by exact_mod_cast fullUpper_le_G p B j
    linarith
  · by_cases hp : p.val<15
    · simp only [if_pos hp]
      intro j hj
      have hs:=(selectedSquarePiece p j).eval_le_upper B.lo B.hi v hv.1 hv.2
      rw [selectedSquarePiece_eval] at hs
      have hG : ((selectedSquarePiece p j).upper B.lo B.hi:ℝ)≤(G p B:ℝ):=by
        exact_mod_cast selectedUpper_le_G p hp B j hj
      linarith
    · simp only [if_neg hp]
      have hpW : p=wPolicy := by apply Fin.ext;have hp16:=p.isLt;dsimp [wPolicy];omega
      have hs:=wExtraPiece.eval_le_upper B.lo B.hi v hv.1 hv.2
      rw [wExtraPiece_eval] at hs
      have hGQ : wExtraPiece.upper B.lo B.hi≤G p B:=by rw [hpW];exact W_extraUpper_le_G B
      have hG : (wExtraPiece.upper B.lo B.hi:ℝ)≤(G p B:ℝ):=by exact_mod_cast hGQ
      have ht : WholeBoxEligible p B:=of_decide_eq_true htest
      have hExtras : wExtraPiece.upper B.lo B.hi<capLower p B ∧ B.hi 0<(25/128:ℚ):=by
        simpa only [if_neg hp] using ht.2.2
      have hXQ : B.hi 0<(25/128:ℚ):=hExtras.2
      have hX : (B.hi 0:ℝ)<(25/128:ℝ):=by exact_mod_cast hXQ
      exact ⟨by linarith,(hv.2 0).trans_lt hX⟩

theorem prefix_error (B : Box) (v : LogFour) (hv : v∈B.region) :
    0≤(Tplus B:ℝ)-U11SelectedLargest.prefixSum v ∧
      (Tplus B:ℝ)-U11SelectedLargest.prefixSum v≤diameter B := by
  rw [Tplus_eq_sum,Rat.cast_sum,prefixSum_eq_sum,←Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun i _=>sub_nonneg.mpr (hv.2 i))
  · calc
      _ ≤ ∑ i : Fin 4,((B.hi i:ℝ)-(B.lo i:ℝ)) :=
        Finset.sum_le_sum (fun i _=>by linarith [hv.1 i])
      _ = _ := by simp [diameter,diameterQ,Rat.cast_sum,Rat.cast_sub]

def tau (p : Policy) (B : Box) (eta : ℚ) (v : LogFour) : ℝ :=
  typedResidual p v-(physicalResidual p B eta:ℝ)

def xiEff (p : Policy) (B : Box) (eta : ℚ) (v : LogFour) : ℝ :=
  v 3-((B.lo 3:ℝ)-(xi p B eta:ℝ))

theorem tau_bounds (p : Policy) (B : Box) (eta : ℚ) (hvalid : B.Valid)
    (htest : wholeBoxEligibleTest p B=true) (heta : 0<eta) (v : LogFour) (hv : v∈B.region) :
    0≤tau p B eta v ∧ tau p B eta v≤(5/2:ℝ)*diameter B+(21/16:ℝ)*(eta:ℝ) := by
  have hGU:=G_lt_capLower p B htest
  have hcap:=cap_bounds p B hv
  have hwidthQ:=capWidth_le p B hvalid
  have hwidth : (capUpper p B:ℝ)-(capLower p B:ℝ)≤(3/2:ℝ)*diameter B := by
    change (capUpper p B:ℝ)-(capLower p B:ℝ)≤(3/2:ℝ)*(diameterQ B:ℝ)
    exact_mod_cast hwidthQ
  have hpref:=prefix_error B v hv
  have hlossQ : 0<capLower p B-nu p B eta ∧ capLower p B-nu p B eta≤eta :=
    NearCapRationalParameters.level_error hGU heta
  have hdeltaQ : delta p B eta≤eta/64:=NearCapRationalParameters.delta_le_eta _ _ _
  have hdQ : 0<delta p B eta:=NearCapRationalParameters.delta_pos hGU heta
  have hloss : 0<(capLower p B:ℝ)-(nu p B eta:ℝ) ∧
      (capLower p B:ℝ)-(nu p B eta:ℝ)≤(eta:ℝ) := by exact_mod_cast hlossQ
  have hdelta : (delta p B eta:ℝ)≤(eta:ℝ)/64:=by exact_mod_cast hdeltaQ
  have hd : (0:ℝ)<(delta p B eta:ℝ):=by exact_mod_cast hdQ
  have hR : (physicalResidual p B eta:ℝ)=(nu p B eta:ℝ)-(Tplus B:ℝ)-20*(delta p B eta:ℝ) := by
    simp [physicalResidual]
  unfold tau typedResidual
  rw [hR]
  constructor <;> linarith

theorem xiEff_bounds (p : Policy) (B : Box) (eta : ℚ) (hvalid : B.Valid)
    (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest p B=true) (heta : 0<eta)
    (v : LogFour) (hv : v∈B.region) :
    0≤xiEff p B eta v ∧ xiEff p B eta v≤diameter B+(eta:ℝ)/64 := by
  have hpars:=rational_parameters p B eta hvalid hpositive htest heta
  have hxQ : 0<xi p B eta:=hpars.2.2.2.1
  have hxiQ : xi p B eta≤eta/64:=(small_parameter_bounds p B eta).2
  have hx : (0:ℝ)<(xi p B eta:ℝ):=by exact_mod_cast hxQ
  have hxi : (xi p B eta:ℝ)≤(eta:ℝ)/64:=by exact_mod_cast hxiQ
  have hwQ:=coordinateWidth_le_diameterQ B hvalid 3
  have hw : (B.hi 3:ℝ)-(B.lo 3:ℝ)≤diameter B:=by
    change (B.hi 3:ℝ)-(B.lo 3:ℝ)≤(diameterQ B:ℝ)
    exact_mod_cast hwQ
  unfold xiEff
  constructor <;> linarith [hv.1 3,hv.2 3]

theorem continuous_tau (p : Policy) (B : Box) (eta : ℚ) : Continuous (tau p B eta) :=
  ((continuous_cap p).sub U11SelectedLargest.continuous_prefixSum).sub continuous_const

theorem continuous_xiEff (p : Policy) (B : Box) (eta : ℚ) : Continuous (xiEff p B eta) :=
  (continuous_apply 3).sub continuous_const

theorem measurable_tau (p : Policy) (B : Box) (eta : ℚ) : Measurable (tau p B eta) :=
  (continuous_tau p B eta).measurable

theorem measurable_xiEff (p : Policy) (B : Box) (eta : ℚ) : Measurable (xiEff p B eta) :=
  (continuous_xiEff p B eta).measurable

/-- EXACT actual physical-query profile. Its two denominators are proved
positive by the same real fixed-cell parameters, not supplied as a profile premise. -/
theorem physical_profile_dictionary (p : Policy) (B : Box) (eta : ℚ)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest p B=true)
    (heta : 0<eta) (v : LogFour) :
    (0<(physicalResidual p B eta:ℝ) ∧ 0<(cutoffExponent p B eta:ℝ) ∧
      0<v 3-xiEff p B eta v) ∧
      (physicalResidual p B eta:ℝ)/(cutoffExponent p B eta:ℝ)=
        max (2+(rho p B eta:ℝ)) ((typedResidual p v-tau p B eta v)/(v 3-xiEff p B eta v)) := by
  have hpars:=rational_parameters p B eta hvalid hpositive htest heta
  have hRQ : 0<physicalResidual p B eta:=hpars.2.2.2.2.2.1
  have hZQ : 0<cutoffExponent p B eta:=hpars.2.2.2.2.2.2
  have hR : (0:ℝ)<(physicalResidual p B eta:ℝ):=by exact_mod_cast hRQ
  have hZ : (0:ℝ)<(cutoffExponent p B eta:ℝ):=by exact_mod_cast hZQ
  have hxiHalfQ : xi p B eta≤B.lo 3/2:=NearCapRationalParameters.xi_le_half _ _ _ _
  have hAq : 0<B.lo 3-xi p B eta:=by linarith
  have hA : (0:ℝ)<(B.lo 3:ℝ)-(xi p B eta:ℝ):=by exact_mod_cast hAq
  have hrhoQ : 0<rho p B eta:=hpars.2.2.2.2.1
  have hrho : (0:ℝ)<(rho p B eta:ℝ):=by exact_mod_cast hrhoQ
  have hC : (0:ℝ)<2+(rho p B eta:ℝ):=by linarith
  have hTau : typedResidual p v-tau p B eta v=(physicalResidual p B eta:ℝ) := by unfold tau;ring
  have hXi : v 3-xiEff p B eta v=(B.lo 3:ℝ)-(xi p B eta:ℝ) := by unfold xiEff;ring
  have hCut : (cutoffExponent p B eta:ℝ)=min ((B.lo 3:ℝ)-(xi p B eta:ℝ))
      ((physicalResidual p B eta:ℝ)/(2+(rho p B eta:ℝ))) := by
    simp [cutoffExponent]
  refine ⟨⟨hR,hZ,by rw [hXi];exact hA⟩,?_⟩
  rw [hTau,hXi,hCut]
  by_cases hleft : (B.lo 3:ℝ)-(xi p B eta:ℝ)≤
      (physicalResidual p B eta:ℝ)/(2+(rho p B eta:ℝ))
  · rw [min_eq_left hleft]
    have hmax : 2+(rho p B eta:ℝ)≤(physicalResidual p B eta:ℝ)/((B.lo 3:ℝ)-(xi p B eta:ℝ)) := by
      apply (le_div_iff₀ hA).2
      have hmul:=(le_div_iff₀ hC).1 hleft
      simpa only [mul_comm] using hmul
    rw [max_eq_right hmax]
  · have hright := le_of_not_ge hleft
    rw [min_eq_right hright]
    have hmax : (physicalResidual p B eta:ℝ)/((B.lo 3:ℝ)-(xi p B eta:ℝ))≤2+(rho p B eta:ℝ) := by
      apply (div_le_iff₀ hA).2
      have hmul:=(div_le_iff₀ hC).1 hright
      simpa only [mul_comm] using hmul
    rw [max_eq_left hmax]
    field_simp [hR.ne',hC.ne']
    <;> ring

def nativeCost (p : Policy) (B : Box) (eta : ℚ) : ℝ :=
  4*(1-Part5UpperTables.H248 ((physicalResidual p B eta:ℝ)/(cutoffExponent p B eta:ℝ)))/
    (physicalResidual p B eta:ℝ)

theorem nativeCost_eq_physicalCost (p : Policy) (B : Box) (eta : ℚ)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest p B=true)
    (heta : 0<eta) (v : LogFour) :
    nativeCost p B eta=BufferedOrdinaryClamp.physicalCost
      (typedResidual p v) (v 3) (tau p B eta v) (xiEff p B eta v) (rho p B eta:ℝ) := by
  have hprofile:=(physical_profile_dictionary p B eta hvalid hpositive htest heta v).2
  have hTau : typedResidual p v-tau p B eta v=(physicalResidual p B eta:ℝ) := by unfold tau;ring
  simp only [nativeCost,BufferedOrdinaryClamp.physicalCost,BufferedOrdinaryClamp.physicalQuery]
  rw [←hprofile,hTau]

theorem originalCost_eq_actualOrdinary (p : Policy) (v : LogFour) :
    BufferedOrdinaryClamp.originalCost (typedResidual p v) (v 3)=
      ordinaryKernel Part5UpperTables.H248 residual p.val v := by
  simp only [BufferedOrdinaryClamp.originalCost,ordinaryKernel,residual,dif_pos p.isLt]

/-- A common before-all-points buffer estimate for the actual all16
physical family. This directly supplies geometric-buffer convergence. -/
theorem uniform_buffer_bound (p : Policy) (B : Box) (eta : ℚ)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest p B=true)
    (heta : 0<eta) (v : LogFour) (hv : v∈B.region) :
    0≤tau p B eta v ∧ 0≤xiEff p B eta v ∧ 0≤(rho p B eta:ℝ) ∧
      max (tau p B eta v) (max (xiEff p B eta v) (rho p B eta:ℝ))≤
        (5/2:ℝ)*diameter B+(21/16:ℝ)*(eta:ℝ) := by
  have ht:=tau_bounds p B eta hvalid htest heta v hv
  have hx:=xiEff_bounds p B eta hvalid hpositive htest heta v hv
  have hpars:=rational_parameters p B eta hvalid hpositive htest heta
  have hrQ : 0<rho p B eta:=hpars.2.2.2.2.1
  have hr : (0:ℝ)<(rho p B eta:ℝ):=by exact_mod_cast hrQ
  have hrleQ:=(small_parameter_bounds p B eta).1
  have hrle : (rho p B eta:ℝ)≤(eta:ℝ)/64:=by exact_mod_cast hrleQ
  have hd:=diameter_nonneg B hvalid
  have he : (0:ℝ)<(eta:ℝ):=by exact_mod_cast heta
  refine ⟨ht.1,hx.1,hr.le,max_le ht.2 (max_le ?_ ?_)⟩ <;> linarith

/-- If every coordinate width and eta are at most h, the real geometric
buffers of EVERY original policy are at most12h, uniformly over its box. -/
theorem uniform_buffer_bound_of_coordinate_side (p : Policy) (B : Box) (eta : ℚ)
    (hvalid : B.Valid) (hpositive : 0<B.lo 3) (htest : wholeBoxEligibleTest p B=true)
    (heta : 0<eta) (h : ℝ) (hh : 0≤h)
    (hside : ∀ i : Fin 4,(B.hi i:ℝ)-(B.lo i:ℝ)≤h) (hetaSmall : (eta:ℝ)≤h)
    (v : LogFour) (hv : v∈B.region) :
    0≤tau p B eta v ∧ 0≤xiEff p B eta v ∧ 0≤(rho p B eta:ℝ) ∧
      max (tau p B eta v) (max (xiEff p B eta v) (rho p B eta:ℝ))≤12*h := by
  have hb:=uniform_buffer_bound p B eta hvalid hpositive htest heta v hv
  have hdiam : diameter B≤4*h := by
    calc
      diameter B = ∑ i : Fin 4,((B.hi i:ℝ)-(B.lo i:ℝ)) := by
        simp [diameter,diameterQ,Rat.cast_sum,Rat.cast_sub]
      _ ≤ ∑ _i : Fin 4,h := Finset.sum_le_sum (fun i _=>hside i)
      _ = 4*h := by simp;ring
  exact ⟨hb.1,hb.2.1,hb.2.2.1,by linarith [hb.2.2.2]⟩

end

end ImbalancedChen.P5Z.U1011OriginalSixteenNearCapBoxProfiles
