import ImbalancedChen.P4BOriginalHigherLowLocalWindows
import ImbalancedChen.P5ZU1011OriginalW16FactorMonomials
import ImbalancedChen.P4AOriginalFiniteFallbackOriginalLength

namespace ImbalancedChen.P4BOriginalHigherLowEndpointBounds
noncomputable section
open Classical VariableEnvelope
open P4BOriginalCollisionWords (Params)
open P4BOriginalHigherLowBins (Groups bins split split_perm selected rest cover theta useRoot)
open P4BOriginalHigherLowRootRows (Row sum)
open P4BOriginalHigherLowRepresentative (d t cell row level)
open P4BOriginalHigherLowLocalWindows (conversion theta_window cover_power selected_window rescue_window)
open P4BOriginalMediumTriplePowers (power power_mono positive_le_iff upper_iff power_base power_rpow power_pow)
open P4AOriginalFiniteFallbackPhysicalSelected (head)
open P4BUpperSelectedBoxCapacity (endpoint endpoint_positive)
open P4AHeldTaggedCompilerSupport (J0)
open Part3.ActualWFineWordAdapter (fineSlots)
open Part3.ActualWThreeCapacityRun (wp)
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation (PrefixSquareBound)

theorem original (P : Params) (hN : 1<P.N) (he : 0<P.e) (hes : (P.e:ℝ)≤1/2048)
    (hstep : logPrimeMeshStep 0 (19/96) (d P).m≤(P.e:ℝ)/20) (ho : 0<P.omega)
    {J : List ℕ} (hJ : J∈P.words) (huse : useRoot P J) {x U z : ℝ}
    (hx : 1<x) (hz : 0<z) (hz' : z≤(P.e:ℝ)/512) (hb : P.T*((J0 P.omega:ℝ)+1)≤z)
    (hlo : x^(1-z)≤(P.N:ℝ)) (hhi : (P.N:ℝ)≤x^(1+z))
    (hU : x^(2*z)≤U) (hU' : U≤x^(1/3+z/2)) (hell : 2*P.ell≤z/16) :
    let S := split P x U z J
    let H := actualPrimeFineLabelIntegerUpper P.N P.T
    let a := endpoint H S.1
    let b := endpoint H S.2.1
    let c := endpoint H S.2.2*x^(2*P.ell)
    a<U*x^(-z/100) ∧ U^2*b*c^2<x^(1-8*(z/100)) ∧
      x^(7/32:ℝ)*U*a*b^5*c^2<x^(2-15*(z/100)) ∧
      U^(23/16:ℝ)*a*b^(73/16:ℝ)*c^(39/16:ℝ)<x^(2-15*(z/100)) := by
  let H := actualPrimeFineLabelIntegerUpper P.N P.T
  let r := row P J
  let M := level P J
  let p := head J
  let C0 := cover r M (P.e:ℝ)
  let v := theta P.N x z C0
  let A := U/x^z
  let S := split P x U z J
  let a := endpoint H S.1
  let b := endpoint H S.2.1
  let c := endpoint H S.2.2
  have hnr : (1:ℝ)<P.N := by exact_mod_cast hN
  have hn := zero_lt_one.trans hnr
  have hp := zero_lt_one.trans hx
  have hUpos := (Real.rpow_pos_of_pos hp _).trans_le hU
  have hAz : A*x^z=U := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hp _).ne'
  have hAp : 0<A := div_pos hUpos (Real.rpow_pos_of_pos hp _)
  have hA : 1≤A := (le_div_iff₀ (Real.rpow_pos_of_pos hp _)).mpr (by
    rw [one_mul]; exact (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : z≤2*z)).trans hU)
  have hAu : A≤x^(1/3-z/2) := (div_le_iff₀ (Real.rpow_pos_of_pos hp _)).mpr (by
    rw [←Real.rpow_add hp,show (1/3:ℝ)-z/2+z=1/3+z/2 by ring]; exact hU')
  obtain ⟨hM,hM',hg,hs,hs',hEl,hEu,hfull,hrest,hpos,hfirst,hlate⟩ :=
    P4BOriginalHigherLowKeySupport.natural P hN he hes hstep ho hJ huse hb
  have heR : 0<(P.e:ℝ) := by exact_mod_cast he
  have hzsm : z≤1/400 := by linarith
  obtain ⟨hq,hq'⟩ := conversion hn hx hz hlo hhi
  obtain ⟨_,_,hv,hv'⟩ := theta_window r heR hes hz hz' hM hM' hq hq'
  change 1/2≤v at hv
  change v≤cap at hv'
  have hC : M+z≤C0 := by dsimp [C0,cover]; split_ifs <;> linarith only [heR,hz']
  have coveq : x^(v-2*z)=(P.N:ℝ)^C0 := cover_power hn hx
  have hD : (P.N:ℝ)^(M+z)≤x^(v-2*z) := coveq ▸ Real.rpow_le_rpow_of_exponent_le hnr.le hC
  have hf : actualDwellSupport (x^(v-2*z)) (J.map H) := fun i hi => (hfull i hi).trans hD
  have part := split_perm P x U z hJ
  change (S.1++(S.2.1++S.2.2)).Perm J at part
  have pref (l : List ℕ) (hl : ∀q∈l,q∈S.1++(S.2.1++S.2.2)) : 0<endpoint H l :=
    endpoint_positive H l (fun q hq => hpos q (part.mem_iff.mp (hl q hq)))
  have ha : 0<a := pref S.1 (fun q hq => by simp [hq])
  have hb' : 0<b := pref S.2.1 (fun q hq => by simp [hq])
  have hc : 0<c := pref S.2.2 (fun q hq => by simp [hq])
  have upper_mono : actualSelectedSubproductUpper (1+z) v≤actualSelectedSubproductUpper 1 v := by
    unfold actualSelectedSubproductUpper
    exact min_le_min le_rfl (by linarith only [hz])
  have relax := Real.rpow_le_rpow_of_exponent_le hx.le upper_mono
  have mon : a≤A ∧ A^2*b*c^2≤x^(1-3*z) ∧ x^(7*1/32:ℝ)*A*a*b^5*c^2≤x^(2-4*z) ∧
      (A*c/b)^(7/16:ℝ)*A*a*b^5*c^2≤x^(2-39*z/8) := by
    by_cases hr : r=.rescue
    · let B := x^(2*v-1)
      let C := x^(1-v-2*z)/A
      let T := x^(actualSelectedSubproductUpper (1+z) v-(2*v-1))
      let tail := J.drop 3
      let out := fineSlots P.N P.T A B C p tail
      have grp : S=(out.left,out.middle,out.right) := by
        change split P x U z J=_
        rw [split,if_pos huse]
        change (if r=.rescue then (out.left,out.middle,out.right) else _)=_
        exact if_pos hr
      have hj := P4BOriginalHigherLowRepresentative.front_eq J (Finset.mem_filter.mp hJ).2
      have inJ (j : ℕ) (h : j∈p 0::p 1::p 2::tail) : j∈J :=
        (congrArg (fun l : List ℕ => j∈l) hj).mp h
      have hinit : ∀i,(p i)∈J := fun i => by
        apply inJ
        fin_cases i <;> simp
      have hvw : v=power x (P.N:ℝ)*(M+(P.e:ℝ))+2*z := by dsimp [v,C0,theta,cover]; rw [if_pos hr]
      have gate : VariableEnvelope.A (t P J 0)≤M+11*(P.e:ℝ)/20 ∧
          M+2*(P.e:ℝ)≤VariableEnvelope.B (t P J 2) := by
        simpa only [show row P J=.rescue from hr,if_pos rfl] using hg
      have hT : P.T≤z := by
        have hh := mul_nonneg P.T_pos.le (Nat.cast_nonneg (J0 P.omega)); linarith
      have hqpos : 0≤power x (P.N:ℝ) := (by linarith : 0≤1-z).trans hq
      have lift (j : ℕ) (u : ℝ) (hj' : j∈J) (hk : (H j:ℝ)≤(P.N:ℝ)^(u+P.T)) :
          power x (H j:ℝ)≤power x (P.N:ℝ)*(u+z) := by
        have H' := power_mono hx (Nat.cast_pos.mpr (hpos j hj')) hk
        rw [power_rpow hn] at H'
        calc
          _≤(u+P.T)*power x (P.N:ℝ) := H'
          _=power x (P.N:ℝ)*(u+P.T) := mul_comm _ _
          _≤_ := mul_le_mul_of_nonneg_left (add_le_add_left hT u) hqpos
      have ord := (P4BOriginalHigherLowRepresentative.owner_data P hN he.le ho.le hJ).2.2.2
      have hOrdered : Ordered (t P J 0) (t P J 1) (t P J 2) :=
        ⟨ord.1,ord.2.1,ord.2.2,huse.2.1⟩
      have keyWindow (j : ℕ) (hj' : j∈p 2::tail) :
          power x (H (p 0):ℝ)≤2*v-1 ∧ 2*power x (H (p 1):ℝ)≤1-v-2*z ∧
          power x (H j:ℝ)≤actualSelectedSubproductUpper (1+z) v-(2*v-1) := by
        have hjJ : j∈J := inJ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj'))
        simpa only [←hvw] using rescue_window (k:=z) heR hes hz hz' le_rfl hq hq' hM hM' hOrdered
          gate.1 gate.2 (lift _ _ (hinit 0) (hfirst 0)) (lift _ _ (hinit 1) (hfirst 1)) (lift _ _ hjJ (hlate j hj'))
      have ini := keyWindow (p 2) List.mem_cons_self
      have hB : (H (p 0):ℝ)≤B := (upper_iff hx (Nat.cast_pos.mpr (hpos _ (hinit 0)))).mpr ini.1
      have hAC : A*C=x^(1-v-2*z) := by dsimp [C]; field_simp [hAp.ne']
      have hQ : (H (p 1):ℝ)^2≤A*C := by
        rw [hAC]; apply (upper_iff hx (sq_pos_of_pos (Nat.cast_pos.mpr (hpos _ (hinit 1))))).mpr
        simpa only [power_pow,Nat.cast_ofNat] using ini.2.1
      have hBnd : 1≤C := (le_div_iff₀ hAp).mpr (by
        rw [one_mul]; apply hAu.trans (Real.rpow_le_rpow_of_exponent_le hx.le ?_)
        dsimp [cap] at hv'; linarith only [hv',hzsm])
      have keypos (l) (hl : l∈p 0::p 1::p 2::tail) : 0<(H l:ℝ) :=
        Nat.cast_pos.mpr (hpos _ (inJ l hl))
      have endpos (j) (hj' : j∈p 2::tail) : 0<(H j:ℝ) := keypos j (by simp only [List.mem_cons]; tauto)
      have bound : PrefixSquareBound (fun i => (H i:ℝ)) (x^(v-2*z)) (p 0::p 1::p 2::tail) := by
        change PrefixSquareBound _ _ (P4AOriginalFiniteFallbackSelectedMask.front (head J) (J.drop 3))
        rw [hj]; intro i hi
        simpa only [←List.map_take,List.map_map,List.getElem_map,Function.comp_def] using
          hf i (by simpa only [List.length_map] using hi)
      obtain ⟨_,cases'⟩ := Part3.ActualWFineWordAdapter.fineSlots_correct P.N P.T
        (A:=A) (B:=B) (C:=C) (D:=x^(v-2*z)) (U:=T) p tail hA hBnd
        keypos hB hQ (fun j hj' => (upper_iff hx (endpos j hj')).mpr (keyWindow j hj').2.2) bound
      have eqA : a=wp (fun i => (H i:ℝ)) out.left := by rw [show a=endpoint H S.1 from rfl,grp]; rfl
      have eqB : b=wp (fun i => (H i:ℝ)) out.middle := by rw [show b=endpoint H S.2.1 from rfl,grp]; rfl
      have eqC : c=wp (fun i => (H i:ℝ)) out.right := by rw [show c=endpoint H S.2.2 from rfl,grp]; rfl
      rcases cases' with succ|⟨overflow,mid,left,right⟩
      · have Hm := P5Z.U1011OriginalW16FactorMonomials.W_success_monomials (delta:=z) (nu:=v) hx hAp ha hb' hc
          hv' (by simpa only [eqA] using succ.1) (by simpa only [eqB] using succ.2.1)
          (by simpa only [eqC] using succ.2.2)
        exact ⟨by simpa only [eqA] using succ.1,Hm.1.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),by simpa using Hm.2⟩
      · change B<wp _ out.middle at overflow
        change wp _ out.middle≤B*T at mid
        have prod : A*b*c≤x^(v-2*z) := by
          have H := (le_div_iff₀ (mul_pos hAp hb')).mp (show c≤x^(v-2*z)/(A*b) from by simpa only [eqB,eqC] using right)
          simpa only [mul_comm c (A*b)] using H
        have bt : B*T=x^actualSelectedSubproductUpper (1+z) v := by
          dsimp only [B,T]; rw [←Real.rpow_add hp]; congr 1 <;> ring
        have Hm := selectedPair_monomials (δ:=z) (θ:=v) (α:=1) hx hAp ha hb' hc prod
          (by simpa only [eqB] using overflow.le) ((by simpa only [eqB,bt] using mid :
            b≤x^actualSelectedSubproductUpper (1+z) v).trans relax) (by simpa only [eqA] using left)
        exact ⟨by simpa only [eqA] using left,Hm.1.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),Hm.2⟩
    · have eC : C0=M+(P.e:ℝ)/4 := by simp only [C0,cover,if_neg hr]
      have hgg := hg
      rw [if_neg hr] at hgg
      have hw := selected_window (k:=z) hn hx heR hes hz hz' le_rfl hlo hhi hM hM' hs hs' hgg hEl hEu
      simp only [←eC] at hw
      have hpart : (selected r p++rest r p (J.drop 3)).Perm J := by
        simpa only [P4BOriginalHigherLowRepresentative.front_eq J (Finset.mem_filter.mp hJ).2] using
          P4BOriginalHigherLowBins.perm r (head J) (J.drop 3)
      have hr' : actualDwellSupport (x^(v-2*z)/endpoint H (selected r p)) ((rest r p (J.drop 3)).map H) :=
        fun i hi => (hrest i hi).trans (div_le_div_of_nonneg_right hD (by rw [P4BUpperSelectedBoxCapacity.endpoint_eq_cast]; positivity))
      have HM := P4BUpperSelectedBoxCapacity.monomials (alpha:=1) hx hz (by linarith) hv
        (by dsimp [cap] at hv'; linarith) H _ _ _ hpart hpos hA hAu hf hr' hw.1 (hw.2.trans relax)
      simpa only [a,b,c,S,split,if_pos huse,bins,if_neg hr,P4BUpperSelectedBoxCapacity.endpoints] using HM
  have R := P4AOriginalFiniteFallbackOriginalLength.beta_and_length (alpha:=1) hx hz hell hAp ha hb' hc
    mon.1 mon.2.1 mon.2.2.1 mon.2.2.2
  simpa only [hAz,mul_one] using R

end
end ImbalancedChen.P4BOriginalHigherLowEndpointBounds
