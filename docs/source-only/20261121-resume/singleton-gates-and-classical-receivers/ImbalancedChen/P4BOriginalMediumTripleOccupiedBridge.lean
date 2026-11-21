import ImbalancedChen.P4BOriginalMediumTripleAllocation
import all ImbalancedChen.P4BOriginalMediumOccupiedLengths

/-!
SOURCE ONLY / NOT COMPILED.

Remove only the pair-mother Index binding from the occupied triple caller.
The original raw representative, endpoint cube and finite two-slot allocation
are reused. No greedy cases, source cube, or general M geometry are reproved.
The generic private capacity helper retains its original owner requirement.
-/
namespace ImbalancedChen.P4BOriginalMediumTripleOccupiedBridge
noncomputable section
open Classical
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (ownerHead)
open P4BOriginalCollisionThirdFactor (splitAt thirdSupport gamma_range)
open P4BOriginalMediumAtomFamily (support support_data third_data)
open P4BOriginalMediumLowTriple (actual_third actual_cap_lower low_choice)
open P4BOriginalMediumTriplePowers
open P4BUpperSelectedBoxCapacity (endpoint)
open P5Z.HBRightClosedDyadicRoles (Block owner owner_owns)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P4AOriginalFiniteFallbackGroupedAtoms (slots group_support)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag)
open P4AOriginalFiniteFallbackOwnCubeRows (old)
open P4AOriginalNewFifthUnion (data)
open VariableEnvelope (mu)
open private groups_left from ImbalancedChen.P4BOriginalMediumOccupiedLengths

/-- This public Params-only owner read is the same actual support read as
the old Index-bound factor_owner. It does not assume a length estimate. -/
theorem factor_owner (P : Params) (S : List ℕ) {D : Block}
    (hD : D∈(support P S).image owner) :
    (lower D:ℝ)≤endpoint (actualPrimeFineLabelIntegerUpper P.N P.T) S := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hD
  have h := (owns_bounds (owner_owns (support_data P S hq).1)).1
  exact (by exact_mod_cast h : (lower (owner q):ℝ)≤q).trans
    (group_support P.N P.omega P.T S q hq)

theorem third_owner (P : Params) (J S : List ℕ) {D : Block}
    (hD : D∈(thirdSupport P J S).image owner) :
    (lower D:ℝ)≤P.L*endpoint (actualPrimeFineLabelIntegerUpper P.N P.T) S := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hD
  have h := (owns_bounds (owner_owns (third_data P J S hq).1)).1
  exact (by exact_mod_cast h : (lower (owner q):ℝ)≤q).trans (gamma_range P hq)

/-- The three actual occupied modulus owners of a low-first triple.
All inputs are original policy, scale-window and support facts. In
particular none of the four desired M inequalities is an input. -/
theorem original_three (P : Params) (hN : 1<P.N)
    (he : 0≤P.e) (he' : (P.e:ℝ)≤1/2048) (hq : 0<P.q)
    {x U zeta kappa : ℝ} (hx : 1<x) (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : kappa≤zeta) (hNx : (P.N:ℝ)≤x^(1+kappa))
    (hU1 : x^(2*zeta)≤U) (hU2 : U≤x^(1/3+zeta/2))
    (hT : P.T≤zeta) (hell : 0≤P.ell) (hell' : 2*P.ell≤zeta/16)
    {J : List ℕ} (hJ : J∈P.words) (h3 : J.length=3)
    (hl : actualPrimeTupleLog P.N (ownerHead P J) 0≤mu)
    (D E G : Block)
    (hD : D∈(support P (splitAt P x U zeta J).1).image owner)
    (hE : E∈(support P (splitAt P x U zeta J).2.1).image owner)
    (hG : G∈(thirdSupport P J (splitAt P x U zeta J).2.2).image owner) :
    (lower D:ℝ)<U*x^(-(zeta/2000)) ∧
      U^2*(lower E:ℝ)*(lower G:ℝ)^2<x^(1-8*(zeta/2000)) ∧
      (P.N:ℝ)^(7/32:ℝ)*U*(lower D:ℝ)*(lower E:ℝ)^5*(lower G:ℝ)^2<x^(2-15*(zeta/2000)) ∧
      U^(23/16:ℝ)*(lower D:ℝ)*(lower E:ℝ)^(73/16:ℝ)*(lower G:ℝ)^(39/16:ℝ)<x^(2-15*(zeta/2000)) := by
  let p := ownerHead P J
  let t := actualPrimeTupleLog P.N p
  let j := fun i : Fin 3 => tag P.N P.T (p i)
  let H := actualPrimeFineLabelIntegerUpper P.N P.T
  let M := old (data P.e P.q P.a) P.omega P.N p
  let A := U/x^zeta
  let ac := actualTwoCapacityGreedy (fun i => (H i:ℝ)) A [j 1,j 2]
  let S := splitAt P x U zeta J
  have hx0 := zero_lt_one.trans hx
  have hu := (Real.rpow_pos_of_pos hx0 (2*zeta)).trans_le hU1
  have hposA : 0<A := div_pos hu (Real.rpow_pos_of_pos hx0 _)
  have hA : 1≤A := (le_div_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr (by
    rw [one_mul]
    exact (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : zeta≤2*zeta)).trans hU1)
  have hU : power x U≤167/500 := by
    have H := (upper_iff hx hu).mp hU2
    linarith only [H,hz0]
  have hnr : (0:ℝ)<P.N := by exact_mod_cast (show 0<P.N by omega)
  have hn := (upper_iff hx hnr).mp hNx
  obtain ⟨hj,_,_,_⟩ := actual_third P hN he hJ h3
  change J=[j 0,j 1,j 2] at hj
  obtain ⟨hp,hin,hcube,hm0⟩ := original_endpoints P hN he hJ h3 hx hNx hk hz0 hT hl
  change ∀i : Fin 3,0<(H (j i):ℝ) at hp
  change ∀i : Fin 3,power x (H (j i))≤49/250 at hin
  change power x (H (j 0))+power x (H (j 1))+3*power x (H (j 2))≤3/5 at hcube
  change power x (H (j 0))≤t 0+1/1000 at hm0
  have hM : t 0+3/8≤M := actual_cap_lower P he' hq p hl
  have hc : 1≤x^(M+4*zeta)/(A*(H (j 0):ℝ)) := by
    apply (le_div_iff₀ (mul_pos hposA (hp 0))).mpr
    rw [one_mul]
    apply (upper_iff hx (mul_pos hposA (hp 0))).mpr
    rw [power_mul hposA (hp 0),show power x A=power x U-zeta from cap_power hx hu]
    linarith only [hz,hM,hm0,hU]
  have groups : S=(ac.1,[j 0],ac.2) := by
    dsimp only [S,splitAt,slots]
    rw [low_choice P p hl]
    change P4BUpperSelectedBoxCapacity.groups (x^(M+4*zeta)) A H (J.take 1) (J.drop 1) J=_
    rw [hj]
    simpa only [List.take_succ_cons,List.take_zero,List.drop_succ_cons,List.drop_zero,
      P4BUpperSelectedBoxCapacity.groups,endpoint,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      mul_one,if_pos hc]
  have hL : power x P.L≤zeta/16 := by
    rw [show P.L=(P.N:ℝ)^P.ell from rfl,power_rpow hnr]
    have H := mul_le_mul_of_nonneg_left (hn.trans (by linarith only [hk,hz0] : 1+kappa≤2)) hell
    linarith only [H,hell']
  have hdP : (0:ℝ)<lower D := by exact_mod_cast lower_pos D
  have heP : (0:ℝ)<lower E := by exact_mod_cast lower_pos E
  have hgP : (0:ℝ)<lower G := by exact_mod_cast lower_pos G
  have hd := factor_owner P S.1 hD
  have heB := factor_owner P S.2.1 hE
  have hg := third_owner P J S.2.2 hG
  rw [groups] at hd heB hg
  change (lower D:ℝ)≤endpoint H ac.1 at hd
  change (lower G:ℝ)≤P.L*endpoint H ac.2 at hg
  have he0 : (lower E:ℝ)≤H (j 0) := by simpa [endpoint] using heB
  have hlP : 0<P.L := Real.rpow_pos_of_pos hnr _
  have hcP : 0<endpoint H ac.2 := pos_of_mul_pos_right (hgP.trans_le hg) hlP.le
  obtain ⟨h2,h3',h4⟩ := P4BOriginalMediumTripleAllocation.three_monomials H (j 0) (j 1) (j 2)
    (x:=x) (U:=U) (eta:=zeta) (n:=power x (P.N:ℝ)) (q1:=power x (lower D))
    (q2:=power x (lower E)) (q3:=power x (lower G)) hx hu hU hz0
    (by linarith only [hn,hk,hz0]) (hp 1) (hp 2) (hin 0) (hin 1) (hin 2) hcube
    ⟨power_mono hx hdP hd,power_mono hx heP he0,by
      have H := power_mono hx hgP hg
      rw [power_mul hlP hcP] at H
      linarith only [H,hL]⟩
  have first : (lower D:ℝ)≤A := by
    apply (factor_owner P S.1 hD).trans
    dsimp only [S,splitAt,slots]
    split <;> apply groups_left _ _ _ _ _ _ hA
  refine ⟨?_,?_,?_,?_⟩
  · apply first.trans_lt
    change U/x^zeta<U*x^(-(zeta/2000))
    calc
      U/x^zeta=U*x^(-zeta) := by rw [Real.rpow_neg hx0.le,div_eq_mul_inv]
      _<_ := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)) hu
  · apply (strict_iff hx (by positivity)).mpr
    simpa only [power_mul (mul_pos (sq_pos_of_pos hu) heP) (sq_pos_of_pos hgP),
      power_mul (sq_pos_of_pos hu) heP,power_pow,Nat.cast_ofNat] using h2
  · apply (strict_iff hx (by positivity)).mpr
    have hn7 := Real.rpow_pos_of_pos hnr (7/32:ℝ)
    have he5 := pow_pos heP 5
    simpa only [power_mul (mul_pos (mul_pos (mul_pos hn7 hu) hdP) he5) (sq_pos_of_pos hgP),
      power_mul (mul_pos (mul_pos hn7 hu) hdP) he5,power_mul (mul_pos hn7 hu) hdP,power_mul hn7 hu,
      power_pow,power_rpow hnr,Nat.cast_ofNat] using h3'
  · apply (strict_iff hx (by positivity)).mpr
    have hu23 := Real.rpow_pos_of_pos hu (23/16:ℝ)
    have he73 := Real.rpow_pos_of_pos heP (73/16:ℝ)
    have hg39 := Real.rpow_pos_of_pos hgP (39/16:ℝ)
    simpa only [power_mul (mul_pos (mul_pos hu23 hdP) he73) hg39,
      power_mul (mul_pos hu23 hdP) he73,power_mul hu23 hdP,
      power_rpow hu,power_rpow heP,power_rpow hgP] using h4

end
end ImbalancedChen.P4BOriginalMediumTripleOccupiedBridge
