import ImbalancedChen.P4BOriginalMediumTripleAllocation

/-! Four manuscript lengths for every occupied low-first three-slot word
of the same physical high-rank coefficient. -/
namespace ImbalancedChen.P4BOriginalMediumLowThreeLengths
noncomputable section
open Classical Filter
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P4BOriginalMediumAtomFamily (Index)
open P4BOriginalMediumAtomReconstruction (withOwners)
open P4BOriginalMediumOccupiedLengths (firstOwners secondOwners thirdOwners factor_owner small_rough_owner)
open P4BOriginalMediumLowTriple (actual_third actual_cap_lower low_choice)
open P4BOriginalMediumTriplePowers (power power_mono power_one power_mul power_pow power_rpow power_base
  upper_iff strict_iff cap_power positive_le_iff original_endpoints)
open P4BOriginalCollisionTensor (ownerHead)
open P4BUpperSelectedBoxCapacity (endpoint)
open P4AOriginalFiniteFallbackOwnCubeRows (old)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag)
open P4AOriginalNewFifthUnion (data)
open VariableEnvelope (mu)

private theorem three_at {order : ℕ} {zeta kap0 kappa : ℝ} (I : Index order zeta kap0)
    (hη : I.eta=zeta) (hz : 0<zeta) (hz0 : zeta≤1/20000) (hk : kappa≤zeta)
    (hN : 1<I.P.N) (he : 0≤I.P.e) (he' : (I.P.e:ℝ)≤1/2048) (hq : 0<I.P.q)
    (hT : I.P.T≤zeta) (hell : 0≤I.P.ell) (hell' : 2*I.P.ell≤zeta/16)
    (hx : 1<I.x) (hNx : (I.P.N:ℝ)≤I.x^(1+kappa))
    (hU1 : I.x^(2*zeta)≤I.U) (hU2 : I.U≤I.x^(1/3+zeta/2))
    (h3 : I.J.length=3) (hl : actualPrimeTupleLog I.P.N (ownerHead I.P I.J) 0≤mu)
    (K : ℕ) (D E G : Block) (hD : D∈firstOwners I) (hE : E∈secondOwners I) (hG : G∈thirdOwners I) :
    let d := (withOwners I D E G).atom K
    let s := zeta/2000
    d.Q1<d.U*d.scale^(-s) ∧ d.U^2*d.Q2*d.Q3^2<d.scale^(1-8*s) ∧
      (d.residue.natAbs:ℝ)^(7/32:ℝ)*d.U*d.Q1*d.Q2^5*d.Q3^2<d.scale^(2-15*s) ∧
      d.U^(1+2*(7/32:ℝ))*d.Q1*d.Q2^(5-2*(7/32:ℝ))*d.Q3^(2+2*(7/32:ℝ))<d.scale^(2-15*s) := by
  let P := I.P
  let p := ownerHead P I.J
  let t := actualPrimeTupleLog P.N p
  let j := fun i : Fin 3 => tag P.N P.T (p i)
  let H := actualPrimeFineLabelIntegerUpper P.N P.T
  let M := old (data P.e P.q P.a) P.omega P.N p
  let A := I.U/I.x^zeta
  let ac := actualTwoCapacityGreedy (fun i => (H i:ℝ)) A [j 1,j 2]
  have hx0 := zero_lt_one.trans hx
  have hu := (Real.rpow_pos_of_pos hx0 (2*zeta)).trans_le hU1
  have hposA : 0<A := div_pos hu (Real.rpow_pos_of_pos hx0 _)
  have hzU := (upper_iff hx hu).mp hU2
  have hU : power I.x I.U≤167/500 := by linarith only [hzU,hz0]
  have hnr : (0:ℝ)<P.N := by exact_mod_cast I.N_pos
  have hn := (upper_iff hx hnr).mp hNx
  obtain ⟨hj,_,_,_⟩ := actual_third P hN he I.word h3
  change I.J=[j 0,j 1,j 2] at hj
  obtain ⟨hp,hin,hcube,hm0⟩ := original_endpoints P hN he I.word h3 hx hNx hk hz0 hT hl
  change ∀i : Fin 3,0<(H (j i):ℝ) at hp
  change ∀i : Fin 3,power I.x (H (j i))≤49/250 at hin
  change power I.x (H (j 0))+power I.x (H (j 1))+3*power I.x (H (j 2))≤3/5 at hcube
  change power I.x (H (j 0))≤t 0+1/1000 at hm0
  have hM : t 0+3/8≤M := actual_cap_lower P he' hq p hl
  have hc : 1≤I.x^(M+4*zeta)/(A*(H (j 0):ℝ)) := by
    apply (le_div_iff₀ (mul_pos hposA (hp 0))).mpr
    rw [one_mul]
    apply (upper_iff hx (mul_pos hposA (hp 0))).mpr
    rw [power_mul hposA (hp 0),show power I.x A=power I.x I.U-zeta from cap_power hx hu]
    linarith only [hz,hM,hm0,hU]
  have groups : I.groups=(ac.1,[j 0],ac.2) := by
    unfold Index.groups P4BOriginalCollisionThirdFactor.splitAt P4AOriginalFiniteFallbackGroupedAtoms.slots
    rw [low_choice P p hl,hη]
    change P4BUpperSelectedBoxCapacity.groups (I.x^(M+4*zeta)) A H (I.J.take 1) (I.J.drop 1) I.J=_
    rw [hj]
    simpa only [List.take_succ_cons,List.take_zero,List.drop_succ_cons,List.drop_zero,
      P4BUpperSelectedBoxCapacity.groups,endpoint,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      mul_one,if_pos hc]
  have hL : power I.x P.L≤zeta/16 := by
    rw [show P.L=(P.N:ℝ)^P.ell from rfl,power_rpow hnr]
    have h := mul_le_mul_of_nonneg_left (hn.trans (by linarith only [hk,hz0] : 1+kappa≤2)) hell
    linarith only [h,hell']
  have hD0 : (0:ℝ)<lower D := by exact_mod_cast lower_pos D
  have hE0 : (0:ℝ)<lower E := by exact_mod_cast lower_pos E
  have hG0 : (0:ℝ)<lower G := by exact_mod_cast lower_pos G
  have hd := factor_owner I hD
  have hE' := factor_owner I hE
  have hg := small_rough_owner I hG
  change (lower D:ℝ)≤endpoint H I.groups.1 at hd
  change (lower E:ℝ)≤endpoint H I.groups.2.1 at hE'
  change (lower G:ℝ)≤P.L*endpoint H I.groups.2.2 at hg
  rw [groups] at hd hE' hg
  change (lower D:ℝ)≤endpoint H ac.1 at hd
  change (lower G:ℝ)≤P.L*endpoint H ac.2 at hg
  have he0 : (lower E:ℝ)≤H (j 0) := by simpa [endpoint] using hE'
  have hlPos : 0<P.L := Real.rpow_pos_of_pos hnr _
  have hcPos : 0<endpoint H ac.2 := pos_of_mul_pos_right (hG0.trans_le hg) hlPos.le
  have Hbounds := P4BOriginalMediumTripleAllocation.three_monomials H (j 0) (j 1) (j 2)
    (x:=I.x) (U:=I.U) (eta:=zeta) (n:=power I.x (P.N:ℝ)) (q1:=power I.x (lower D))
    (q2:=power I.x (lower E)) (q3:=power I.x (lower G)) hx hu hU hz0
    (by linarith only [hn,hk,hz0]) (hp 1) (hp 2) (hin 0) (hin 1) (hin 2) hcube
    ⟨power_mono hx hD0 hd,power_mono hx hE0 he0,by
      have hh := power_mono hx hG0 hg
      rw [power_mul hlPos hcPos] at hh
      linarith only [hh,hL]⟩
  obtain ⟨h2,h3',h4⟩ := Hbounds
  refine ⟨by simpa only [hη] using P4BOriginalMediumOccupiedLengths.first_length I K D E G hD
    hx (hη.symm ▸ hz) (hη.symm ▸ hU1),?_,?_,?_⟩
  · change I.U^2*(lower E:ℝ)*(lower G:ℝ)^2<I.x^_
    apply (strict_iff hx (by positivity)).mpr
    simpa only [power_mul (mul_pos (sq_pos_of_pos hu) hE0) (sq_pos_of_pos hG0),
      power_mul (sq_pos_of_pos hu) hE0,power_pow,Nat.cast_ofNat] using h2
  · change (P.N:ℝ)^(7/32:ℝ)*I.U*(lower D:ℝ)*(lower E:ℝ)^5*(lower G:ℝ)^2<I.x^_
    apply (strict_iff hx (by positivity)).mpr
    have hn7 := Real.rpow_pos_of_pos hnr (7/32:ℝ)
    have h5 := pow_pos hE0 5
    simpa only [power_mul (mul_pos (mul_pos (mul_pos hn7 hu) hD0) h5) (sq_pos_of_pos hG0),
      power_mul (mul_pos (mul_pos hn7 hu) hD0) h5,power_mul (mul_pos hn7 hu) hD0,power_mul hn7 hu,
      power_pow,power_rpow hnr,Nat.cast_ofNat] using h3'
  · change I.U^(1+2*(7/32:ℝ))*(lower D:ℝ)*(lower E:ℝ)^(5-2*(7/32:ℝ))*
        (lower G:ℝ)^(2+2*(7/32:ℝ))<I.x^_
    apply (strict_iff hx (by positivity)).mpr
    rw [show 1+2*(7/32:ℝ)=23/16 by norm_num,show 5-2*(7/32:ℝ)=73/16 by norm_num,
      show 2+2*(7/32:ℝ)=39/16 by norm_num]
    have hu23 := Real.rpow_pos_of_pos hu (23/16:ℝ)
    have he73 := Real.rpow_pos_of_pos hE0 (73/16:ℝ)
    have hg39 := Real.rpow_pos_of_pos hG0 (39/16:ℝ)
    simpa only [power_mul (mul_pos (mul_pos hu23 hD0) he73) hg39,
      power_mul (mul_pos hu23 hD0) he73,power_mul hu23 hD0,
      power_rpow hu,power_rpow hE0,power_rpow hG0] using h4

/-- The target threshold precedes every smoothing width, genuine HB mode,
word and choice of the three occupied dyadic modulus intervals. -/
theorem eventually_original_three (K order : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz0 : zeta≤1/20000) (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ (I : Index order zeta kap0),I.P.N=N → I.eta=zeta →
      0≤I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q → I.P.T≤zeta →
      0≤I.P.ell → 2*I.P.ell≤zeta/16 → I.J.length=3 →
      actualPrimeTupleLog I.P.N (ownerHead I.P I.J) 0≤mu →
      ∀ D∈firstOwners I,∀ E∈secondOwners I,∀ G∈thirdOwners I,
      let d := (withOwners I D E G).atom K
      let s := zeta/2000
      d.Q1<d.U*d.scale^(-s) ∧ d.U^2*d.Q2*d.Q3^2<d.scale^(1-8*s) ∧
      (d.residue.natAbs:ℝ)^(7/32:ℝ)*d.U*d.Q1*d.Q2^5*d.Q3^2<d.scale^(2-15*s) ∧
      d.U^(1+2*(7/32:ℝ))*d.Q1*d.Q2^(5-2*(7/32:ℝ))*d.Q3^(2+2*(7/32:ℝ))<d.scale^(2-15*s) := by
  have hke : kappa≤zeta := by linarith
  filter_upwards [P4BOriginalHighRankLiveFibreModes.eventually_fixed_live_window K hz
    (by linarith : zeta≤1/400) hk hke ht ht1,eventually_ge_atTop (2:ℕ)] with N H hN
  intro I hIN hη he hE hq hT hel hel' h3 hlow D hD E hE' G hG
  rw [←hIN] at H hN
  obtain ⟨hx,_,hn,hu,hu',_⟩ := H I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i
    I.C I.live (P4BOriginalMediumFibreSWWindow.first_spec I.selected)
  exact three_at I hη hz hz0 hke hN he hE hq hT hel hel' hx hn hu hu' h3 hlow K D E G hD hE' hG

end
end ImbalancedChen.P4BOriginalMediumLowThreeLengths
