import ImbalancedChen.P1OriginalSingletonMediumLowThreeAdmissible
import ImbalancedChen.P4AOriginalFiniteFallbackCommonGroups

/-!
SOURCE ONLY / NOT COMPILED.

The actual singleton row family consumes the existing generic high-first
and raised low-first endpoint providers. The only newly unbound geometric
caller is the low-first triple bridge imported above. The complete modulus
grouping is fixed before its integer tuples and discrepancy signs.
-/
namespace ImbalancedChen.P1OriginalSingletonMediumAdmissible
noncomputable section
open Classical Filter
open P1OriginalSingletonMediumLowThreeAdmissible (Index size)
open Part3 (MediumAdmissible UniformAuxiliarySW)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (ownerHead)
open P4BOriginalCollisionThirdFactor (splitAt thirdSupport)
open P4BOriginalMediumAtomFamily (support)
open P5Z.HBRightClosedDyadicRoles (Block owner)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P4BOriginalMediumTripleOccupiedBridge (factor_owner third_owner)
open P4BOriginalHigherLowRepresentative (d t g primeWord front_eq length_word)
open P4BOriginalMediumLowTriple (representative_raw)
open P4BOriginalHigherActionKeys (localE)
open P4AOriginalFiniteFallbackCommonGroups (gap groupsAt)
open P4AOriginalFiniteFallbackGroupedAtoms (sizes)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AHeldTaggedCompilerSupport (J0)
open P1OriginalSingletonMediumWindow (eventually_original_medium_window)
open P1OriginalSingletonMediumAuxiliarySW (eventually_actual_singleton_row)

/-- The high-first and higher low-first portions of the actual singleton
family. The upper endpoints are supplied by the original physical policy,
then decreased to the actual occupied dyadic owners. -/
theorem eventually_high_or_higher_low (K modeOrder : ℕ) {kap zeta kappa kap0 : ℝ}
    (hkap : kap<1) (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ I : Index modeOrder kap zeta kap0,I.P.N=N →
      0<I.P.e → (I.P.e:ℝ)≤1/2048 → zeta≤localE I.P/512 →
      logPrimeMeshStep 0 (19/96) (d I.P).m≤(I.P.e:ℝ)/20 →
      0<I.P.omega → zeta≤gap I.P.m (d I.P) →
      I.P.T*((J0 I.P.omega:ℝ)+1)≤zeta → 0≤I.P.ell → 2*I.P.ell≤zeta/16 →
      (VariableEnvelope.mu<t I.P I.J 0 ∨ 4≤I.J.length) →
      ∀ D∈I.firstOwners,∀ E∈I.secondOwners,∀ G∈I.thirdOwners,
        MediumAdmissible 6 (zeta/2000) kappa (1/2) (I.atom K D E G) := by
  have hz1 : zeta≤1/400 := by linarith
  have hk1 : kappa≤1 := by linarith
  have hke : kappa≤zeta := by linarith
  filter_upwards [eventually_original_medium_window K (Real.exp (Real.exp 1)+1)
      hkap hz hz1 hk ht ht1,
    (eventually_actual_singleton_row K modeOrder 0 (le_refl (0:ℝ))
      hkap hz hz1 hk hk1 ht ht1).choose_spec.2,
    eventually_ge_atTop (2:ℕ)] with N HW HS hNN
  intro I hN he he' hzE step ho hgap hbudget hell hell' hcase D hD E hE G hG
  rw [←hN] at HW HS hNN
  obtain ⟨hLarge,hx,hRes,hNx,hlo,hU,hUlo,hUhi,_,_,_,_,_⟩ :=
    HW I.cj (size I.j) I.bv I.i I.C I.live I.selected_ofFn
  obtain ⟨hAlpha,hRough,_⟩ := HS I.cj I.j.val I.bs I.row I.i I.C
    I.live I.selected I.xi I.band
  have hx0 := zero_lt_one.trans hx
  have hnR : 0<(I.P.N:ℝ) := by exact_mod_cast I.N_pos
  have hu := zero_lt_one.trans hU
  have hhi : (I.P.N:ℝ)≤I.x^(1+zeta) := hNx.trans
    (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [hke]))
  let H := actualPrimeFineLabelIntegerUpper I.P.N I.P.T
  let S := I.groups
  let a := P4BUpperSelectedBoxCapacity.endpoint H S.1
  let b := P4BUpperSelectedBoxCapacity.endpoint H S.2.1
  let c := P4BUpperSelectedBoxCapacity.endpoint H S.2.2*I.x^(2*I.P.ell)
  have targets :
      a<I.U*I.x^(-zeta/100) ∧ I.U^2*b*c^2<I.x^(1-8*(zeta/100)) ∧
      I.x^(7/32:ℝ)*I.U*a*b^5*c^2<I.x^(2-15*(zeta/100)) ∧
      I.U^(23/16:ℝ)*a*b^(73/16:ℝ)*c^(39/16:ℝ)<I.x^(2-15*(zeta/100)) := by
    by_cases hhigh : VariableEnvelope.mu<t I.P I.J 0
    · have off : I.groups=splitAt I.P I.x I.U zeta I.J :=
        P4BOriginalHigherActionFamily.off_low I.P I.x I.U zeta I.J (Or.inr hhigh)
      have hr := representative_raw I.P (by omega) I.word
      have hlen : 3≤(primeWord I.P I.J).length := by
        rw [length_word I.P (by omega) I.word]
        exact (Finset.mem_filter.mp I.word).2
      have hfront : (g I.P I.J).primeFactorsList.reverse=
          P4AOriginalFiniteFallbackSelectedMask.front (ownerHead I.P I.J)
            ((g I.P I.J).primeFactorsList.reverse.drop 3) :=
        (front_eq (primeWord I.P I.J) hlen).symm
      -- Read a genuine small factor from this occupied third owner.
      change G∈(thirdSupport I.P I.J I.groups.2.2).image owner at hG
      obtain ⟨q,hq,_⟩ := Finset.mem_image.mp hG
      obtain ⟨⟨small,rough⟩,hpair,_⟩ := Finset.mem_image.mp hq
      have hsmall := (Finset.mem_filter.mp (Finset.mem_product.mp hpair).1).2
      have hbeta : (small:ℝ)<I.P.L := by
        unfold Params.small P4AOriginalFiniteFallbackGroupedAtoms.beta at hsmall
        split_ifs at hsmall
        · exact (actualSmallRosserPlus_active hsmall).2.1
        · exact (actualSmallRosserMinus_active hsmall).2.1
      have HM := P4AOriginalFiniteFallbackCommonGroups.high I.P.m I.P.n I.P.N I.P.N
        (g I.P I.J) (g I.P I.J) small (width I.P.r) I.P.omega I.P.T I.P.ell (d I.P)
        (width_pos _) he.le (by omega) ho I.P.T_pos hz hgap hbudget hr.1 rfl hbeta hell hell'
        (ownerHead I.P I.J) _ hfront hhigh hx (by linarith : (0:ℝ)≤zeta)
        hlo hhi hUlo hUhi
      have hs := sizes I.P.m I.P.N (d I.P) I.P.omega I.P.T I.x I.U zeta
        (ownerHead I.P I.J) I.J
      rw [hr.2] at HM
      rw [hs] at HM
      simpa only [a,b,c,H,S,off,splitAt,show (7*(1+3*(0:ℝ))/32)=7/32 by norm_num] using HM.2
    · have h4 : 4≤I.J.length := hcase.resolve_left hhigh
      exact P4BOriginalHigherActionGroups.endpoints I.P (by omega) he he' step ho I.word
        h4 (le_of_not_gt hhigh) hx hz hzE hbudget hlo hhi hUlo hUhi hell'
  obtain ⟨h1,h2,h3,h4⟩ := targets
  have a1 : (lower D:ℝ)≤a := factor_owner I.P I.groups.1 hD
  have a2 : (lower E:ℝ)≤b := factor_owner I.P I.groups.2.1 hE
  have a3 : (lower G:ℝ)≤c := by
    apply (third_owner I.P I.J I.groups.2.2 hG).trans
    have hL : I.P.L≤I.x^(2*I.P.ell) := by
      apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hhi hell).trans
      rw [←Real.rpow_mul hx0.le]
      apply Real.rpow_le_rpow_of_exponent_le hx.le
      nlinarith only [mul_nonneg hell (show 0≤1-zeta by linarith)]
    change I.P.L*P4BUpperSelectedBoxCapacity.endpoint H S.2.2≤_
    rw [mul_comm I.P.L]
    exact mul_le_mul_of_nonneg_left hL
      (by rw [P4BUpperSelectedBoxCapacity.endpoint_eq_cast]; positivity)
  have hdP : (0:ℝ)<lower D := by exact_mod_cast lower_pos D
  have heP : (0:ℝ)<lower E := by exact_mod_cast lower_pos E
  have hgP : (0:ℝ)<lower G := by exact_mod_cast lower_pos G
  have mov : (I.P.N:ℝ)^(7/32:ℝ)≤I.x^(7*kappa/32)*I.x^(7/32:ℝ) := by
    apply (Real.rpow_le_rpow hnR.le hNx (by norm_num : (0:ℝ)≤7/32)).trans_eq
    rw [←Real.rpow_mul hx0.le,←Real.rpow_add hx0]
    congr 1 <;> ring
  have m3 : (I.P.N:ℝ)^(7/32:ℝ)*I.U*(lower D:ℝ)*(lower E:ℝ)^5*(lower G:ℝ)^2<I.x^(2-15*(zeta/2000)) := by
    calc
      _≤(I.x^(7*kappa/32)*I.x^(7/32:ℝ))*I.U*a*b^5*c^2 := by gcongr
      _=I.x^(7*kappa/32)*(I.x^(7/32:ℝ)*I.U*a*b^5*c^2) := by ring
      _<I.x^(7*kappa/32)*I.x^(2-15*(zeta/100)) :=
        mul_lt_mul_of_pos_left h3 (Real.rpow_pos_of_pos hx0 _)
      _≤_ := by
        rw [←Real.rpow_add hx0]
        apply Real.rpow_le_rpow_of_exponent_le hx.le
        linarith only [hkz,hz]
  have hp (B : Block) : (1:ℝ)≤lower B := by exact_mod_cast lower_pos B
  refine ⟨hU.le,hp I.C,hp D,hp E,hp G,?_,?_,hNx,?_,?_,m3,?_,?_,?_,?_,?_,?_,?_⟩
  · change Real.exp (Real.exp 1)<I.x
    linarith only [hLarge]
  · simpa only [one_div] using hRes
  · exact (a1.trans_lt h1).trans_le (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) hu.le)
  · change I.U^2*(lower E:ℝ)*(lower G:ℝ)^2<_
    apply lt_of_le_of_lt (show _≤I.U^2*b*c^2 by gcongr)
    exact h2.trans_le (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  · change I.U^(1+2*(7/32:ℝ))*(lower D:ℝ)*(lower E:ℝ)^(5-2*(7/32:ℝ))*
      (lower G:ℝ)^(2+2*(7/32:ℝ))<_
    rw [show 1+2*(7/32:ℝ)=23/16 by norm_num,show 5-2*(7/32:ℝ)=73/16 by norm_num,
      show 2+2*(7/32:ℝ)=39/16 by norm_num]
    apply lt_of_le_of_lt (show _≤I.U^(23/16:ℝ)*a*b^(73/16:ℝ)*c^(39/16:ℝ) by gcongr <;> norm_num)
    exact h4.trans_le (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  · exact fun n _ => hAlpha n
  · exact fun n _ hn p hp hd => hRough n hn p hp hd
  · exact fun m hm => I.beta_bound K D E G hm
  · exact fun q _ => (I.factor_bounds K D E G q).1
  · exact fun q _ => (I.factor_bounds K D E G q).2.1
  · exact fun q _ => (I.factor_bounds K D E G q).2.2

/-- Exhaust the actual P.words bank. Its raw rank is at least three;
the only split is the fixed raw representative's first coordinate. -/
theorem eventually_original_admissible (K modeOrder : ℕ) {kap zeta kappa kap0 : ℝ}
    (hkap : kap<1) (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ I : Index modeOrder kap zeta kap0,I.P.N=N →
      0<I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q → zeta≤localE I.P/512 →
      logPrimeMeshStep 0 (19/96) (d I.P).m≤(I.P.e:ℝ)/20 →
      0<I.P.omega → zeta≤gap I.P.m (d I.P) →
      I.P.T*((J0 I.P.omega:ℝ)+1)≤zeta → 0≤I.P.ell → 2*I.P.ell≤zeta/16 →
      ∀ D∈I.firstOwners,∀ E∈I.secondOwners,∀ G∈I.thirdOwners,
        MediumAdmissible 6 (zeta/2000) kappa (1/2) (I.atom K D E G) := by
  filter_upwards [P1OriginalSingletonMediumLowThreeAdmissible.eventually_low_three K modeOrder
      hkap hz hz0 hk hkz ht ht1,
    eventually_high_or_higher_low K modeOrder hkap hz hz0 hk hkz ht ht1] with N HT HH
  intro I hN he he' hq hzE step ho hgap hbudget hell hell' D hD E hE G hG
  by_cases hhigh : VariableEnvelope.mu<t I.P I.J 0
  · exact HH I hN he he' hzE step ho hgap hbudget hell hell' (Or.inl hhigh) D hD E hE G hG
  · by_cases h3 : I.J.length=3
    · have hT : I.P.T≤zeta := by
        have hJ : (1:ℝ)≤(J0 I.P.omega:ℝ)+1 := by positivity
        exact (le_mul_of_one_le_right I.P.T_pos.le hJ).trans hbudget
      exact HT I hN he.le he' hq hT hell hell' h3 (le_of_not_gt hhigh) D hD E hE G hG
    · have hr : 3≤I.J.length := (Finset.mem_filter.mp I.word).2
      exact HH I hN he he' hzE step ho hgap hbudget hell hell' (Or.inr (by omega)) D hD E hE G hG

/-- The geometric licence and actual all-k/q auxiliary SW share one
physical-N threshold. The same alpha interval and exact coprime mean are
used. This statement does not assume or conclude the signed M estimate. -/
theorem eventually_original_with_auxiliary (K modeOrder : ℕ) (A : ℝ) (hA : 0<A)
    {kap zeta kappa kap0 : ℝ} (hkap : kap<1) (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∃ Csw : ℝ,0<Csw ∧ ∀ᶠ N : ℕ in atTop,
      ∀ I : Index modeOrder kap zeta kap0,I.P.N=N →
      0<I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q → zeta≤localE I.P/512 →
      logPrimeMeshStep 0 (19/96) (d I.P).m≤(I.P.e:ℝ)/20 →
      0<I.P.omega → zeta≤gap I.P.m (d I.P) →
      I.P.T*((J0 I.P.omega:ℝ)+1)≤zeta → 0≤I.P.ell → 2*I.P.ell≤zeta/16 →
      ∀ D∈I.firstOwners,∀ E∈I.secondOwners,∀ G∈I.thirdOwners,
      MediumAdmissible 6 (zeta/2000) kappa (1/2) (I.atom K D E G) ∧
      ∀ k q residue : ℕ,1≤k → 1≤q → residue.Coprime q →
        ‖(I.atom K D E G).auxSWError k q residue‖≤
          Csw*I.U*(k.divisors.card:ℝ)/(Real.log I.x)^A := by
  have hz1 : zeta≤1/400 := by linarith
  have hk1 : kappa≤1 := by linarith
  obtain ⟨Csw,hC,x0,_,HS⟩ :=
    P1OriginalSingletonMediumLowThreeAdmissible.uniform_auxiliary K modeOrder
      hkap hz hz1 hk hk1 ht ht1 A hA
  refine ⟨Csw,hC,?_⟩
  filter_upwards [eventually_original_admissible K modeOrder hkap hz hz0 hk hkz ht ht1,
    eventually_original_medium_window K x0 hkap hz hz1 hk ht ht1] with N HA HW
  intro I hN he he' hq hzE step ho hgap hbudget hell hell' D hD E hE G hG
  refine ⟨HA I hN he he' hq hzE step ho hgap hbudget hell hell' D hD E hE G hG,?_⟩
  have hx : x0≤I.x := by
    rw [←hN] at HW
    exact (HW I.cj (size I.j) I.bv I.i I.C I.live I.selected_ofFn).1
  intro k q residue hk' hq' hr
  simpa only [pow_one] using HS (I,D,E,G) hx k q residue hk' hq' hr

end
end ImbalancedChen.P1OriginalSingletonMediumAdmissible
