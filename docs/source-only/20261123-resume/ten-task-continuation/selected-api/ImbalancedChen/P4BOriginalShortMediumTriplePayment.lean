import ImbalancedChen.P4BOriginalMediumLowThreeAdmissible
import ImbalancedChen.Part3OriginalSharedPRefinedFamily

/-! SOURCE ONLY / UNCOMPILED.
A low-first three-letter modulus word on the original two-HB-group fibre.
The length cut is on its selected physical HB head. The three occupied
modulus blocks and the small Rosser factor have their original owners. -/
namespace ImbalancedChen.P4BOriginalShortMediumTriplePayment

noncomputable section
open Classical Filter
open scoped BigOperators
open Part3 (MediumAtom MediumAdmissible UniformAuxiliarySW)
open P4BOriginalMediumAtomFamily (Index uniform_original_auxiliary_SW)
open P4BOriginalMediumAtomReconstruction (withOwners)
open P4BOriginalMediumOccupiedLengths (firstOwners secondOwners thirdOwners factor_owner small_rough_owner)
open P4BOriginalMediumTriplePowers
open P4BOriginalMediumLowTriple (actual_third)
open P4BOriginalCollisionTensor (ownerHead)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag)
open P4BUpperSelectedBoxCapacity (endpoint)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)

/-- The endpoint argument for the actual three-prime word is independent
of the HB mother. The assigned lists must partition this very word, and the
third occupied block includes the same physical small Rosser attachment. -/
theorem short_three_owner_lengths (P : P4BOriginalCollisionWords.Params)
    {J : List ℕ} (hJ : J∈P.words) (hN : 1<P.N) (he : 0≤P.e)
    {x U V zeta kappa : ℝ} (hxprod : x=U*V) (hu : 0<U) (hv : 0<V)
    (hz : zeta≤1/20000) (hk : kappa≤zeta) (hx : 1<x) (hNx : (P.N:ℝ)≤x^(1+kappa))
    (hT : P.T≤zeta) (hell : 0≤P.ell) (hell' : 2*P.ell≤zeta/16)
    (h3 : J.length=3) (hl : actualPrimeTupleLog P.N (ownerHead P J) 0≤VariableEnvelope.mu)
    (hshort : U≤x^(1/16:ℝ)) (S : List ℕ × List ℕ × List ℕ)
    (hperm : (S.1++(S.2.1++S.2.2)).Perm J) (D E G : Block)
    (h1 : (lower D:ℝ)≤endpoint (actualPrimeFineLabelIntegerUpper P.N P.T) S.1)
    (h2 : (lower E:ℝ)≤endpoint (actualPrimeFineLabelIntegerUpper P.N P.T) S.2.1)
    (h3' : (lower G:ℝ)≤P.L*endpoint (actualPrimeFineLabelIntegerUpper P.N P.T) S.2.2) :
    (lower D:ℝ)^3*((lower E:ℝ)*(lower G:ℝ))^4≤V^2*x^(-(1/100:ℝ)) := by
  let H := actualPrimeFineLabelIntegerUpper P.N P.T
  let p := ownerHead P J
  let j := fun i : Fin 3 => tag P.N P.T (p i)
  let v := fun i : Fin 3 => (H (j i):ℝ)
  obtain ⟨hword,_,_,_⟩ := actual_third P hN he hJ h3
  change J=[j 0,j 1,j 2] at hword
  obtain ⟨hp,hi,hcube,_⟩ := original_endpoints P hN he hJ h3 hx hNx hk hz hT hl
  change ∀ i : Fin 3,0<v i at hp
  change ∀ i : Fin 3,power x (v i)≤49/250 at hi
  change power x (v 0)+power x (v 1)+3*power x (v 2)≤3/5 at hcube
  have htotal : power x (v 0)+power x (v 1)+power x (v 2)≤173/375 := by
    linarith only [hcube,hi 0,hi 1]
  have hgroup : endpoint H S.1*(endpoint H S.2.1*endpoint H S.2.2)=
      v 0*(v 1*v 2) := by
    have hp' := (hperm.map (fun l => (H l:ℝ))).prod_eq
    rw [hword] at hp'
    simpa only [endpoint,v,List.map_append,List.prod_append,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one] using hp'
  have hd : (0:ℝ)<lower D := by exact_mod_cast lower_pos D
  have he' : (0:ℝ)<lower E := by exact_mod_cast lower_pos E
  have hg : (0:ℝ)<lower G := by exact_mod_cast lower_pos G
  have hP : 0<(P.N:ℝ) := by exact_mod_cast (show 0<P.N by omega)
  have hL : 0<P.L := Real.rpow_pos_of_pos hP _
  have hpowL : power x P.L≤zeta/16 := by
    change power x ((P.N:ℝ)^P.ell)≤_
    rw [power_rpow hP]
    have hbase := (upper_iff hx hP).mp hNx
    have h := mul_le_mul_of_nonneg_left (hbase.trans (by linarith only [hk,hz] : 1+kappa≤2)) hell
    linarith only [h,hell']
  have hprod : (lower D:ℝ)*((lower E:ℝ)*(lower G:ℝ))≤P.L*(v 0*(v 1*v 2)) := by
    calc
      _≤endpoint H S.1*(endpoint H S.2.1*(P.L*endpoint H S.2.2)) :=
        mul_le_mul h1 (mul_le_mul h2 h3' hg.le (he'.le.trans h2))
          (mul_nonneg he'.le hg.le) (hd.le.trans h1)
      _=P.L*(endpoint H S.1*(endpoint H S.2.1*endpoint H S.2.2)) := by ring
      _=_ := by rw [hgroup]
  have hs := power_mono hx (mul_pos hd (mul_pos he' hg)) hprod
  rw [power_mul hd (mul_pos he' hg),power_mul he' hg,
    power_mul hL (mul_pos (hp 0) (mul_pos (hp 1) (hp 2))),
    power_mul (hp 0) (mul_pos (hp 1) (hp 2)),power_mul (hp 1) (hp 2)] at hs
  have hd0 : 0≤power x (lower D) := by
    rw [←power_one x]
    exact power_mono hx zero_lt_one (by exact_mod_cast lower_pos D)
  have hwindow := (upper_iff hx hu).mp hshort
  have huv : power x U+power x V=1 := by
    rw [←power_mul hu hv,←hxprod]
    simpa only [Real.rpow_one] using power_base hx (1:ℝ)
  change (lower D:ℝ)^3*((lower E:ℝ)*(lower G:ℝ))^4≤V^2*x^(-(1/100:ℝ))
  apply (positive_le_iff hx (by positivity) (mul_pos (sq_pos_of_pos hv)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _))).mpr
  rw [power_mul (pow_pos hd 3) (pow_pos (mul_pos he' hg) 4),power_pow,power_pow,
    power_mul he' hg,power_mul (sq_pos_of_pos hv) (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _),
    power_pow,power_base hx]
  push_cast
  linarith only [hs,htotal,hpowL,hz,hd0,hwindow,huv]

/-- The measured whole-word endpoint satisfies the refined shared-first-factor
bound. The repeated third letter in the cube and the small/rough attachment
are both charged before taking powers of the three occupied block lengths. -/
theorem short_three_boundary {order K : ℕ} {zeta kappa kap0 : ℝ}
    (I : Index order zeta kap0) (hN : 1<I.P.N) (he : 0≤I.P.e)
    (hz : zeta≤1/20000) (hk : kappa≤zeta)
    (hx : 1<I.x) (hNx : (I.P.N:ℝ)≤I.x^(1+kappa))
    (hT : I.P.T≤zeta) (hell : 0≤I.P.ell) (hell' : 2*I.P.ell≤zeta/16)
    (h3 : I.J.length=3) (hl : actualPrimeTupleLog I.P.N (ownerHead I.P I.J) 0≤VariableEnvelope.mu)
    (hshort : I.U≤I.x^(1/16:ℝ))
    (D E G : Block) (hD : D∈firstOwners I) (hE : E∈secondOwners I) (hG : G∈thirdOwners I) :
    let d := (withOwners I D E G).atom K
    d.Q1^3*(d.Q2*d.Q3)^4≤d.V^2*d.scale^(-(1/100:ℝ)) := by
  exact short_three_owner_lengths I.P I.word hN he rfl
    (by exact_mod_cast lower_pos (I.bs I.i)) (by exact_mod_cast lower_pos I.C)
    hz hk hx hNx hT hell hell' h3 hl hshort I.groups
    (P4AOriginalFiniteFallbackGroupedAtoms.partition I.P.m I.P.N _ _ _ I.x I.U I.eta
      (ownerHead I.P I.J) I.J (Finset.mem_filter.mp I.word).2)
    D E G (factor_owner I hD) (factor_owner I hE) (small_rough_owner I hG)

/-- Arbitrary logarithmic accuracy on each native complex signed atom in
this subfamily. One physical-N threshold precedes the policy, pair chart,
selected slot, complementary owner, twist, word and three modulus owners. -/
theorem eventually_short_three_signed (K order : ℕ) (A : ℝ) (hA : 0<A)
    {zeta kappa kap0 : ℝ} (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,∀ I : Index order zeta kap0,
      I.P.N=N → I.eta=zeta → 0≤I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q →
      I.P.T≤zeta → 0≤I.P.ell → 2*I.P.ell≤zeta/16 → I.J.length=3 →
      actualPrimeTupleLog I.P.N (ownerHead I.P I.J) 0≤VariableEnvelope.mu →
      I.U≤I.x^(1/16:ℝ) →
      ∀ D∈firstOwners I,∀ E∈secondOwners I,∀ G∈thirdOwners I,
        ‖((withOwners I D E G).atom K).signedError‖≤C*I.x/(Real.log I.x)^A := by
  have hz1 : zeta≤1/400 := by linarith
  have hke : kappa≤zeta := by linarith
  let T := { i : Index order zeta kap0 //
    MediumAdmissible 12 (zeta/2000) kappa (1/Real.exp 1) (i.atom K) }
  let F : T→MediumAtom := fun i => i.val.atom K
  have sw : UniformAuxiliarySW F 1 := by
    intro B hB
    obtain ⟨C,hC,x0,hx0,H⟩ := uniform_original_auxiliary_SW K order hz hz1 hk hke ht ht1 B hB
    exact ⟨C,hC,x0,hx0,fun i hi => H i.val hi⟩
  obtain ⟨C,hC,x0,_,H⟩ :=
    Part3.OriginalSharedPRefinedFamily20261026b.uniformAuxiliarySW_refined_shared_boundary_signedError
      F 12 1 (zeta/2000) kappa (1/Real.exp 1) (1/100)
      (by positivity) (by linarith) (by positivity) hk.le (by linarith only [hkz])
      (by norm_num) (fun i => i.property) sw A hA
  refine ⟨C,hC,?_⟩
  filter_upwards [P4BOriginalMediumLowThreeAdmissible.eventually_original_admissible
      K order hz hz0 hk hkz ht ht1,
    P4BOriginalMediumFibreSWWindow.eventually_window K order x0 hz hz1 hk hke ht ht1,
    P4BOriginalHighRankLiveFibreModes.eventually_fixed_live_window K hz hz1 hk hke ht ht1,
    eventually_ge_atTop (2:ℕ)] with N Hlic HW HL hN
  intro I hIN hEta he he' hq hT hell hell' h3 hl hu D hD E hE G hG
  have had := Hlic I hIN hEta he he' hq hT hell hell' h3 hl D hD E hE G hG
  rw [←hIN] at HW HL hN
  have hs := P4BOriginalMediumFibreSWWindow.first_spec I.selected
  have hw := HW I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hs
  have htarg := HL I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hs
  let t : T := ⟨withOwners I D E G,had⟩
  exact H t hw.1 (short_three_boundary I (by omega) he hz0 hke hw.2.1 htarg.2.2.1
    hT hell hell' h3 hl hu D E G hD hE hG)

end
end ImbalancedChen.P4BOriginalShortMediumTriplePayment
