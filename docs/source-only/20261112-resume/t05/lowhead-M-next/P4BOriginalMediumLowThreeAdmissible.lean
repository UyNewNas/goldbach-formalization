import ImbalancedChen.P4BOriginalMediumLowThreeLengths

/-! The literal Part 3 licence on the occupied three-prime subfamily. -/
namespace ImbalancedChen.P4BOriginalMediumLowThreeAdmissible
noncomputable section
open Filter
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P4BOriginalMediumAtomFamily (Index factor_bounds)
open P4BOriginalMediumAtomReconstruction (withOwners)
open P4BOriginalMediumOccupiedLengths (firstOwners secondOwners thirdOwners)
open P4BOriginalCollisionTensor (ownerHead)

theorem eventually_original_admissible (K order : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz0 : zeta≤1/20000) (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ (I : Index order zeta kap0),I.P.N=N → I.eta=zeta →
      0≤I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q → I.P.T≤zeta →
      0≤I.P.ell → 2*I.P.ell≤zeta/16 → I.J.length=3 →
      actualPrimeTupleLog I.P.N (ownerHead I.P I.J) 0≤VariableEnvelope.mu →
      ∀ D∈firstOwners I,∀ E∈secondOwners I,∀ G∈thirdOwners I,
        Part3.MediumAdmissible 12 (zeta/2000) kappa (1/Real.exp 1) ((withOwners I D E G).atom K) := by
  have hz1 : zeta≤1/400 := by linarith
  have hke : kappa≤zeta := by linarith
  filter_upwards [P4BOriginalMediumLowThreeLengths.eventually_original_three K order hz hz0 hk hkz ht ht1,
    P4BOriginalMediumFibreSWWindow.eventually_window K order (Real.exp (Real.exp 1)+1) hz hz1 hk hke ht ht1,
    P4BOriginalHighRankLiveFibreModes.eventually_fixed_live_window K hz hz1 hk hke ht ht1]
    with N HA HW HS
  intro I hN hη he he' hq hT hel hel' h3 hl D hD E hE G hG
  obtain ⟨h1,h2,h3',h4⟩ := HA I hN hη he he' hq hT hel hel' h3 hl D hD E hE G hG
  rw [←hN] at HW HS
  have hf := P4BOriginalMediumFibreSWWindow.first_spec I.selected
  obtain ⟨hB,_,_,_,hU,_,_,hZ,_⟩ := HW I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hf
  have hNx := (HS I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hf).2.2.1
  let T := withOwners I D E G
  have hp (F : Block) : (1:ℝ)≤lower F := by exact_mod_cast lower_pos F
  have hNx' : (1/Real.exp 1)*I.x≤I.P.N := by
    calc
      _≤(1/Real.exp 1)*(Real.exp 1*I.P.N) :=
        mul_le_mul_of_nonneg_left I.scale_upper (by positivity)
      _=(I.P.N:ℝ) := by rw [←mul_assoc,div_mul_cancel₀ _ (Real.exp_pos 1).ne',one_mul]
  refine ⟨hU.le,hp I.C,hp D,hp E,hp G,by change Real.exp (Real.exp 1)<I.x; linarith only [hB],
    hNx',hNx,h1,h2,h3',h4,?_,?_,?_,?_,?_,?_⟩
  · intro n _
    exact P4BOriginalMediumHBHead.alpha_one _ _ _ _ _ n
  · intro n _ hn p hp' hd
    exact hZ.trans_lt (P4BOriginalMediumHBHead.alpha_rough hn p hp' hd)
  · exact fun _ hn => T.atom_beta_bound K hn
  · exact fun q _ => (factor_bounds T K q).1
  · exact fun q _ => (factor_bounds T K q).2.1
  · exact fun q _ => (factor_bounds T K q).2.2

end
end ImbalancedChen.P4BOriginalMediumLowThreeAdmissible
