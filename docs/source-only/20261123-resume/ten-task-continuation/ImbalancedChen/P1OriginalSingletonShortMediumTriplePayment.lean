import ImbalancedChen.P1OriginalSingletonMediumLowThreeAdmissible
import ImbalancedChen.P4BOriginalShortMediumTriplePayment

/-! The refined shared-first-factor estimate on the actual singleton index,
with the original complete product, group assignment and three occupied
owners. Source only. -/
namespace ImbalancedChen.P1OriginalSingletonShortMediumTriplePayment
noncomputable section
open Classical Filter
open Part3 (MediumAtom MediumAdmissible UniformAuxiliarySW)
open P1OriginalSingletonMediumLowThreeAdmissible (Index size uniform_auxiliary eventually_low_three)
open P1OriginalSingletonMediumWindow (eventually_original_medium_window)
open P4BOriginalCollisionTensor (ownerHead)
open P4BOriginalMediumTripleOccupiedBridge (factor_owner third_owner)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower_pos)

/-- The endpoints come from the very raised-action grouping used by atom,
including its third owner's small prime part. -/
theorem short_three_boundary {order K : ℕ} {kap zeta kappa kap0 : ℝ}
    (I : Index order kap zeta kap0) (hN : 1<I.P.N) (he : 0≤I.P.e)
    (hz : zeta≤1/20000) (hk : kappa≤zeta)
    (hx : 1<I.x) (hNx : (I.P.N:ℝ)≤I.x^(1+kappa))
    (hT : I.P.T≤zeta) (hell : 0≤I.P.ell) (hell' : 2*I.P.ell≤zeta/16)
    (h3 : I.J.length=3) (hl : actualPrimeTupleLog I.P.N (ownerHead I.P I.J) 0≤VariableEnvelope.mu)
    (hshort : I.U≤I.x^(1/16:ℝ))
    (D E G : Block) (hD : D∈I.firstOwners) (hE : E∈I.secondOwners) (hG : G∈I.thirdOwners) :
    let d := I.atom K D E G
    d.Q1^3*(d.Q2*d.Q3)^4≤d.V^2*d.scale^(-(1/100:ℝ)) :=
  P4BOriginalShortMediumTriplePayment.short_three_owner_lengths I.P I.word hN he rfl
    (by exact_mod_cast lower_pos (I.bv I.i)) (by exact_mod_cast lower_pos I.C)
    hz hk hx hNx hT hell hell' h3 hl hshort I.groups
    (P4BOriginalHigherActionGroups.split_perm I.P hN I.x I.U zeta I.word)
    D E G (factor_owner I.P I.groups.1 hD) (factor_owner I.P I.groups.2.1 hE)
    (third_owner I.P I.J I.groups.2.2 hG)

/-- A single physical threshold precedes final P, chart, HB row, selected
slot, complement, frequency, word and all modulus owners. -/
theorem eventually_short_three_signed (K order : ℕ) (A : ℝ) (hA : 0<A)
    {kap zeta kappa kap0 : ℝ} (hkap : kap<1) (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,∀ I : Index order kap zeta kap0,
      I.P.N=N → 0≤I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q →
      I.P.T≤zeta → 0≤I.P.ell → 2*I.P.ell≤zeta/16 → I.J.length=3 →
      actualPrimeTupleLog I.P.N (ownerHead I.P I.J) 0≤VariableEnvelope.mu →
      I.U≤I.x^(1/16:ℝ) →
      ∀ D∈I.firstOwners,∀ E∈I.secondOwners,∀ G∈I.thirdOwners,
        ‖(I.atom K D E G).signedError‖≤C*I.x/(Real.log I.x)^A := by
  have hz1 : zeta≤1/400 := by linarith
  have hk1 : kappa≤1 := by linarith
  have hke : kappa≤zeta := by linarith
  let f := fun p : Index order kap zeta kap0 × Block × Block × Block =>
    p.1.atom K p.2.1 p.2.2.1 p.2.2.2
  let T := {p // MediumAdmissible 6 (zeta/2000) kappa (1/2) (f p)}
  let F : T→MediumAtom := fun t => f t.val
  have sw : UniformAuxiliarySW F 1 := by
    intro a ha
    obtain ⟨C,hC,x0,hx0,H⟩ := uniform_auxiliary K order hkap hz hz1 hk hk1 ht ht1 a ha
    exact ⟨C,hC,x0,hx0,fun t hx => H t.val hx⟩
  obtain ⟨C,hC,x0,_,H⟩ :=
    Part3.OriginalSharedPRefinedFamily20261026b.uniformAuxiliarySW_refined_shared_boundary_signedError
      F 6 1 (zeta/2000) kappa (1/2) (1/100)
      (by positivity) (by linarith) (by norm_num) hk.le (by linarith only [hkz])
      (by norm_num) (fun t => t.property) sw A hA
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_low_three K order hkap hz hz0 hk hkz ht ht1,
    eventually_original_medium_window K x0 hkap hz hz1 hk ht ht1,
    eventually_ge_atTop (2:ℕ)] with N HA HW hNN
  intro I hn he he' hq hT hell hell' h3 hl hu D hD E hE G hG
  rw [←hn] at HW
  obtain ⟨hx0,hx,_,hNx,_⟩ := HW I.cj (size I.j) I.bv I.i I.C I.live I.selected_ofFn
  have hN : 1<I.P.N := by omega
  let t : T := ⟨(I,D,E,G),HA I hn he he' hq hT hell hell' h3 hl D hD E hE G hG⟩
  apply H t
  · exact hx0
  · exact short_three_boundary I hN he hz0 hke hx hNx
      hT hell hell' h3 hl hu D E G hD hE hG

end
end ImbalancedChen.P1OriginalSingletonShortMediumTriplePayment
