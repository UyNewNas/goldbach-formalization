import ImbalancedChen.P4AOriginalEarlySumComparison
import ImbalancedChen.P4AOriginalFiniteAll22RawLedger

namespace ImbalancedChen.P4AOriginalEarlyFinitePayment
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P4AOriginalEarlyHistoricalFloors (slots gain historical_payment)
open P4AOriginalEarlyTupleCarriers (Alignment)
open P4AOriginalEarlyTupleComparison (PlusShift MinusShift)
open P4AOriginalEarlySumComparison (M fixed_mass same_target)
open P4AOriginalFull87JointPhysicalBudget (cutoff_le_target)
open P4AOriginalFiniteAll22RawLedger (lowerEarly lowerEarlySlots lowerEarlyDefect lowStage_zero)

/-- Literal indices 0, 1 and 2 on the finite-dispatch coefficient. The
archive mesh and both historical cutoffs are fixed before the target.
The same n and q work for every physical cutoff w≤a. -/
theorem original_low_early_payment (eps : ℝ) (heps : 0<eps) :
    ∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<e → (e:ℝ)<E →
    ∀ a : ℝ,0<a → a≤1/800 → ∀ qMin mMin : ℕ,∃ q0 : ℕ,0<q0 ∧ qMin≤q0 ∧
    ∀ k : ℕ,0<k → q0≤256*k → mMin≤refinedMesh (256*k) ∧
    ∃ N0 : ℕ,2≤N0 ∧ ∀ w : ℝ,w≤a → ∀N≥N0,Even N →
      lowerEarlySlots-eps<lowerEarly n e (256*k) a w N := by
  obtain ⟨C4,hC4,HM4⟩ := fixed_mass 4
  obtain ⟨C5,hC5,HM5⟩ := fixed_mass 5
  let u := eps/(4*(C4+2*C5+1))
  have hD : 0<C4+2*C5+1 := by positivity
  have hu : 0<u := by dsimp [u]; positivity
  have hbudget : u*C4+2*u*C5<eps/2 := by
    have hi : u*(C4+2*C5+1)=eps/4 := by
      dsimp [u]; field_simp [hD.ne'] <;> ring
    linarith only [hi,hu,heps]
  obtain ⟨n4,hn4⟩ := P4AOriginalEarlyMovingPlus.compact_fourth_shift u hu
  obtain ⟨n5,hn5⟩ := P4AOriginalEarlyMovingMinus.compact_fifth_shift u hu
  obtain ⟨E0,hE0,H0⟩ := historical_payment (eps/2) (half_pos heps)
  refine ⟨max n4 n5,?_⟩
  intro n hn
  obtain ⟨N4,hN4,H4⟩ := hn4 n ((le_max_left _ _).trans hn)
  obtain ⟨N5,hN5,H5⟩ := hn5 n ((le_max_right _ _).trans hn)
  refine ⟨min E0 (1/20000),lt_min hE0 (by norm_num),?_⟩
  intro e he hE a ha haa qMin mMin
  have heR : 0<(e:ℝ) := by exact_mod_cast he
  have he' := hE.trans_le (min_le_right _ _)
  obtain ⟨q0,hq0,hmin,Hq⟩ := H0 e heR (hE.trans_le (min_le_left _ _)) a ha haa qMin mMin
  refine ⟨q0,hq0,hmin,?_⟩
  intro k hk hq
  obtain ⟨hm,hstep,Hfloor⟩ := Hq (256*k) hq
  obtain ⟨NM,HM⟩ := eventually_atTop.mp (HM4.and (HM5.and Hfloor))
  refine ⟨hm,max NM (max N4 N5),hN4.trans ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro w hw N hN hEven
  have hm' := HM N ((le_max_left _ _).trans hN)
  have hn4' := (le_max_left N4 N5).trans ((le_max_right _ _).trans hN)
  have hn5' := (le_max_right N4 N5).trans ((le_max_right _ _).trans hN)
  have hn' : 1<N := by omega
  have cover := cutoff_le_target N (by exact_mod_cast hn'.le)
  have h4 : PlusShift n N u := H4 N hn4' hEven N cover
  have h5 : MinusShift n N u := H5 N hn5' hEven N cover
  have alg : Alignment e k a w := ⟨hk,heR.le,by linarith,hstep,haa.trans (by norm_num),hw⟩
  have hcomp := same_target alg (by linarith) hu.le hn' h4 h5
  have m4 := mul_le_mul_of_nonneg_left hm'.1 hu.le
  have m5 := mul_le_mul_of_nonneg_left hm'.2.1 (show 0≤2*u by linarith)
  have hfloor := hm'.2.2 hEven
  rw [lowerEarly,lowStage_zero]
  change slots-eps<_
  linarith only [hfloor,hcomp,m4,m5,hbudget]

/-- The remainder used by the existing All22 telescope is genuinely
smaller than eps on a cofinal choice of q after every other lower bound. -/
theorem cofinal_actual_early_defect (eps : ℝ) (heps : 0<eps) :
    ∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<e → (e:ℝ)<E →
    ∀a : ℝ,0<a → a≤1/800 → ∀qMin mMin : ℕ,∃ q : ℕ,qMin≤q ∧ 0<q ∧ 256∣q ∧
      mMin≤refinedMesh q ∧ ∃ N0 : ℕ,2≤N0 ∧ ∀w : ℝ,w≤a → ∀N≥N0,Even N →
        lowerEarlyDefect n e q a w N<eps := by
  obtain ⟨n0,H⟩ := original_low_early_payment eps heps
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨E,hE,HE⟩ := H n hn
  refine ⟨E,hE,?_⟩
  intro e he heE a ha haa qMin mMin
  obtain ⟨q0,hq0,hmin,Q⟩ := HE e he heE a ha haa qMin mMin
  have hq : q0≤256*q0 := by omega
  obtain ⟨hm,N0,hN0,HN⟩ := Q q0 hq0 hq
  refine ⟨256*q0,hmin.trans hq,by omega,⟨q0,rfl⟩,hm,N0,hN0,?_⟩
  intro w hw N hN hEven
  unfold lowerEarlyDefect
  linarith only [HN w hw N hN hEven]

end
end ImbalancedChen.P4AOriginalEarlyFinitePayment

