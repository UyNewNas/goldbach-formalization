import ImbalancedChen.P4BOriginalHighRankComplementBlocks

/-! Remove an empty complementary fibre only after its original inverse
Fourier integral is restored. A live point licenses the complete fixed
(x,U) for its entire fibre. -/
namespace ImbalancedChen.P4BOriginalHighRankLiveFibreModes
noncomputable section
open Classical Filter MeasureTheory
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open P5Z.ActualAllRankOccurrenceFourierBridge
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots)
open P5Z.ActualRoughHeathBrownWords
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalChartRoughCutoff (roughF)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualHBMediumBranchPartition (firstMedium)
open P4BUpperPairOrderedRowGeometry (integerProfile blockScales)
open P4BUpperPairOrderedRowModes (amplitude amplitude_mode_integrable integerProfile_fourier)
open P4BOriginalHighRankComplementBlocks (fibre same_scale)
open P4BOuterRampRoughness (baseline)

variable {u v : ℕ}

theorem fibre_integral {b kap s : ℝ} (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N : ℕ) (kap0 : ℝ) (cj ck : ℕ) (bs : Fin (u+v)→Block) (i : Fin (u+v)) (C : Block)
    (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role) (Q : Finset ℕ) (rho : ℕ→ℂ) :
    (∫ xi,amplitude b kap s N kap0 cj ck bs xi*
      MellinInsertion20261028.exactDiscrepancy (fibre bs i C) Q rho completeProduct N
        (fun y => hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi))=
    MellinInsertion20261028.exactDiscrepancy (fibre bs i C) Q rho completeProduct N
      (fun y => hbSlots Z ys rs y*(integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y:ℂ)) := by
  have hG : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  let E := fibre bs i C
  let kernel := fun y : Fin (u+v)→ℕ =>
    ∑ d∈Q,rho d*MellinInsertion20261028.residueKernel d N (completeProduct y)
  let A := amplitude (a:=u) (d:=v) b kap s N kap0 cj ck bs
  let W := fun xi (y : Fin (u+v)→ℕ) => A xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)
  have int (y : Fin (u+v)→ℕ) : Integrable (fun xi => W xi y) := by
    have h := (amplitude_mode_integrable hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
      hs hG N kap0 cj ck bs y).const_mul (hbSlots Z ys rs y)
    exact h.congr (Eventually.of_forall (fun xi => by dsimp [W,A]; ring))
  calc
    _=∫ xi,MellinInsertion20261028.functional E kernel (W xi) := by
      congr 1
      funext xi
      change A xi*MellinInsertion20261028.functional E kernel
        (fun y => hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)=
        MellinInsertion20261028.functional E kernel
          (fun y => A xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi))
      rw [MellinInsertion20261028.functional_mul]
    _=MellinInsertion20261028.functional E kernel (fun y => ∫ xi,W xi y) :=
      (MellinInsertion20261028.functional_integral E kernel W (fun y _ => int y)).symm
    _=_ := by
      change MellinInsertion20261028.functional E kernel (fun y => ∫ xi,W xi y)=
        MellinInsertion20261028.functional E kernel
          (fun y => hbSlots Z ys rs y*(integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y:ℂ))
      unfold MellinInsertion20261028.functional
      apply Finset.sum_congr rfl
      intro y hy
      have hrect : y∈rectangle bs := (Finset.mem_filter.mp hy).1
      have h := integerProfile_fourier hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
        hs hG N kap0 cj ck bs hrect
      have he : (∫ xi,W xi y)=hbSlots Z ys rs y*
          (integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y:ℂ) := by
        rw [h,←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun xi => by dsimp [W,A]; ring)
      rw [he]

theorem dead_fibre_integral {b kap s : ℝ} (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N : ℕ) (kap0 : ℝ) (cj ck : ℕ) (bs : Fin (u+v)→Block) (i : Fin (u+v)) (C : Block)
    (hdead : ¬∃ y∈fibre bs i C,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0)
    (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role) (Q : Finset ℕ) (rho : ℕ→ℂ) :
    (∫ xi,amplitude b kap s N kap0 cj ck bs xi*
      MellinInsertion20261028.exactDiscrepancy (fibre bs i C) Q rho completeProduct N
        (fun y => hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi))=0 := by
  rw [fibre_integral hb hs hg]
  unfold MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
  apply Finset.sum_eq_zero
  intro y hy
  have h0 : integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y=0 := by
    by_contra h
    exact hdead ⟨y,hy,h⟩
  simp only [h0,Complex.ofReal_zero,mul_zero,zero_mul]

/-- The same local scale and rough cutoff license every test on a fixed
occupied fibre, including its terms at zeros of the original profile. -/
theorem eventually_fixed_live_window (K : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (u v cj ck : ℕ) (bs : Fin (u+v)→Block) (i : Fin (u+v)) (C : Block),
      (∃ y∈fibre bs i C,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0) →
      firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
        (List.ofFn bs)=some i.val →
      let U := (lower (bs i):ℝ)
      let x := U*(lower C:ℝ)
      1<x ∧ x^(1-zeta)≤N ∧ (N:ℝ)≤x^(1+kappa) ∧ x^(2*zeta)≤U ∧ U≤x^(1/3+zeta/2:ℝ) ∧
      roughF x≤beforeHBCutoff K [cj,ck] ∧ beforeHBCutoff K [cj,ck]≤x^(2/(Real.log (Real.log x))^3) := by
  filter_upwards [P4BOriginalHighRankMediumScale.eventually_live_medium K hz hz1 hk hkz ht ht1] with N H
  intro b kap s hb hp hs hg u v cj ck bs i C hLive hsel
  obtain ⟨y,hy,hnz⟩ := hLive
  have hv := H hb hp hs hg u v cj ck bs y i (Finset.mem_filter.mp hy).1 hnz hsel
  simpa only [same_scale hy] using hv

end
end ImbalancedChen.P4BOriginalHighRankLiveFibreModes
