import ImbalancedChen.P4AOrderedThirdFixedOmegaLimit
import ImbalancedChen.P5HistoricalRectangularGammaTransport

namespace ImbalancedChen.P4AOrderedThirdCompactComparison
noncomputable section
open Set VariableEnvelope HistoricalThirdCoarse P5HistoricalRectangularGammaTransport
open P4AOriginalOrderedThirdTable (portion infimum full capValue)
open P4AOriginalOrderedThirdAgreement (hi_cast)
open scoped Classical

theorem rational_box {m : ℕ} {j : Cell m} {t : Fin 3 → ℝ} (ht : t∈portion m j) :
    (box m j).InBox (t 0) (t 1) (t 2) := by
  have hlo (i : Fin 3) : (qLogPrimeMeshLo 0 (19/96) m j i:ℝ)=logPrimeMeshLo 0 (19/96) m j i := by
    simpa only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using congrFun (cast_qLogPrimeMeshLo 0 (19/96) m j) i
  have h (i : Fin 3) := ht.1 i (mem_univ _)
  exact ⟨(hlo 0).symm ▸ (h 0).1,(hi_cast m j 0).symm ▸ (h 0).2,
    (hlo 1).symm ▸ (h 1).1,(hi_cast m j 1).symm ▸ (h 1).2,
    (hlo 2).symm ▸ (h 2).1,(hi_cast m j 2).symm ▸ (h 2).2⟩

/-- Shrinking the rectangle to its ordered part can raise the stored infima
and enable an additional pair. A previously enabled whole-rectangle pair
stays enabled even when the three prime coordinates share a coarse label. -/
theorem rectangular_lower {e : ℝ} (he : 0≤e) {m : ℕ} {j : Cell m}
    (hn : (portion m j).Nonempty) :
    (gamma e (box m j):ℝ) ≤ P4AOriginalOrderedThirdTable.envelope e m j := by
  let b := box m j
  have I {f : (Fin 3 → ℝ) → ℝ} {c : ℝ}
      (hc : ∀ s∈portion m j, c≤f s) : c≤infimum m j f := by
    apply le_csInf (hn.image _)
    rintro _ ⟨s,hs,rfl⟩
    exact hc s hs
  have vx : (qVLo b.lx b.ux:ℝ)≤infimum m j (actualExtendedThirdRobustBaseBranch 0) :=
    I (fun s hs => qVLo_le_v (rational_box hs).1 (rational_box hs).2.1)
  have hhigh : logPrimeMeshHi 0 (19/96) m j 0=(b.ux:ℝ) := (hi_cast m j 0).symm
  change (gamma e b:ℝ)≤_
  rw [gamma,P4AOriginalOrderedThirdTable.envelope,hhigh]
  split_ifs with hc
  · have hmu : (b.ux:ℝ)≤mu := by linarith
    have H {f : (Fin 3 → ℝ) → ℝ} {l u : ℚ}
        (hb : ∀ s∈portion m j,(l:ℝ)≤f s ∧ f s≤(u:ℝ)) :
        (qVLo l u:ℝ)≤infimum m j (fun s => v (f s)) :=
      I (fun s hs => qVLo_le_v (hb s hs).1 (hb s hs).2)
    have xy : (qVLo (b.lx+b.ly) (b.ux+b.uy):ℝ)≤infimum m j (actualExtendedThirdRobustBaseBranch 2) := by
      apply H (f:=fun s => s 0+s 1)
      intro s hs; obtain ⟨h1,h2,h3,h4,h5,h6⟩ := rational_box hs
      constructor <;> push_cast <;> linarith
    have xyz : (qVLo (b.lx+b.ly+b.lz) (b.ux+b.uy+b.uz):ℝ)≤infimum m j (actualExtendedThirdRobustBaseBranch 3) := by
      apply H (f:=fun s => s 0+s 1+s 2)
      intro s hs; obtain ⟨h1,h2,h3,h4,h5,h6⟩ := rational_box hs
      constructor <;> push_cast <;> linarith
    have xz : (qVLo (b.lx+b.lz) (b.ux+b.uz):ℝ)≤infimum m j actualExtendedThirdPairXZ := by
      apply H (f:=fun s => s 0+s 2)
      intro s hs; obtain ⟨h1,h2,h3,h4,h5,h6⟩ := rational_box hs
      constructor <;> push_cast <;> linarith
    have yz : (qVLo (b.ly+b.lz) (b.uy+b.uz):ℝ)≤infimum m j actualExtendedThirdPairYZ := by
      apply H (f:=fun s => s 1+s 2)
      intro s hs; obtain ⟨h1,h2,h3,h4,h5,h6⟩ := rational_box hs
      constructor <;> push_cast <;> linarith
    have gx : (xzGap b:ℝ)≤infimum m j actualExtendedThirdGateXZ :=
      I (fun _ hs => xzGap_le (rational_box hs))
    have gy : (yzGap b:ℝ)≤infimum m j actualExtendedThirdGateYZ :=
      I (fun _ hs => yzGap_le (rational_box hs))
    have r : (rescue b:ℝ)≤infimum m j (actualExtendedThirdRobustBaseBranch 4) := by
      apply I
      intro s hs
      have h0 := (rational_box hs).2.1.trans hmu
      change _≤max (v (s 0)) (wInner (s 0) (s 1) (s 2))
      rw [v_eq_A h0,wInner_eq_B _ (hs.2.2.2.trans h0) hs.2.1]
      exact rescue_le (rational_box hs)
    dsimp only [fullGamma,full]
    split_ifs <;> simp only [Rat.cast_max,max_le_iff] <;>
      first | (exfalso; linarith) |
        (repeat' apply And.intro) <;> first |
        exact vx.trans (by simp [le_max_iff]) | exact xy.trans (by simp [le_max_iff]) |
        exact xyz.trans (by simp [le_max_iff]) | exact r.trans (by simp [le_max_iff]) |
        exact xz.trans (by simp [le_max_iff]) | exact yz.trans (by simp [le_max_iff])
  · exact vx

/-- Uniform one-sided error on all cells with an ordered point. -/
theorem cell_lower {e g : ℝ} (he : 0≤e) (hg : 0≤g) {m : ℕ}
    (hw : logPrimeMeshStep 0 (19/96) m≤g) (hf : e+7*g≤3/256) {j : Cell m}
    {t : Fin 3 → ℝ} (ht : t∈portion m j) :
    P4AOriginalHistoricalThirdMajorant.envelope t-(4*e+6*g)≤capValue e m j := by
  let b := box m j
  have hb := rational_box ht
  have hwidth : (b.width:ℝ)≤g := (P4ACatalogFiveHistoricalCoverage.box_width m j).le.trans hw
  have htarget := P4AOriginalHistoricalThirdMajorant.envelope_eq ht.2.1 ht.2.2.1 ht.2.2.2
  have hroot := P4AOriginalHistoricalThirdMajorant.envelope_le t
  have hh := rectangular_lower he (show (portion m j).Nonempty from ⟨t,ht⟩)
  change _≤min (thirdPrefixTheta-2*e) (P4AOriginalOrderedThirdTable.envelope e m j-2*e)
  apply le_min (by linarith)
  rw [htarget,actualExtendedThirdIdealCap_eq]
  by_cases hfull : (b.ux:ℝ)≤mu-4*e
  · have h0 : t 0≤mu := by linarith [hb.2.1]
    have ho : Ordered (t 0) (t 1) (t 2) := ⟨ht.2.1,ht.2.2.1,ht.2.2.2,h0⟩
    have hG := (fullGamma_error e g b hg hwidth hb ho hf).2
    change (gamma e b:ℝ)≤_ at hh
    rw [gamma,if_pos hfull] at hh
    rw [if_pos h0,original_eq_six ho]
    linarith only [min_le_right thirdPrefixTheta (six (t 0) (t 1) (t 2)),hG,hh,he,hg]
  · change (gamma e b:ℝ)≤_ at hh
    rw [gamma,if_neg hfull] at hh
    have herr := rationalInterval_v_error hb.1 hb.2.1
    have hw' := (coordinate_widths b g hwidth).1
    by_cases h0 : t 0≤mu
    · rw [if_pos h0,original_eq_six ⟨ht.2.1,ht.2.2.1,ht.2.2.2,h0⟩]
      have hcap : cap-A (t 0)≤2*e+g/2 := by dsimp [cap,A,mu] at *; linarith only [not_le.mp hfull,hw',hb.1]
      rw [v_eq_A h0] at herr
      linarith only [herr,hh,hcap,hw',hg,he,six_le_cap (t 0) (t 1) ht.2.1,
        min_le_right thirdPrefixTheta (six (t 0) (t 1) (t 2))]
    · rw [if_neg h0]
      linarith only [herr,hh,hw',he,hg,min_le_right thirdPrefixTheta (v (t 0))]

end
end ImbalancedChen.P4AOrderedThirdCompactComparison

