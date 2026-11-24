import ImbalancedChen.P4AOriginalOrderedThirdTable

/-! Literal parent preservation on every old wholly ordered third owner.
In the lower region extrema are attained at the two ordered corners for
each sum, the upper corner for the two gate gaps, and (lx,ly,uz) for
the first rescue. The other rescue and singleton y are dominated. -/
namespace ImbalancedChen.P4AOriginalOrderedThirdAgreement
noncomputable section
open Set HistoricalThirdCoarse VariableEnvelope P4AOriginalOrderedThirdTable
open scoped Classical

private theorem lo_cast (m : ℕ) (j : Cell m) (i : Fin 3) :
    (qLogPrimeMeshLo 0 (19/96) m j i : ℝ)=logPrimeMeshLo 0 (19/96) m j i := by
  simpa only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using congrFun (cast_qLogPrimeMeshLo 0 (19/96) m j) i

theorem hi_cast (m : ℕ) (j : Cell m) (i : Fin 3) :
    (qLogPrimeMeshHi 0 (19/96) m j i : ℝ)=logPrimeMeshHi 0 (19/96) m j i := by
  simpa only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using congrFun (cast_qLogPrimeMeshHi 0 (19/96) m j) i

theorem old_rectangle {e chi : ℝ} {m : ℕ} {j : Cell m} (hj : j∈cells e chi m) (t : Point) :
    t∈portion m j ↔ (box m j).InBox (t 0) (t 1) (t 2) := by
  let b := box m j
  have H := (mem_cells e chi m j).mp hj
  have hlo (i : Fin 3) := lo_cast m j i
  have hhi (i : Fin 3) := hi_cast m j i
  constructor
  · intro h
    have hs (i : Fin 3) := h.1 i (mem_univ _)
    exact ⟨(hlo 0).symm ▸ (hs 0).1,(hhi 0).symm ▸ (hs 0).2,
      (hlo 1).symm ▸ (hs 1).1,(hhi 1).symm ▸ (hs 1).2,
      (hlo 2).symm ▸ (hs 2).1,(hhi 2).symm ▸ (hs 2).2⟩
  · rintro ht
    change b.InBox _ _ _ at ht
    refine ⟨?_,?_,?_,?_⟩
    · intro i _
      rw [← hlo,← hhi]
      fin_cases i
      · exact ⟨ht.1,ht.2.1⟩
      · exact ⟨ht.2.2.1,ht.2.2.2.1⟩
      · exact ht.2.2.2.2
    · exact (by exact_mod_cast H.2.1 : (0:ℝ)≤b.lz).trans ht.2.2.2.2.1
    · exact ht.2.2.2.2.2.trans ((by exact_mod_cast H.2.2.1 : (b.uz:ℝ)≤b.ly).trans ht.2.2.1)
    · exact ht.2.2.2.1.trans ((by exact_mod_cast H.2.2.2.1 : (b.uy:ℝ)≤b.lx).trans ht.1)

private theorem inf_of_minimum {m : ℕ} {j : Cell m} {f : Point → ℝ} (hf : Continuous f)
    {t : Point} (ht : t∈portion m j) {c : ℝ} (hv : f t=c)
    (hl : ∀ s ∈ portion m j, c≤f s) : infimum m j f=c := by
  refine le_antisymm ((inf_le hf ht).trans hv.le) ?_
  apply le_csInf ((show (portion m j).Nonempty from ⟨t,ht⟩).image _)
  rintro _ ⟨s,hs,rfl⟩
  exact hl s hs

private theorem inf_v {m : ℕ} {j : Cell m} {g : Point → ℝ} (hg : Continuous g)
    {l u : ℚ} {a b : Point} (ha : a∈portion m j) (hb : b∈portion m j)
    (hlo : g a=l) (hhi : g b=u)
    (h : ∀ t∈portion m j, (l:ℝ)≤g t ∧ g t≤(u:ℝ)) :
    infimum m j (fun t => v (g t)) = (qVLo l u:ℝ) := by
  have hends := (h a ha).2
  rw [hlo] at hends
  have hlu : l≤u := by exact_mod_cast hends
  have hl t (ht : t ∈ portion m j) := qVLo_le_v (h t ht).1 (h t ht).2
  have he := HistoricalThirdCoarse.interval_lower_endpoints l u hlu
  by_cases hn : qV l≤qV u
  · apply inf_of_minimum (continuous_v.comp hg) ha _ hl
    rw [hlo,he,min_eq_left hn,cast_qV]
  · apply inf_of_minimum (continuous_v.comp hg) hb _ hl
    rw [hhi,he,min_eq_right (le_of_not_ge hn),cast_qV]

theorem original_value {e chi : ℝ} (he : 0≤e) {m : ℕ} {j : Cell m}
    (hj : j∈cells e chi m) : envelope e m j=(gamma e (box m j):ℝ) := by
  let b := box m j
  let a : Point := ![b.lx,b.ly,b.lz]
  let u : Point := ![b.ux,b.uy,b.uz]
  let r : Point := ![b.lx,b.ly,b.uz]
  have hw := ((mem_cells e chi m j).mp hj).1
  have hx : (b.lx:ℝ)≤b.ux := by exact_mod_cast hw.1
  have hy : (b.ly:ℝ)≤b.uy := by exact_mod_cast hw.2.1
  have hz : (b.lz:ℝ)≤b.uz := by exact_mod_cast hw.2.2
  have ha : a∈portion m j := (old_rectangle hj _).mpr ⟨le_rfl,hx,le_rfl,hy,le_rfl,hz⟩
  have hu : u∈portion m j := (old_rectangle hj _).mpr ⟨hx,le_rfl,hy,le_rfl,hz,le_rfl⟩
  have hr : r∈portion m j := (old_rectangle hj _).mpr ⟨le_rfl,hx,le_rfl,hy,hz,le_rfl⟩
  have I {g : Point → ℝ} (hg : Continuous g) {l u' : ℚ}
      (h1 : g a=l) (h2 : g u=u')
      (h : ∀ t, b.InBox (t 0) (t 1) (t 2) → (l:ℝ)≤g t ∧ g t≤(u':ℝ)) :=
    inf_v hg ha hu h1 h2 (fun t ht => h t ((old_rectangle hj _).mp ht))
  have bx : infimum m j (actualExtendedThirdRobustBaseBranch 0) = (qVLo b.lx b.ux:ℝ) :=
    I (g:=fun t => t 0) (continuous_apply 0) rfl rfl (fun _ h => ⟨h.1,h.2.1⟩)
  have hhigh : logPrimeMeshHi 0 (19/96) m j 0=(b.ux:ℝ) := (hi_cast m j 0).symm
  rw [envelope,hhigh,HistoricalThirdCoarse.gamma]
  change (if (b.ux:ℝ)≤mu-4*e then full e m j else _) = ((if (b.ux:ℝ)≤mu-4*e then fullGamma e b else _ : ℚ):ℝ)
  split_ifs with hfull
  · have htop : (b.ux:ℝ)≤mu := by linarith
    have hxz : infimum m j actualExtendedThirdPairXZ = (qVLo (b.lx+b.lz) (b.ux+b.uz):ℝ) := by
      apply I (g:=fun t => t 0+t 2) (by fun_prop) <;> try simp [a,u]
      rintro t ⟨hl,hh,_,_,zl,zh⟩
      exact ⟨by push_cast; linarith,by push_cast; linarith⟩
    have hyz : infimum m j actualExtendedThirdPairYZ = (qVLo (b.ly+b.lz) (b.uy+b.uz):ℝ) := by
      apply I (g:=fun t => t 1+t 2) (by fun_prop) <;> try simp [a,u]
      rintro t ⟨_,_,hl,hh,zl,zh⟩
      exact ⟨by push_cast; linarith,by push_cast; linarith⟩
    have hxy : infimum m j (actualExtendedThirdRobustBaseBranch 2) =
        (qVLo (b.lx+b.ly) (b.ux+b.uy):ℝ) := by
      apply I (g:=fun t => t 0+t 1) (by fun_prop) <;> try simp [a,u]
      rintro t ⟨hl,hh,yl,yh,_,_⟩
      exact ⟨by push_cast; linarith,by push_cast; linarith⟩
    have hxyz : infimum m j (actualExtendedThirdRobustBaseBranch 3) =
        (qVLo (b.lx+b.ly+b.lz) (b.ux+b.uy+b.uz):ℝ) := by
      apply I (g:=fun t => t 0+t 1+t 2) (by fun_prop) <;> try simp [a,u]
      rintro t ⟨hl,hh,yl,yh,zl,zh⟩
      exact ⟨by push_cast; linarith,by push_cast; linarith⟩
    have hg1 : infimum m j actualExtendedThirdGateXZ=xzGap b :=
      inf_of_minimum continuous_actualExtendedThirdGateXZ hu rfl (fun _ ht => xzGap_le ((old_rectangle hj _).mp ht))
    have hg2 : infimum m j actualExtendedThirdGateYZ=yzGap b :=
      inf_of_minimum continuous_actualExtendedThirdGateYZ hu rfl (fun _ ht => yzGap_le ((old_rectangle hj _).mp ht))
    have H {t : Point} (ht : t∈portion m j) : t 0≤mu :=
      ((old_rectangle hj t).mp ht).2.1.trans htop
    have R {t : Point} (ht : t∈portion m j) :
        actualExtendedThirdRobustBaseBranch 4 t=max (A (t 0)) (B (t 2)) := by
      change max (v (t 0)) (wInner (t 0) (t 1) (t 2))=_
      rw [v_eq_A (H ht),wInner_eq_B _ (ht.2.2.2.trans (H ht)) ht.2.1]
    have hres : infimum m j (actualExtendedThirdRobustBaseBranch 4)=(rescue b:ℝ) := by
      apply inf_of_minimum (continuous_actualExtendedThirdRobustBaseBranch 4) hr
      · rw [R hr]
        simp [r,rescue,cast_qA,cast_qB]
      · intro s hs
        rw [R hs]
        exact rescue_le ((old_rectangle hj _).mp hs)
    have mono {f g : Point→ℝ} (hf : Continuous f) (h : ∀ t∈portion m j, f t≤g t) :
        infimum m j f ≤ infimum m j g := by
      apply le_csInf ((show (portion m j).Nonempty from ⟨a,ha⟩).image _)
      rintro _ ⟨t,ht,rfl⟩
      exact (inf_le hf ht).trans (h t ht)
    have by0 : infimum m j (actualExtendedThirdRobustBaseBranch 1) ≤
        infimum m j (actualExtendedThirdRobustBaseBranch 0) := by
      apply mono (continuous_actualExtendedThirdRobustBaseBranch 1)
      intro t ht
      change v (t 1) ≤ v (t 0)
      rw [v_eq_A (ht.2.2.2.trans (H ht)),v_eq_A (H ht)]
      dsimp [A]
      linarith [ht.2.2.2]
    have by4 : infimum m j (actualExtendedThirdRobustBaseBranch 5) ≤
        infimum m j (actualExtendedThirdRobustBaseBranch 4) := by
      apply mono (continuous_actualExtendedThirdRobustBaseBranch 5)
      intro t ht
      change max (v (t 0)) (wInner (t 0) (t 2) (t 1)) ≤ max (v (t 0)) (wInner (t 0) (t 1) (t 2))
      rw [wInner_eq_B _ (ht.2.2.1.trans (ht.2.2.2.trans (H ht))) (ht.2.1.trans ht.2.2.1),
        wInner_eq_B _ (ht.2.2.2.trans (H ht)) ht.2.1]
      apply max_le_max_left
      dsimp [B]; linarith [ht.2.2.1]
    have drop {v w : ℝ} (h : w≤v) (s : ℝ) : max v (max w s)=max v s := by
      rw [← max_assoc,max_eq_left h]
    dsimp only [full,fullGamma]
    rw [drop by0,drop by4,hg1,hg2,hxz,hyz,hxy,hxyz,hres,bx]
    split_ifs <;> simp only [Rat.cast_max]
  · exact bx

theorem old_owner_level {e chi : ℝ} (he : 0≤e) {m : ℕ} {j : Cell m}
    (hj : j∈cells e chi m) : capValue e m j=levelExponent e (box m j) := by
  rw [capValue,original_value he hj]
  exact min_eq_right (levelExponent_lt_initial _ _ he ((mem_cells _ _ _).mp hj).1
    ((mem_cells _ _ _).mp hj).2.1).le

end
end ImbalancedChen.P4AOriginalOrderedThirdAgreement
