import ImbalancedChen.Part5OriginalH430SeedPairRealFibres

/-! Exact identity between the four original good Γ5–8 integrals in the
first W2 action and the ordinary seed coefficient. The bad part is the two
literal seed fibres meeting at one third. The sloping wall is null only
for the real integral. -/
namespace ImbalancedChen.Part5OriginalH430SeedOrdinaryFourIntegral
noncomputable section
open Set MeasureTheory Filter Finset
open P5OriginalActionMassBound (Point originalW2At W2PairDomain)
open P5OriginalFeedbackDomains (measurableSet_W2PairDomain)
open P2EnhancedSeedSingletonPrimitive (parameters)
open P2SeedOmegaLiteralFibre P2SeedOmegaLiteralFunctional (badOrdinaryDouble)
open Part5OriginalH430SeedPairRealFibres
open Part5OriginalH430OrdinaryPairCounts (ordinaryIntegral)
open scoped Classical BigOperators

theorem first_parameters : originalW2At 0=parameters := rfl

private theorem coords :
    P5OriginalActionMassBound.a0 parameters=a0 ∧ P5OriginalActionMassBound.a1 parameters=a1 ∧
      P5OriginalActionMassBound.a2 parameters=a2 ∧ P5OriginalActionMassBound.a3 parameters=a3 := by
  norm_num [P5OriginalActionMassBound.a0,P5OriginalActionMassBound.a1,P5OriginalActionMassBound.a2,
    P5OriginalActionMassBound.a3,parameters,a0,a1,a2,a3]

theorem good_dictionary (x : Point) : x∈W2PairDomain (originalW2At 0) 0 ↔
    a0<x 0 ∧ x 0<x 1 ∧ x 1<a2 ∧ x 1+2*x 0<1 := by
  rw [first_parameters]
  change _<x 0 ∧ x 0<x 1 ∧ x 1<_ ∧ x 1+2*x 0<1 ↔ _
  rw [coords.1,coords.2.2.1]

theorem three_domains :
    W2PairDomain (originalW2At 0) 1=rectangle a2 a3 ∧
      W2PairDomain (originalW2At 0) 2=triangle a1 ∧
      W2PairDomain (originalW2At 0) 3=rectangle a1 a2 := by
  rw [first_parameters]
  refine ⟨?_,?_,?_⟩
  · ext x
    change (_<x 0 ∧ x 0<_ ∧ _<x 1 ∧ x 1<_) ↔ (a0<x 0 ∧ x 0<a1) ∧ a2<x 1 ∧ x 1<a3
    rw [coords.1,coords.2.1,coords.2.2.1,coords.2.2.2]
    tauto
  · ext x
    change (_<x 0 ∧ x 0<x 1 ∧ x 1<_) ↔ (a0<x 0 ∧ x 0<a1) ∧ x 0<x 1 ∧ x 1<a1
    rw [coords.1,coords.2.1]
    exact ⟨fun ⟨hu,hv,hw⟩ => ⟨⟨hu,hv.trans hw⟩,hv,hw⟩,fun ⟨⟨hu,_⟩,hv,hw⟩ => ⟨hu,hv,hw⟩⟩
  · ext x
    change (_<x 0 ∧ x 0<_ ∧ _<x 1 ∧ x 1<_) ↔ (a0<x 0 ∧ x 0<a1) ∧ a1<x 1 ∧ x 1<a2
    rw [coords.1,coords.2.1,coords.2.2.1]
    tauto

private theorem sloping_wall : ∀ᵐ x : Point ∂volume,x 1+2*x 0≠1 := by
  let L : Point →L[ℝ] ℝ := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 2 => ℝ) 1+
    (2:ℝ) • ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 2 => ℝ) 0
  have hL : L≠0 := by
    intro hz
    have hh := congrArg (fun J : Point →L[ℝ] ℝ => J ![0,1]) hz
    norm_num [L] at hh
  rw [ae_iff]
  simpa [L,smul_eq_mul] using affinePrimeWall_volume_zero L hL 1

theorem fifth_ordinary_partition : ordinaryIntegral 0 0=ordinaryTriangle a2-badOrdinaryDouble := by
  let G := W2PairDomain (originalW2At 0) 0
  let T := triangle a2
  have ht : MeasurableSet T := strip_measurable a0 a2 continuous_id continuous_const
  have hg : MeasurableSet G := measurableSet_W2PairDomain _ _
  have hb : MeasurableSet bad := strip_measurable _ _ (by unfold badLower; fun_prop) continuous_const
  have hgb : G⊆T := by
    intro x hx
    obtain ⟨hu,hv,hw,_⟩ := (good_dictionary x).mp hx
    exact ⟨⟨hu,hv.trans hw⟩,hv,hw⟩
  have hsplit : T.indicator raw=ᵐ[volume] fun x => G.indicator raw x+bad.indicator raw x := by
    filter_upwards [sloping_wall] with x hx
    have hbx := bad_dictionary x
    change x∈bad ↔ a0<x 0 ∧ x 0<x 1 ∧ x 1<a2 ∧ 1<x 1+2*x 0 at hbx
    have hgx := good_dictionary x
    change x∈G ↔ _ at hgx
    by_cases hxt : x∈T
    · have htu : (a0<x 0 ∧ x 0<a2) ∧ x 0<x 1 ∧ x 1<a2 := hxt
      obtain ⟨⟨hu,_⟩,hv,hw⟩ := htu
      rcases lt_or_gt_of_ne hx with h | h
      · have h1 := hgx.mpr ⟨hu,hv,hw,h⟩
        have h2 : x∉bad := fun z => (lt_asymm h (hbx.mp z).2.2.2)
        simp [hxt,h1,h2]
      · have h1 : x∉G := fun z => (lt_asymm h (hgx.mp z).2.2.2)
        have h2 := hbx.mpr ⟨hu,hv,hw,h⟩
        simp [hxt,h1,h2]
    · have h1 : x∉G := fun z => hxt (hgb z)
      have h2 : x∉bad := by
        intro z
        obtain ⟨hu,hv,hw,_⟩ := hbx.mp z
        exact hxt ⟨⟨hu,hv.trans hw⟩,hv,hw⟩
      simp [hxt,h1,h2]
  have hGI : Integrable (G.indicator raw) :=
    (integrable_raw_box.mono_set (hgb.trans (triangle_subset le_rfl))).integrable_indicator hg
  have hBI : Integrable (bad.indicator raw) := (integrable_raw_box.mono_set bad_subset).integrable_indicator hb
  have heq : (∫ x in T,raw x)=(∫ x in G,raw x)+∫ x in bad,raw x := by
    rw [←integral_indicator ht,integral_congr_ae hsplit,integral_add hGI hBI,
      integral_indicator hg,integral_indicator hb]
  change (∫ x in G,raw x)=ordinaryTriangle a2-badOrdinaryDouble
  change (∫ x in triangle a2,raw x)=_ at heq
  rw [triangle_integral (by norm_num [a0,a2]) le_rfl,bad_integral] at heq
  linarith only [heq]

theorem seed_four_ordinary :
    (∑ k : Fin 4,ordinaryIntegral 0 k)=ordinaryTriangle a2+ordinaryRectangle a2 a3+
      ordinaryTriangle a1+ordinaryRectangle a1 a2-badOrdinaryDouble := by
  have h6 : ordinaryIntegral 0 1=ordinaryRectangle a2 a3 := by
    change (∫ x in W2PairDomain (originalW2At 0) 1,raw x)=_
    rw [three_domains.1]
    exact rectangle_integral (by norm_num [a0,a2]) (by norm_num [a2,a3]) le_rfl
  have h7 : ordinaryIntegral 0 2=ordinaryTriangle a1 := by
    change (∫ x in W2PairDomain (originalW2At 0) 2,raw x)=_
    rw [three_domains.2.1]
    exact triangle_integral (by norm_num [a0,a1]) (by norm_num [a1,a2])
  have h8 : ordinaryIntegral 0 3=ordinaryRectangle a1 a2 := by
    change (∫ x in W2PairDomain (originalW2At 0) 3,raw x)=_
    rw [three_domains.2.2]
    exact rectangle_integral (by norm_num [a0,a1]) (by norm_num [a1,a2]) (by norm_num [a2,a3])
  rw [Fin.sum_univ_four,fifth_ordinary_partition,h6,h7,h8]
  ring

end
end ImbalancedChen.Part5OriginalH430SeedOrdinaryFourIntegral
