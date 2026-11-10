import ImbalancedChen.Part5OriginalH430W1OriginalBaseEnclosure
import ImbalancedChen.P2OriginalClosedCellProfileAtoms

/-! The actual target-deleted three-prime sum for the W1 unsifted family.
The integration variable in the middle slot receives the extra reciprocal. -/
namespace ImbalancedChen.Part5OriginalH430W1ConvertedPrimeQuadrature
noncomputable section
open Set MeasureTheory Filter Real Finset
open P5OriginalActionMassBound (W1Anchor W1Target)
open P2OriginalBankChildPrimeMass P2OriginalHalfOpenProfileCarrier
open P2OriginalAffineProfilePassage P2OriginalClosedCellProfileAtoms
open P2N48GenericTwoThreeTieVolumes P2N48TiedMomentPrimitives
open scoped Classical BigOperators

def chamber (a b : ℝ) : Set (Coord 3) := {x | a≤x 2 ∧ x 2<x 1 ∧ x 1<x 0 ∧ x 0<b}
def form : Fin 4 → Coord 3 →L[ℝ] ℝ := ![-coord 2,coord 2-coord 1,coord 1-coord 0,coord 0]
def edge (a b : ℝ) : Fin 4 → ℝ := ![-a,0,0,b]
def test (x : Coord 3) : ℝ := 1/max (1/10:ℝ) (x 1)

private theorem form_ne (j : Fin 4) : form j≠0 := by
  intro h
  have h0 := congrArg (fun F : Coord 3 →L[ℝ] ℝ => F ![1,0,0]) h
  have h1 := congrArg (fun F : Coord 3 →L[ℝ] ℝ => F ![0,1,0]) h
  have h2 := congrArg (fun F : Coord 3 →L[ℝ] ℝ => F ![0,0,1]) h
  fin_cases j <;> norm_num [form,coord] at h0 h1 h2

private theorem chambers (a b : ℝ) : AffineSandwich form (edge a b) (chamber a b) := by
  constructor
  · intro x hx
    have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
    simp [form,edge,coord] at h0 h1 h2 h3
    exact ⟨by linarith,by linarith,by linarith,h3⟩
  · rintro x ⟨h0,h1,h2,h3⟩ j
    fin_cases j <;> simp [form,edge,coord] <;> linarith

theorem chamber_bounds {a b : ℝ} {x : Coord 3} (h : x∈chamber a b) :
    ∀ i,a≤x i ∧ x i≤b := by
  intro i; rcases h with ⟨hh,hm,hp,hb⟩; fin_cases i <;> constructor <;> linarith

private def toTriple : Coord 3 ≃ᵐ Triple :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)))

private theorem perm : MeasurePreserving toTriple volume volume := by
  have hid : MeasurePreserving (id : ℝ → ℝ) volume volume := ⟨measurable_id,by simp⟩
  have hprod : MeasurePreserving (Prod.map (id : ℝ → ℝ)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))) volume volume := by
    simpa only [Measure.volume_eq_prod] using hid.prod (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))
  exact hprod.comp (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (0:Fin 3))

private theorem density_integral (a b : ℝ) (ha : 1/5≤a) (hab : a≤b) :
    (∫ x in chamber a b,test x*∏ i,1/x i)≤moment11 a b := by
  have ha0 : 0<a := by linarith
  let D := tripleSorted a b
  have hsub : chamber a b⊆toTriple ⁻¹' D := by
    intro x hx
    obtain ⟨h0,h1,h2,h3⟩ := hx
    change (x 0,(x 1,x 2))∈tripleSorted a b
    exact ⟨⟨⟨h0.trans (h1.trans h2).le,h3.le⟩,
      ⟨⟨h0.trans h1.le,(h2.trans h3).le⟩,⟨h0,(h1.trans (h2.trans h3)).le⟩⟩⟩,h1.le,h2.le⟩
  have hm : MeasurableSet (chamber a b) :=
    (measurableSet_le measurable_const (measurable_pi_apply 2)).inter
      ((measurableSet_lt (measurable_pi_apply 2) (measurable_pi_apply 1)).inter
      ((measurableSet_lt (measurable_pi_apply 1) (measurable_pi_apply 0)).inter
        (measurableSet_lt (measurable_pi_apply 0) measurable_const)))
  have hc : ContinuousOn tripleKernel (tripleCube a b) := by
    unfold tripleKernel
    exact ((continuousOn_const.div continuous_fst.continuousOn
      (fun x hx => (ha0.trans_le hx.1.1).ne')).mul
      (continuousOn_const.div ((continuous_fst.comp continuous_snd).continuousOn.pow 2)
        (fun x hx => pow_ne_zero _ (ha0.trans_le hx.2.1.1).ne'))).mul
      (continuousOn_const.div (continuous_snd.comp continuous_snd).continuousOn
        (fun x hx => (ha0.trans_le hx.2.2.1).ne'))
  have hi : IntegrableOn tripleKernel D :=
    (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).mono_set
      (fun _ hx => hx.1)
  have hmeas := measurableSet_tripleSorted a b
  have hpr := perm.restrict_preimage_emb toTriple.measurableEmbedding D
  have hi' : IntegrableOn (tripleKernel ∘ toTriple) (toTriple ⁻¹' D) := hi.comp_measurePreserving hpr
  calc
    _ = ∫ x in chamber a b,(tripleKernel ∘ toTriple) x := by
      apply setIntegral_congr_fun hm
      intro x hx
      have hm' : 1/10≤x 1 := by linarith [(chamber_bounds hx 1).1]
      change test x*(∏ i:Fin 3,1/x i)=tripleKernel (x 0,(x 1,x 2))
      rw [test,max_eq_right hm',Fin.prod_univ_three,tripleKernel]
      simp only [one_div,pow_two,mul_inv_rev]; ring
    _ ≤ ∫ x in toTriple ⁻¹' D,(tripleKernel ∘ toTriple) x := by
      apply setIntegral_mono_set hi' _ (Eventually.of_forall hsub)
      filter_upwards [ae_restrict_mem (toTriple.measurable hmeas)] with x hx
      have h0 := ha0.trans_le hx.1.1.1
      have h1 := ha0.trans_le hx.1.2.1.1
      have h2 := ha0.trans_le hx.1.2.2.1
      dsimp only [Function.comp_apply,tripleKernel]
      positivity
    _ = _ := (perm.setIntegral_preimage_emb toTriple.measurableEmbedding tripleKernel D).trans
      (tripleTriangle_moment ha0 hab)

theorem actual_triple_quadrature {η A a b ε : ℝ} (hη : 0<η) (hA : η≤A)
    (ha : 1/5≤a) (hb : b≤1/2) (hab : a≤b) (he : 0<ε) :
    ∃ T : ℕ, ∀ N : ℕ,T≤N → ∀ L∈Icc η A,
      scaledPrimeSum N L (chamber a b) test ≤ moment11 a b+ε := by
  have hcont : Continuous test := continuous_const.div (continuous_const.max (continuous_apply 1))
    (fun x => (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/10) (le_max_left _ _)).ne')
  have hbound (x : Coord 3) : |test x|≤10 := by
    have hm : 1/10≤max (1/10:ℝ) (x 1) := le_max_left _ _
    have hp : 0<max (1/10:ℝ) (x 1) := (by norm_num : (0:ℝ)<1/10).trans_le hm
    rw [test,abs_of_nonneg (one_div_pos.mpr hp).le]
    exact (div_le_iff₀ hp).mpr (by linarith)
  obtain ⟨T,hT⟩ := compact_uniform_sandwich hη hA (by norm_num : (0:ℝ)≤10) he
    form (edge a b) form_ne (enumForms (controlForms 3)) (enumBounds controlBounds)
    (fun i => control_nonzero ((Fintype.equivFin _).symm i))
    (by rw [←finiteGates_enum]; exact control_in_cube 3) (chambers a b)
    (by rw [←finiteGates_enum]; intro x hx; apply control_contains_box
        exact fun i => ⟨ha.trans (chamber_bounds hx i).1,(chamber_bounds hx i).2.trans hb⟩)
    test hcont hbound
  refine ⟨T,?_⟩
  intro N hN L hL
  have h := (abs_lt.mp (hT N hN L hL)).2
  linarith only [h,density_integral a b ha hab]

end
end ImbalancedChen.Part5OriginalH430W1ConvertedPrimeQuadrature
