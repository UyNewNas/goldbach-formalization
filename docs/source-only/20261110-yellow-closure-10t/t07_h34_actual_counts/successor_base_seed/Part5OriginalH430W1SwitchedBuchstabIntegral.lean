import ImbalancedChen.P2N48TiedMomentPrimitives
import ImbalancedChen.P2SeedOmegaGlobalEnvelope
import ImbalancedChen.Part5OriginalH430W1SignedOrdinaryBase

/-! The actual one-step Buchstab integral at every selected W1 action.
Reverse-coordinate order (largest,middle,smallest) identifies the original
middle-squared kernel with the existing exact triple moment. -/
namespace ImbalancedChen.Part5OriginalH430W1SwitchedBuchstabIntegral
noncomputable section
open Set MeasureTheory Real LiLiuPrereqBuchstab
open P5OriginalActionMassBound (W1Target W1Anchor)
open P2N48GenericTwoThreeTieVolumes P2N48TiedMomentPrimitives
open P2SeedOmegaLiteralFibre (omegaCap)
open P2SeedOmegaGlobalEnvelope
open scoped Classical

def ordered (a b : ℝ) : Set Triple := {x | a<x.2.2 ∧ x.2.2<x.2.1 ∧ x.2.1<x.1 ∧ x.1<b}
def argument (α : ℝ) (x : Triple) : ℝ := (α-x.2.2-x.2.1-x.1)/x.2.1
def switchedIntegral (i : Fin 7) (j : Fin 10) (α : ℝ) : ℝ :=
  ∫ x in ordered (1/W1Anchor j) (1/W1Target i),buchstab (argument α x)*tripleKernel x
def envelope (i : Fin 7) (j : Fin 10) : ℝ :=
  let s := W1Target i
  let s0 := W1Anchor j
  omegaCap*((s0+s)*log (s0/s)-2*(s0-s))

private theorem ordered_measurable (a b : ℝ) : MeasurableSet (ordered a b) := by
  exact ((isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).inter
    ((isOpen_lt (continuous_snd.comp continuous_snd) (continuous_fst.comp continuous_snd)).inter
    ((isOpen_lt (continuous_fst.comp continuous_snd) continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)))).measurableSet

private theorem subset_sorted (a b : ℝ) : ordered a b ⊆ tripleSorted a b := by
  intro x hx
  obtain ⟨h1,h2,h3,h4⟩ := hx
  exact ⟨⟨⟨(h1.trans (h2.trans h3)).le,h4.le⟩,
    ⟨⟨(h1.trans h2).le,(h3.trans h4).le⟩,⟨h1.le,(h2.trans (h3.trans h4)).le⟩⟩⟩,h2.le,h3.le⟩

theorem argument_lower {s s0 α : ℝ} (hs : (12/5:ℝ)≤s) (hs0 : 0<s0) (hα : 2≤α)
    {x : Triple} (hx : x∈tripleCube (1/s0) (1/s)) : 2*s-3≤argument α x := by
  have hs' : 0<s := by linarith
  have vpos := (one_div_pos.mpr hs0).trans_le hx.2.1.1
  have hz : 0≤2*s-3 := by linarith
  have hp := mul_le_mul_of_nonneg_left hx.2.1.2 hz
  have hr : (2*s-3)*(1/s)=2-3*(1/s) := by field_simp [hs'.ne']; ring
  rw [hr] at hp
  have harg : 2*s-3≤argument α x := (le_div_iff₀ vpos).mpr
    (by linarith only [hp,hα,hx.1.2,hx.2.1.2,hx.2.2.2])

  exact harg

theorem cap_on_cube {s s0 α : ℝ} (hs : (12/5:ℝ)≤s) (hs0 : 0<s0) (hα : 2≤α)
    {x : Triple} (hx : x∈tripleCube (1/s0) (1/s)) : buchstab (argument α x)≤omegaCap := by
  have harg := argument_lower hs hs0 hα hx
  have harg1 : 1≤argument α x := by linarith
  apply (actual_buchstab_original_global_envelope harg1).trans
  apply max_le _ le_rfl
  apply (div_le_iff₀ (by linarith : 0<argument α x)).mpr
  have hmul := mul_le_mul_of_nonneg_left harg omegaCap_positive.le
  unfold omegaCap at hmul ⊢
  linarith only [hmul,hs]

theorem original_switched_integral_le (i : Fin 7) (j : Fin 10) {α : ℝ} (hα : 2≤α) :
    switchedIntegral i j α≤envelope i j := by
  let s := W1Target i
  let s0 := W1Anchor j
  let a : ℝ := 1/s0
  let b : ℝ := 1/s
  have hs : 12/5≤s := le_add_of_nonneg_right (by positivity)
  have h0 := P2AllW1FrozenReceiverFiniteAction.original_W1_parameters i j
  have hs' : 0<s := by linarith
  have h0' : 0<s0 := hs'.trans_le h0.2.1
  have ha : 0<a := one_div_pos.mpr h0'
  have hab : a≤b := one_div_le_one_div_of_le hs' h0.2.1
  have hcont : ContinuousOn tripleKernel (tripleCube a b) := by
    unfold tripleKernel
    exact ((continuousOn_const.div continuous_fst.continuousOn
      (fun x hx => (ha.trans_le hx.1.1).ne')).mul
      (continuousOn_const.div ((continuous_fst.comp continuous_snd).continuousOn.pow 2)
        (fun x hx => pow_ne_zero _ (ha.trans_le hx.2.1.1).ne'))).mul
      (continuousOn_const.div (continuous_snd.comp continuous_snd).continuousOn
        (fun x hx => (ha.trans_le hx.2.2.1).ne'))
  have harg : ContinuousOn (argument α) (tripleCube a b) :=
    (((continuous_const.sub (continuous_snd.comp continuous_snd)).sub
      (continuous_fst.comp continuous_snd)).sub continuous_fst).continuousOn.div
      (continuous_fst.comp continuous_snd).continuousOn (fun x hx => (ha.trans_le hx.2.1.1).ne')
  have hCube : IsCompact (tripleCube a b) := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hpos {x : Triple} (hx : x∈tripleCube a b) : 0≤tripleKernel x := by
    have h1 := ha.trans_le hx.1.1
    have h2 := ha.trans_le hx.2.1.1
    have h3 := ha.trans_le hx.2.2.1
    unfold tripleKernel; positivity
  have hc : ordered a b ⊆ tripleCube a b := fun x hx => (subset_sorted a b hx).1
  have hcω : ContinuousOn (fun _ : Triple => omegaCap) (tripleCube a b) := continuousOn_const
  have hi := (hcω.mul hcont).integrableOn_compact hCube
  change (∫ x in ordered a b,buchstab (argument α x)*tripleKernel x)≤_
  calc
    _ ≤ ∫ x in ordered a b,omegaCap*tripleKernel x := by
      apply setIntegral_mono_on
        ((((continuous_buchstab.comp_continuousOn harg).mul hcont).integrableOn_compact hCube).mono_set hc)
        (hi.mono_set hc) (ordered_measurable a b)
      intro x hx
      exact mul_le_mul_of_nonneg_right (cap_on_cube hs h0' hα (hc hx)) (hpos (hc hx))
    _ ≤ ∫ x in tripleSorted a b,omegaCap*tripleKernel x := by
      apply setIntegral_mono_set (hi.mono_set (fun x hx => hx.1)) _ (Filter.Eventually.of_forall (subset_sorted a b))
      filter_upwards [ae_restrict_mem (measurableSet_tripleSorted a b)] with x hx
      exact mul_nonneg omegaCap_positive.le (hpos hx.1)
    _ = _ := by
      rw [integral_const_mul,tripleTriangle_moment ha hab]
      have hd : b/a=s0/s := by dsimp [a,b]; field_simp [hs'.ne',h0'.ne']
      dsimp only [envelope]
      change omegaCap*moment11 a b=omegaCap*((s0+s)*log (s0/s)-2*(s0-s))
      rw [moment11,hd]
      dsimp [a,b]
      field_simp [hs'.ne',h0'.ne'] <;> ring

end
end ImbalancedChen.Part5OriginalH430W1SwitchedBuchstabIntegral
