import ImbalancedChen.Part3WeakGradientLocalTensorDetector
import Mathlib.Topology.Compactness.Lindelof

/-! SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.
Countably many genuine local cutoffs identify a local L² function from its
compact tensor pairings. Consequently its two zero weak coordinate partials
force ONE almost-everywhere constant on a positive-height open rectangle. -/
namespace ImbalancedChen.Part3.WeakGradientRectangleRigidity20261026a
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff
open ImbalancedChen.Part3.WeakGradientRectangleTensorPairing20261026a
open ImbalancedChen.Part3.WeakGradientLocalTensorDetector20261026a

/-- A genuine smooth test, equal to one on a neighborhood of the chosen point,
whose entire closed support stays strictly within the original interval. -/
theorem exists_interval_cutoff_at {a b x : ℝ} (hx : x ∈ Ioo a b) :
    ∃ (g : ℝ → ℝ) (r : ℝ), 0 < r ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ioo a b ∧ ∀ y ∈ ball x r, g y = 1 := by
  let r : ℝ := min (x-a) (b-x) / 4
  have hr : 0 < r := div_pos (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)) (by norm_num)
  let β : ContDiffBump x :=
    { rIn := r, rOut := 2*r, rIn_pos := hr, rIn_lt_rOut := by linarith }
  refine ⟨β, r, hr, β.contDiff, β.hasCompactSupport, ?_, ?_⟩
  · rw [β.tsupport_eq]
    intro y hy
    have hy' : |y-x| ≤ 2*r := by simpa [β, Real.dist_eq] using hy
    have hmin₁ : 4*r ≤ x-a := by dsimp [r]; linarith [min_le_left (x-a) (b-x)]
    have hmin₂ : 4*r ≤ b-x := by dsimp [r]; linarith [min_le_right (x-a) (b-x)]
    rcases abs_le.mp hy' with ⟨hl, hu⟩
    constructor <;> linarith
  · intro y hy
    exact β.one_of_mem_closedBall (le_of_lt hy)

/-- Local compact tensor tests really detect local L² functions. The exceptional
sets are combined only after a countable subcover has been constructed. -/
theorem ae_zero_of_rectangle_tensor_pairings {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hc : 0 ≤ c)
    {f : (ℝ × ℝ) → ℂ} (hf : MemLp f 2 (volume.restrict (openRectangle a b c d)))
    (hpair : ∀ u v : ℝ → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ Ioo a b → ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f u v = 0) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ openRectangle a b c d → f p = 0 := by
  let Q := openRectangle a b c d
  choose gx rx hrx hgx hgcx hgsx hgonex using
    (fun p : Q => exists_interval_cutoff_at p.property.1)
  choose gy ry hry hgy hgcy hgsy hgoney using
    (fun p : Q => exists_interval_cutoff_at p.property.2)
  let V : Q → Set (ℝ × ℝ) := fun p => ball p.val.1 (rx p) ×ˢ ball p.val.2 (ry p)
  have hVo : ∀ p, IsOpen (V p) := fun _ => isOpen_ball.prod isOpen_ball
  have hcover : Q ⊆ ⋃ p, V p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩, mem_ball_self (hrx ⟨p,hp⟩), mem_ball_self (hry ⟨p,hp⟩)⟩
  have hQne : Q.Nonempty := ⟨((a+b)/2,(c+d)/2), by
    dsimp [Q, openRectangle]; constructor <;> constructor <;> linarith⟩
  letI : Nonempty Q := ⟨⟨hQne.choose, hQne.choose_spec⟩⟩
  obtain ⟨seq, hseq⟩ := (HereditarilyLindelofSpace.isLindelof Q).indexed_countable_subcover V hVo hcover
  have hzero : ∀ n : ℕ, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      p ∈ Q → p ∈ V (seq n) → f p = 0 := by
    intro n
    filter_upwards [ae_zero_where_local_cutoff_one hc hf hpair
      (hgx (seq n)) (hgy (seq n)) (hgcx (seq n)) (hgcy (seq n))
      (hgsx (seq n)) (hgsy (seq n))] with p hp
    intro hpQ hpV
    exact hp hpQ (hgonex (seq n) p.1 hpV.1) (hgoney (seq n) p.2 hpV.2)
  filter_upwards [ae_all_iff.mpr hzero] with p hp
  intro hpQ
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hseq hpQ)
  exact hp n hpQ hn

/-- The constant function has exactly the expected tensor average. -/
theorem tensorPairing_const {a b c d : ℝ} (C : ℂ) {g h : ℝ → ℝ}
    (hgs : tsupport g ⊆ Ioo a b) (hhs : tsupport h ⊆ Ioo c d) :
    tensorPairing (openRectangle a b c d) (fun _ => C) g h =
      ((∫ x, g x) * (∫ y, h y)) • C := by
  unfold tensorPairing
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_smul_const]
    congr 1
    exact integral_prod_mul g h
  · intro p hp
    have hz : tensorTest g h p = 0 := by
      by_cases hx : p.1 ∈ Ioo a b
      · have hy : p.2 ∉ Ioo c d := fun hy => hp ⟨hx,hy⟩
        simp [tensorTest, image_eq_zero_of_notMem_tsupport (fun ht => hy (hhs ht))]
      · simp [tensorTest, image_eq_zero_of_notMem_tsupport (fun ht => hx (hgs ht))]
    simp [hz]

/-- The real rigidity endpoint on a rectangle: neither a representative nor
an ae constant is part of the input. The scalar is the constructed tensor
average, and both weak partials concern exactly the available tensor tests. -/
theorem ae_eq_one_const_of_zero_weak_partials {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hc : 0 ≤ c)
    {f : (ℝ × ℝ) → ℂ} (hf : MemLp f 2 (volume.restrict (openRectangle a b c d)))
    (hweakX : ∀ ψ h : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f (deriv ψ) h = 0)
    (hweakY : ∀ g ψ : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f g (deriv ψ) = 0) :
    ∃ C : ℂ, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ openRectangle a b c d → f p = C := by
  let Q := openRectangle a b c d
  have hvol : volume Q ≠ ⊤ := ne_of_lt <| lt_of_le_of_lt
    (measure_mono (show Q ⊆ Icc a b ×ˢ Icc c d from fun p hp =>
      ⟨⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩))
    ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)
  letI : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.mpr hvol
  have hfi : IntegrableOn f Q := MemLp.integrable (by norm_num) hf
  obtain ⟨C,hC⟩ := exists_common_tensor_average hab hcd hfi hweakX hweakY
  refine ⟨C, ?_⟩
  have hdiff : MemLp (fun p => f p - C) 2 (volume.restrict Q) := hf.sub (memLp_const C)
  have hpair : ∀ g h : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Ioo c d → tensorPairing Q (fun p => f p - C) g h = 0 := by
    intro g h hg hgc hgs hh hhc hhs
    have hi₁ := integrable_tensor_pair hfi hg.continuous hh.continuous hgc hhc
    have hi₂ := integrable_tensor_pair (integrable_const C) hg.continuous hh.continuous hgc hhc
    change (∫ p in Q, tensorTest g h p • (f p - C)) = 0
    simp_rw [smul_sub]
    rw [integral_sub hi₁ hi₂]
    change tensorPairing Q f g h - tensorPairing Q (fun _ => C) g h = 0
    rw [hC g h hg hgc hgs hh hhc hhs, tensorPairing_const C hgs hhs, sub_self]
  filter_upwards [ae_zero_of_rectangle_tensor_pairings hab hcd hc hdiff hpair] with p hp
  intro hpQ
  exact sub_eq_zero.mp (hp hpQ)

end
end ImbalancedChen.Part3.WeakGradientRectangleRigidity20261026a
