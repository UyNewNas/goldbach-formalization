import ImbalancedChen.P5ZU1011OriginalSixteenEligibilityStripVolume
import ImbalancedChen.P5ZU1011OriginalSixteenOscillation

/-!
# Exact actual16 eligibility stability under a nearby snap

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual formula-derived coefficient bound gives global margin
oscillation at most 6*l1Delta. Outside the SAME actual required-wall strip
union of width delta, every margin has absolute value greater than delta.
Therefore l1Delta<=delta/12 preserves every required strict margin sign,
and hence exact TypedEligible for ALL sixteen original policies.

The starting point belongs to the unit cube because the strip union is
cube restricted. The nearby point needs no additional cube, positivity,
gate, or agreement supplier. Original-domain support supplies this cube
membership directly below. No saved endpoint or H248 knot claim is made.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilitySnapStability

noncomputable section

open Set U11Integral BoxCertificates EligibilityGridCertificates EligibilityStripVolume
open U1011OriginalSixteenOscillation P2OriginalFourthCapProducerInterface
open scoped BigOperators

theorem margin_abs_sub_le_six_l1 (p : Policy) (left : Bool) (g : Gate) (v w : LogFour) :
    |(margin p left g).eval v - (margin p left g).eval w| ≤ 6 * l1Delta v w := by
  have heq : (margin p left g).eval v - (margin p left g).eval w =
      ∑ i : Fin 4, ((margin p left g).coefficient i : ℝ) * (v i - w i) := by
    simp only [Affine.eval, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ ∑ i : Fin 4, |((margin p left g).coefficient i : ℝ) * (v i - w i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, 6 * |v i - w i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (margin_coefficient_abs_le_six p left g i) (abs_nonneg _)
    _ = 6 * l1Delta v w := by rw [l1Delta, Finset.mul_sum]

/-- Off the cube-restricted union, the actual required margin has the
explicit separation delta. No margin-separation premise is supplied. -/
theorem actual_margin_separated (delta : ℝ) {v : LogFour} (hv : v ∈ unitCube)
    (hoff : v ∉ actualStripUnion delta) (p : Policy) (left : Bool) (g : Gate)
    (hg : Required p g) : delta < |(margin p left g).eval v| := by
  by_contra hn
  apply hoff
  apply mem_iUnion.mpr
  refine ⟨(p, g, left), ?_⟩
  simp only [if_pos hg]
  exact ⟨hv, le_of_not_gt hn⟩

theorem actual_margin_sign_stable (delta : ℝ) (hdelta : 0 < delta)
    {v w : LogFour} (hv : v ∈ unitCube) (hoff : v ∉ actualStripUnion delta)
    (hclose : l1Delta v w ≤ delta / 12) (p : Policy) (left : Bool) (g : Gate)
    (hg : Required p g) :
    (0 < (margin p left g).eval v ↔ 0 < (margin p left g).eval w) := by
  have hsep := actual_margin_separated delta hv hoff p left g hg
  have herr : |(margin p left g).eval v - (margin p left g).eval w| ≤ delta / 2 := by
    apply (margin_abs_sub_le_six_l1 p left g v w).trans
    linarith only [hclose]
  constructor
  · intro hpos
    rw [abs_of_pos hpos] at hsep
    have hdiff := (abs_le.mp herr).2
    linarith only [hsep, hdiff, hdelta]
  · intro hpos
    by_contra hn
    have hnonpos : (margin p left g).eval v ≤ 0 := le_of_not_gt hn
    rw [abs_of_nonpos hnonpos] at hsep
    have hdiff := (abs_le.mp herr).1
    linarith only [hsep, hdiff, hpos, hdelta]

/-- One reserve precedes ALL sixteen policies and all nearby moving
points. This is exact original gate agreement, derived from the actual
proper-wall strips and the coefficient formula, not an hAgree input. -/
theorem actual_all_sixteen_eligibility_stable (delta : ℝ) (hdelta : 0 < delta)
    {v w : LogFour} (hv : v ∈ unitCube) (hoff : v ∉ actualStripUnion delta)
    (hclose : l1Delta v w ≤ delta / 12) :
    ∀ p : Policy, TypedEligible p v ↔ TypedEligible p w := by
  intro p
  rw [typedEligible_iff_positive_margins, typedEligible_iff_positive_margins]
  constructor
  · intro he g hg left
    exact (actual_margin_sign_stable delta hdelta hv hoff hclose p left g hg).mp (he g hg left)
  · intro he g hg left
    exact (actual_margin_sign_stable delta hdelta hv hoff hclose p left g hg).mpr (he g hg left)

theorem originalDomain_subset_originalCube (mask : Set (ℝ × ℝ)) :
    originalDomain mask ⊆ originalCube := by
  intro v hv i hi
  obtain ⟨ha, h32, h21, h1, h0lo, h0hi, hm⟩ := hv
  fin_cases i <;> constructor <;> linarith

theorem originalDomain_subset_unitCube (mask : Set (ℝ × ℝ)) :
    originalDomain mask ⊆ unitCube :=
  (originalDomain_subset_originalCube mask).trans originalCube_subset_unitCube

end

end ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilitySnapStability
