import ImbalancedChen.Part3SharedFirstFactorLargePairedGCDW
import ImbalancedChen.Part3TransposedGCDPoissonMask
import ImbalancedChen.Part3TransposedPrimitiveUPayment

/-!
# The full Fourier remainder at large paired gcd and one common first factor

The raw zero and the nonzero Fourier series retain the very same original
ordered alpha-pair mask as whole W. A finite grouping of the two remaining
factor labels keeps the common first factor in the lcm denominator. The
actual beta and gamma1 second moments are multiplied before the original
medium geometry pays every fixed logarithmic cost.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter Topology
open scoped BigOperators Pointwise
open TransposedGCDPoissonMask TransposedPrimitiveUPayment
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The literal raw zero under the original large ordered paired-gcd mask. -/
def MediumAtom.sharedLargePairedGCDZero (d : MediumAtom) (Y : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    (d.q1SliceAtom p).transposedAtom.commonLargeBetaGCDZeroPart Y

/-- The entire nonzero Fourier series under precisely that same mask. -/
def MediumAtom.sharedLargePairedGCDNonzero (d : MediumAtom) (Y : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    (d.q1SliceAtom p).transposedAtom.commonLargeBetaGCDNonzeroPart Y

namespace SharedFirstFactorLargePairedGCDNonzero

private def tailLabels (d : MediumAtom) : Finset (ℕ × ℕ) :=
  factorCarrier d.Q2 ×ˢ factorCarrier d.Q3

private def tailProducts (d : MediumAtom) : Finset ℕ :=
  (tailLabels d).image (fun u ↦ u.1 * u.2)

private def tailGamma (d : MediumAtom) (v : ℕ) : ℂ :=
  ∑ u ∈ (tailLabels d).filter (fun u ↦ u.1 * u.2 = v), d.gamma2 u.1 * d.gamma3 u.2

private def tailCap (d : MediumAtom) : ℝ := 4 * d.Q2 * d.Q3

private def tau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

private theorem factor_bounds {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : 0 < n ∧ Q ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hlower : Q ≤ (n : ℝ) :=
    (Nat.le_ceil Q).trans (by exact_mod_cast hlo)
  have hpos : (0 : ℝ) < n := (zero_lt_one.trans_le hQ).trans_le hlower
  refine ⟨by exact_mod_cast hpos, hlower, ?_⟩
  exact (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
    (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

private theorem one_le_tailCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ tailCap d := by
  have h2 := hd.2.2.2.1
  have h3 := hd.2.2.2.2.1
  unfold tailCap
  nlinarith [mul_le_mul h2 h3 zero_le_one (by linarith : 0 ≤ d.Q2)]

private theorem tail_product_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {u : ℕ × ℕ}
    (hu : u ∈ tailLabels d) : 0 < u.1 * u.2 ∧ (u.1 * u.2 : ℕ) ≤ Nat.floor (tailCap d) := by
  obtain ⟨h2, h3⟩ := Finset.mem_product.mp hu
  have hb2 := factor_bounds hd.2.2.2.1 h2
  have hb3 := factor_bounds hd.2.2.2.2.1 h3
  refine ⟨Nat.mul_pos hb2.1 hb3.1, Nat.le_floor ?_⟩
  push_cast
  calc
    (u.1 : ℝ) * u.2 ≤ (2 * d.Q2) * (2 * d.Q3) :=
      mul_le_mul hb2.2.2 hb3.2.2 (Nat.cast_nonneg _) (by linarith [hd.2.2.2.1])
    _ = tailCap d := by unfold tailCap; ring

private theorem tailProducts_subset_prefix
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    tailProducts d ⊆ Finset.Ioc 0 (Nat.floor (tailCap d)) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_Ioc.mpr (tail_product_bounds hd hu)

private theorem tailGamma_zero_off_products (d : MediumAtom) {v : ℕ}
    (hv : v ∉ tailProducts d) : tailGamma d v = 0 := by
  unfold tailGamma
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hu, he⟩ := Finset.mem_filter.mp hu
  exact (hv (Finset.mem_image.mpr ⟨u, hu, he⟩)).elim

private theorem tailGamma_norm_le_tau
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (v : ℕ) :
    ‖tailGamma d v‖ ≤ tau v := by
  let S := (tailLabels d).filter (fun u ↦ u.1 * u.2 = v)
  have hsub : S ⊆ v.divisorsAntidiagonal := by
    intro u hu
    obtain ⟨hu, he⟩ := Finset.mem_filter.mp hu
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨he, by rw [← he]; exact (tail_product_bounds hd hu).1.ne'⟩
  have hcard : v.divisorsAntidiagonal.card = v.divisors.card := by
    rw [← Nat.map_div_right_divisors]
    exact Finset.card_map _
  have hg : ∀ u ∈ S, ‖d.gamma2 u.1 * d.gamma3 u.2‖ ≤ 1 := by
    intro u hu
    obtain ⟨hu, _⟩ := Finset.mem_filter.mp hu
    obtain ⟨h2, h3⟩ := Finset.mem_product.mp hu
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hg2, hg3⟩ := hd
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hg2 _ h2).1 (hg3 _ h3).1
      (norm_nonneg _) zero_le_one
  calc
    ‖tailGamma d v‖ ≤ ∑ u ∈ S, ‖d.gamma2 u.1 * d.gamma3 u.2‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ S, (1 : ℝ) := Finset.sum_le_sum hg
    _ = (S.card : ℝ) := by simp
    _ ≤ tau v := by
      unfold tau
      exact_mod_cast (Finset.card_le_card hsub).trans_eq hcard

/-- Group every original complex tail label before taking its norm. -/
private theorem tail_sum_eq_grouped (d : MediumAtom) (F : ℕ → ℂ) :
    (∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) * F (u.1 * u.2)) =
      ∑ v ∈ tailProducts d, tailGamma d v * F v := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := tailLabels d) (t := tailProducts d) (g := fun u ↦ u.1 * u.2)
    (fun u hu ↦ Finset.mem_image_of_mem _ hu)
    (fun u ↦ (d.gamma2 u.1 * d.gamma3 u.2) * F (u.1 * u.2))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro v _
  rw [tailGamma, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [(Finset.mem_filter.mp hu).2]

private theorem tail_star_sum_eq_grouped (d : MediumAtom) (F : ℕ → ℂ) :
    (∑ u ∈ tailLabels d, star (d.gamma2 u.1 * d.gamma3 u.2) * F (u.1 * u.2)) =
      ∑ v ∈ tailProducts d, star (tailGamma d v) * F v := by
  calc
    _ = star (∑ u ∈ tailLabels d,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (F (u.1 * u.2))) := by
      simp only [star_sum, star_mul', star_star]
    _ = star (∑ v ∈ tailProducts d, tailGamma d v * star (F v)) :=
      congrArg star (tail_sum_eq_grouped d (fun v ↦ star (F v)))
    _ = _ := by simp only [star_sum, star_mul', star_star]

private theorem tail_pair_sum_eq_grouped (d : MediumAtom) (F : ℕ → ℕ → ℂ) :
    (∑ u ∈ tailLabels d, ∑ v ∈ tailLabels d,
      (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
        F (u.1 * u.2) (v.1 * v.2)) =
      ∑ a ∈ tailProducts d, ∑ b ∈ tailProducts d,
        tailGamma d a * star (tailGamma d b) * F a b := by
  calc
    _ = ∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) *
        ∑ v ∈ tailLabels d,
          star (d.gamma2 v.1 * d.gamma3 v.2) * F (u.1 * u.2) (v.1 * v.2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ a ∈ tailProducts d, tailGamma d a *
        ∑ v ∈ tailLabels d,
          star (d.gamma2 v.1 * d.gamma3 v.2) * F a (v.1 * v.2) :=
      tail_sum_eq_grouped d (fun a ↦ ∑ v ∈ tailLabels d,
        star (d.gamma2 v.1 * d.gamma3 v.2) * F a (v.1 * v.2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [tail_star_sum_eq_grouped d (F a), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

private theorem slice_factor_sum (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (F : (ℕ × ℕ × ℕ) → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      (d.q1SliceAtom p).transposedAtom.complexFactorGamma a * F a) =
      ∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) * F (p, u.1, u.2) := by
  simp only [MediumAtom.complexFactorLabels, MediumAtom.complexFactorGamma,
    MediumAtom.q1SliceAtom, MediumAtom.transposedAtom, Finset.sum_product]
  change (∑ q ∈ factorCarrier d.Q1, ∑ a ∈ factorCarrier d.Q2,
    ∑ b ∈ factorCarrier d.Q3,
      ((if q = p then (1 : ℂ) else 0) * d.gamma2 a * d.gamma3 b) * F (q, a, b)) = _
  rw [Finset.sum_eq_single p]
  · simp only [ite_true, one_mul, tailLabels, Finset.sum_product]
  · intro q _ hqp
    simp only [if_neg hqp, zero_mul, Finset.sum_const_zero]
  · exact fun h ↦ (h hp).elim

private theorem slice_factor_star_sum (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (F : (ℕ × ℕ × ℕ) → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma a) * F a) =
      ∑ u ∈ tailLabels d, star (d.gamma2 u.1 * d.gamma3 u.2) * F (p, u.1, u.2) := by
  calc
    _ = star (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
        (d.q1SliceAtom p).transposedAtom.complexFactorGamma a * star (F a)) := by
      simp only [star_sum, star_mul', star_star]
    _ = star (∑ u ∈ tailLabels d,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (F (p, u.1, u.2))) :=
      congrArg star (slice_factor_sum d hp (fun a ↦ star (F a)))
    _ = _ := by simp only [star_sum, star_mul', star_star]

private theorem slice_factor_pair_sum (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (F : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
        (d.q1SliceAtom p).transposedAtom.complexFactorGamma a *
          star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) * F a b) =
      ∑ u ∈ tailLabels d, ∑ v ∈ tailLabels d,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
          F (p, u.1, u.2) (p, v.1, v.2) := by
  calc
    _ = ∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
        (d.q1SliceAtom p).transposedAtom.complexFactorGamma a *
          ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
            star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) * F a b := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) *
        ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
          star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) *
            F (p, u.1, u.2) b := slice_factor_sum d hp _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [slice_factor_star_sum d hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring

private theorem slice_zero_eq_grouped (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (n1 n2 : ℕ) :
    (d.q1SliceAtom p).transposedAtom.commonFactorPairZeroWeight n1 n2 =
      ∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
        tailGamma d v * star (tailGamma d w) *
          ((if ComplexCRT.Compatible (p * v) (p * w) n1 n2 then
            d.V / ((p * v.lcm w : ℕ) : ℝ) * CommonSmoothCutoff.cutoffMass
          else 0 : ℝ) : ℂ) := by
  unfold MediumAtom.commonFactorPairZeroWeight
  rw [slice_factor_pair_sum d hp]
  have hU : (d.q1SliceAtom p).transposedAtom.U = d.V := rfl
  simpa only [complexFactorModulus, Nat.mul_assoc, sharedFirstFactor_lcm, hU] using
    tail_pair_sum_eq_grouped d (fun v w ↦
      ((if ComplexCRT.Compatible (p * v) (p * w) n1 n2 then
        d.V / ((p * v.lcm w : ℕ) : ℝ) * CommonSmoothCutoff.cutoffMass
      else 0 : ℝ) : ℂ))

private theorem tail_lcm_moment
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
      ‖tailGamma d v‖ * ‖tailGamma d w‖ / (v.lcm w : ℝ)) ≤
        (1 + Real.log (tailCap d)) ^ 9 := by
  have hh := MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.sum_abs_lcm_weight_le_log
    2 (one_le_tailCap hd) (tailProducts d) (tailProducts_subset_prefix hd)
    (fun v ↦ ‖tailGamma d v‖)
    (fun v _ ↦ by
      simpa only [abs_norm, fouvryTau_two, tau] using tailGamma_norm_le_tau hd v)
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    exact (abs_of_nonneg (by positivity)).symm
  · norm_num

private def pairGate (p n1 n2 : ℕ) : Prop :=
  n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2

private theorem compatible_implies_pairGate (p v w n1 n2 : ℕ)
    (h : ComplexCRT.Compatible (p * v) (p * w) n1 n2) : pairGate p n1 n2 := by
  rw [sharedFirstFactor_compatible_iff] at h
  exact ⟨h.1.of_dvd_right (dvd_mul_right p v),
    h.2.1.of_dvd_right (dvd_mul_right p w), h.2.2.of_dvd (dvd_mul_right p (v.gcd w))⟩

private theorem slice_zero_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) (n1 n2 : ℕ) :
    ‖(d.q1SliceAtom p).transposedAtom.commonFactorPairZeroWeight n1 n2‖ ≤
      if pairGate p n1 n2 then
        |CommonSmoothCutoff.cutoffMass| * d.V / (p : ℝ) *
          (1 + Real.log (tailCap d)) ^ 9 else 0 := by
  have hp0 := (factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1).1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  rw [slice_zero_eq_grouped d (Finset.mem_filter.mp hp).1]
  by_cases hg : pairGate p n1 n2
  · rw [if_pos hg]
    calc
      _ ≤ ∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
          (|CommonSmoothCutoff.cutoffMass| * d.V / (p : ℝ)) *
            (‖tailGamma d v‖ * ‖tailGamma d w‖ / (v.lcm w : ℝ)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro v _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro w _
        by_cases hc : ComplexCRT.Compatible (p * v) (p * w) n1 n2
        · have hlcm : (0 : ℝ) ≤ (v.lcm w : ℝ) := Nat.cast_nonneg _
          simp only [if_pos hc, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
            abs_mul, abs_div, abs_of_nonneg hV, Nat.cast_mul,
            abs_of_nonneg hpR.le, abs_of_nonneg hlcm]
          exact le_of_eq (by ring)
        · simp only [if_neg hc, Complex.ofReal_zero, mul_zero, norm_zero]
          positivity
      _ = (|CommonSmoothCutoff.cutoffMass| * d.V / (p : ℝ)) *
          ∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
            ‖tailGamma d v‖ * ‖tailGamma d w‖ / (v.lcm w : ℝ) := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_lcm_moment hd) (by positivity)
  · rw [if_neg hg]
    have hz : (∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
        tailGamma d v * star (tailGamma d w) *
          ((if ComplexCRT.Compatible (p * v) (p * w) n1 n2 then
            d.V / ((p * v.lcm w : ℕ) : ℝ) * CommonSmoothCutoff.cutoffMass
          else 0 : ℝ) : ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      apply Finset.sum_eq_zero
      intro w _
      have hc : ¬ComplexCRT.Compatible (p * v) (p * w) n1 n2 :=
        fun h ↦ hg (compatible_implies_pairGate p v w n1 n2 h)
      simp only [if_neg hc, Complex.ofReal_zero, mul_zero]
    rw [hz, norm_zero]

private theorem transposed_beta_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖d.transposedAtom.beta n‖ ≤ 1 := by
  have hAlpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
    exact hAlpha
  change ‖if n ∈ d.alphaCarrier then d.alpha n else 0‖ ≤ 1
  by_cases hn : n ∈ d.alphaCarrier
  · simpa only [if_pos hn] using hAlpha n hn
  · simp only [if_neg hn, norm_zero, zero_le_one]

private theorem card_primitiveCarrier_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.primitiveFirstFactorCarrier.card : ℝ) ≤ 2 * d.Q1 := by
  have hsub : d.primitiveFirstFactorCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.Q1)) := by
    intro p hp
    exact Finset.mem_Ioc.mpr
      ⟨(factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1).1,
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩
  have hc := Finset.card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hc
  exact (show (d.primitiveFirstFactorCarrier.card : ℝ) ≤ (Nat.floor (2 * d.Q1) : ℝ) by
    exact_mod_cast hc).trans (Nat.floor_le (by linarith [hd.2.2.1]))

private theorem slice_large_zero_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) (Y : ℝ) :
    ‖(d.q1SliceAtom p).transposedAtom.commonLargeBetaGCDZeroPart Y‖ ≤
      (|CommonSmoothCutoff.cutoffMass| * d.V / (p : ℝ) *
        (1 + Real.log (tailCap d)) ^ 9) *
          ((sharedPrimitiveLargeGCDPairs d.transposedAtom.betaCarrier p Y).card : ℝ) := by
  let K := |CommonSmoothCutoff.cutoffMass| * d.V / (p : ℝ) *
    (1 + Real.log (tailCap d)) ^ 9
  have hK : 0 ≤ K := by
    dsimp [K]
    have hV : 0 ≤ d.V := by linarith [hd.2.1]
    have hH : 0 ≤ 1 + Real.log (tailCap d) := by
      linarith [Real.log_nonneg (one_le_tailCap hd)]
    positivity
  change ‖∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
    if Y < (n1.gcd n2 : ℝ) then
      d.transposedAtom.beta n1 * star (d.transposedAtom.beta n2) *
        (d.q1SliceAtom p).transposedAtom.commonFactorPairZeroWeight n1 n2 else 0‖ ≤ _
  calc
    _ ≤ ∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
        if n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2 ∧ Y < (n1.gcd n2 : ℝ)
          then K else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n1 _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n2 _
      by_cases hy : Y < (n1.gcd n2 : ℝ)
      · rw [if_pos hy]
        have hb := slice_zero_norm_le hd hp n1 n2
        have hcoef : ‖d.transposedAtom.beta n1‖ * ‖d.transposedAtom.beta n2‖ ≤ 1 := by
          simpa only [one_mul] using mul_le_mul
            (transposed_beta_norm_le_one hd n1) (transposed_beta_norm_le_one hd n2)
            (norm_nonneg _) zero_le_one
        by_cases hc : pairGate p n1 n2
        · have hfull : n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2 ∧
              Y < (n1.gcd n2 : ℝ) := ⟨hc.1, hc.2.1, hc.2.2, hy⟩
          rw [if_pos hc] at hb
          rw [if_pos hfull]
          simp only [norm_mul, norm_star]
          calc
            _ ≤ 1 * K := mul_le_mul hcoef hb (norm_nonneg _) zero_le_one
            _ = K := one_mul K
        · have hnot : ¬(n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2 ∧
              Y < (n1.gcd n2 : ℝ)) := fun h ↦ hc ⟨h.1, h.2.1, h.2.2.1⟩
          rw [if_neg hc] at hb
          have hz := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
          simp only [hz, mul_zero, norm_zero, if_neg hnot, le_refl]
      · have hnot : ¬(n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2 ∧
            Y < (n1.gcd n2 : ℝ)) := fun h ↦ hy h.2.2.2
        simp only [if_neg hy, if_neg hnot, norm_zero, le_refl]
    _ = _ := by
      rw [← Finset.sum_product', ← Finset.sum_filter]
      simp only [sharedPrimitiveLargeGCDPairs, Finset.sum_const, nsmul_eq_mul]
      ring

/-- Raw zero is paid with its actual paired mask; the common first factor
remains in the denominator before the primitive p sum is taken. -/
theorem shared_large_zero_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖d.sharedLargePairedGCDZero Y‖ ≤
      |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 9 *
        (16 * d.U ^ 2 / (d.Q1 * Y) + 4 * d.U * (1 + Real.log (2 * d.U))) := by
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hU : 0 ≤ d.U := by linarith [hd.1]
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  have hH : 0 ≤ 1 + Real.log (tailCap d) := by
    linarith [Real.log_nonneg (one_le_tailCap hd)]
  have hLU : 0 ≤ 1 + Real.log (2 * d.U) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.U by linarith [hd.1])]
  have hrect (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      ‖(d.q1SliceAtom p).transposedAtom.commonLargeBetaGCDZeroPart Y‖ ≤
        (|CommonSmoothCutoff.cutoffMass| * d.V / d.Q1 *
          (1 + Real.log (tailCap d)) ^ 9) *
            (8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U))) := by
    obtain ⟨hp0, hQp, _⟩ := factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1
    have hcount := d.card_sharedPrimitiveLargeGCDPairs_le hd.1 hY hp0
    have hc : ((sharedPrimitiveLargeGCDPairs d.transposedAtom.betaCarrier p Y).card : ℝ) ≤
        8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U)) :=
      hcount.trans (add_le_add (div_le_div_of_nonneg_left (by positivity)
        (mul_pos hQ hY0) (mul_le_mul_of_nonneg_right hQp hY0.le)) le_rfl)
    exact (slice_large_zero_norm_le hd hp Y).trans (mul_le_mul
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) hQ hQp) (pow_nonneg hH _)) hc
      (Nat.cast_nonneg _) (by positivity))
  unfold MediumAtom.sharedLargePairedGCDZero
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        ‖(d.q1SliceAtom p).transposedAtom.commonLargeBetaGCDZeroPart Y‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier,
        (|CommonSmoothCutoff.cutoffMass| * d.V / d.Q1 *
          (1 + Real.log (tailCap d)) ^ 9) *
            (8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U))) :=
      Finset.sum_le_sum hrect
    _ = (d.primitiveFirstFactorCarrier.card : ℝ) *
        ((|CommonSmoothCutoff.cutoffMass| * d.V / d.Q1 *
          (1 + Real.log (tailCap d)) ^ 9) *
            (8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U)))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d.Q1) *
        ((|CommonSmoothCutoff.cutoffMass| * d.V / d.Q1 *
          (1 + Real.log (tailCap d)) ^ 9) *
            (8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U)))) :=
      mul_le_mul_of_nonneg_right (card_primitiveCarrier_le hd) (by positivity)
    _ = _ := by field_simp [hQ.ne', hY0.ne']; ring

/-- The full raw zero and full nonzero series have exactly the same mask as W. -/
theorem shared_largeW_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    d.sharedLargePairedGCDW Y =
      d.sharedLargePairedGCDZero Y + d.sharedLargePairedGCDNonzero Y := by
  unfold MediumAtom.sharedLargePairedGCDW MediumAtom.sharedLargePairedGCDZero
    MediumAtom.sharedLargePairedGCDNonzero
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact transposed_largeW_eq_zero_add_nonzero (mediumAdmissible_q1SliceAtom hd hp) Y

private theorem shared_nonzero_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    ‖d.sharedLargePairedGCDNonzero Y‖ ≤
      ‖d.sharedLargePairedGCDW Y‖ + ‖d.sharedLargePairedGCDZero Y‖ := by
  have he : d.sharedLargePairedGCDNonzero Y =
      d.sharedLargePairedGCDW Y - d.sharedLargePairedGCDZero Y := by
    rw [shared_largeW_eq_zero_add_nonzero hd]
    ring
  rw [he]
  exact norm_sub_le _ _

private def outside (d : MediumAtom) : ℝ :=
  (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)

private def betaLog (d : MediumAtom) : ℝ := 1 + Real.log (2 * d.V)
private def capLog (d : MediumAtom) : ℝ := 1 + Real.log d.physicalFactorCap

private theorem outside_nonneg (d : MediumAtom) : 0 ≤ outside d := by
  unfold outside
  positivity

private theorem log_and_scale_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    d.U ≤ d.V ∧ d.Q1 ≤ d.U ∧ 1 ≤ betaLog d ∧ 1 ≤ capLog d ∧
      1 + Real.log (2 * d.U) ≤ betaLog d ∧
        1 + Real.log (tailCap d) ≤ capLog d := by
  have hX := one_le_scale hd
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hsq : d.U ^ 2 ≤ d.scale := by
    apply (TransposedPrimitiveUMoment.U_sq_lt_scale_rpow hd).le.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (show 1 - 8 * sigma ≤ 1 by linarith)
  have hUV : d.U ≤ d.V := by
    change d.U ^ 2 ≤ d.U * d.V at hsq
    nlinarith
  have hQU : d.Q1 ≤ d.U := by
    have hq := hd.2.2.2.2.2.2.2.2.1.le
    exact hq.trans (mul_le_of_le_one_right hU.le
      (Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)))
  have hTail : tailCap d ≤ d.physicalFactorCap := by
    unfold tailCap MediumAtom.physicalFactorCap
    have h2 : 0 ≤ d.Q2 := by linarith [hd.2.2.2.1]
    have h3 : 0 ≤ d.Q3 := by linarith [hd.2.2.2.2.1]
    nlinarith [mul_nonneg h2 h3, mul_le_mul_of_nonneg_right hd.2.2.1 (mul_nonneg h2 h3)]
  refine ⟨hUV, hQU, ?_, ?_, ?_, ?_⟩
  · dsimp [betaLog]
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  · dsimp [capLog]
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  · dsimp [betaLog]
    exact add_le_add (le_refl 1) (Real.log_le_log (by linarith)
      (mul_le_mul_of_nonneg_left hUV (by norm_num)))
  · dsimp [capLog]
    exact add_le_add (le_refl 1) (Real.log_le_log
      (zero_lt_one.trans_le (one_le_tailCap hd)) hTail)

private theorem bracket_bound (a b q Y L H : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hY : 0 < Y)
    (hL : 1 ≤ L) (hH : H ≤ L) :
    a / Y + b * q * H ≤ (a + b) * L * (1 / Y + q) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  calc
    _ ≤ a / Y * L + b * q * L := add_le_add
      (le_mul_of_one_le_right (div_nonneg ha hY.le) hL)
      (mul_le_mul_of_nonneg_left hH (mul_nonneg hb hq))
    _ ≤ (a / Y * L + b * q * L) + (a * q * L + b / Y * L) :=
      le_add_of_nonneg_right (add_nonneg (by positivity) (by positivity))
    _ = _ := by ring

private theorem outside_zero_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d)
    {Y : ℝ} (hY : 1 ≤ Y) :
    outside d * ‖d.cleanedAlphaAtom.sharedLargePairedGCDZero Y‖ ≤
      (80 * |CommonSmoothCutoff.cutoffMass|) * d.scale ^ 2 *
        betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9 *
          (1 / Y + d.Q1 / d.U) := by
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  obtain ⟨_, _, hL, hH, hLU, hTH⟩ := log_and_scale_bounds hsigma hd
  have hT : 0 ≤ 1 + Real.log (tailCap d) := by
    linarith [Real.log_nonneg (one_le_tailCap hd)]
  have hLU0 : 0 ≤ 1 + Real.log (2 * d.U) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.U by linarith [hd.1])]
  have hz := shared_large_zero_bound (mediumAdmissible_cleanedAlphaAtom hd) hY
  change ‖d.cleanedAlphaAtom.sharedLargePairedGCDZero Y‖ ≤
    |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 9 *
      (16 * d.U ^ 2 / (d.Q1 * Y) + 4 * d.U * (1 + Real.log (2 * d.U))) at hz
  calc
    _ ≤ (4 * d.V * d.Q1 * betaLog d ^ ((2 ^ B) ^ 2 - 1)) *
        (|CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 9 *
          (16 * d.U ^ 2 / (d.Q1 * Y) + 4 * d.U * (1 + Real.log (2 * d.U)))) :=
      mul_le_mul (d.sharedFirstFactor_outside_le hd) hz (norm_nonneg _) (by
        dsimp [betaLog]; positivity)
    _ = |CommonSmoothCutoff.cutoffMass| * d.scale ^ 2 *
        betaLog d ^ ((2 ^ B) ^ 2 - 1) * (1 + Real.log (tailCap d)) ^ 9 *
          (64 / Y + 16 * (d.Q1 / d.U) * (1 + Real.log (2 * d.U))) := by
      unfold MediumAtom.scale
      field_simp [hU.ne', hQ.ne', hY0.ne']
      ring
    _ ≤ |CommonSmoothCutoff.cutoffMass| * d.scale ^ 2 *
        betaLog d ^ ((2 ^ B) ^ 2 - 1) * capLog d ^ 9 *
          ((64 + 16) * betaLog d * (1 / Y + d.Q1 / d.U)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTH 9) (by positivity)
      · exact bracket_bound 64 16 (d.Q1 / d.U) Y (betaLog d)
          (1 + Real.log (2 * d.U)) (by norm_num) (by norm_num) (by positivity) hY0 hL hLU
      · positivity
      · positivity
    _ = _ := by rw [pow_succ]; ring

private theorem outside_wholeW_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      0 < sigma → MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ, 1 ≤ Y →
        outside d * ‖d.cleanedAlphaAtom.sharedLargePairedGCDW Y‖ ≤
          C * d.scale ^ epsilon * d.scale ^ 2 *
            betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9 *
              (1 / Y + d.Q1 / d.U) := by
  obtain ⟨C, hC, hw⟩ := cleanedAlpha_sharedLargePairedGCDW_bound kappa hepsilon
  refine ⟨400 * C, by positivity, fun B sigma c0 d hsigma hd Y hY ↦ ?_⟩
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hX : 0 ≤ d.scale := zero_le_one.trans (one_le_scale hd)
  obtain ⟨hUV, hQU, hL, hH, hLU, _⟩ := log_and_scale_bounds hsigma hd
  have hLU0 : 0 ≤ 1 + Real.log (2 * d.U) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.U by linarith [hd.1])]
  have hQV : d.Q1 ≤ d.V := hQU.trans hUV
  have hratio : 4 * d.V / d.Q1 + 1 ≤ 5 * d.V / d.Q1 := by
    apply (le_div_iff₀ hQ).mpr
    field_simp [hQ.ne']
    nlinarith
  have hcap : (1 : ℝ) ≤ capLog d ^ 9 := one_le_pow₀ hH
  calc
    _ ≤ (4 * d.V * d.Q1 * betaLog d ^ ((2 ^ B) ^ 2 - 1)) *
        (C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
          (16 * d.U ^ 2 / Y + 4 * d.Q1 * d.U * (1 + Real.log (2 * d.U)))) :=
      mul_le_mul (d.sharedFirstFactor_outside_le hd) (hw B sigma c0 d hd Y hY)
        (norm_nonneg _) (by positivity)
    _ ≤ (4 * d.V * d.Q1 * betaLog d ^ ((2 ^ B) ^ 2 - 1)) *
        (C * d.scale ^ epsilon * (5 * d.V / d.Q1) *
          (16 * d.U ^ 2 / Y + 4 * d.Q1 * d.U * (1 + Real.log (2 * d.U)))) := by
      gcongr
    _ = C * d.scale ^ epsilon * d.scale ^ 2 * betaLog d ^ ((2 ^ B) ^ 2 - 1) *
        (320 / Y + 80 * (d.Q1 / d.U) * (1 + Real.log (2 * d.U))) := by
      unfold MediumAtom.scale
      field_simp [hU.ne', hQ.ne', hY0.ne']
      ring
    _ ≤ C * d.scale ^ epsilon * d.scale ^ 2 * betaLog d ^ ((2 ^ B) ^ 2 - 1) *
        ((320 + 80) * betaLog d * (1 / Y + d.Q1 / d.U)) :=
      mul_le_mul_of_nonneg_left
        (bracket_bound 320 80 (d.Q1 / d.U) Y (betaLog d)
          (1 + Real.log (2 * d.U)) (by norm_num) (by norm_num) (by positivity) hY0 hL hLU)
        (by positivity)
    _ ≤ (C * d.scale ^ epsilon * d.scale ^ 2 * betaLog d ^ ((2 ^ B) ^ 2 - 1) *
        ((320 + 80) * betaLog d * (1 / Y + d.Q1 / d.U))) * capLog d ^ 9 :=
      le_mul_of_one_le_right (by positivity) hcap
    _ = _ := by rw [pow_succ]; ring

private theorem outside_nonzero_finite_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      0 < sigma → MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ, 1 ≤ Y →
        outside d * ‖d.cleanedAlphaAtom.sharedLargePairedGCDNonzero Y‖ ≤
          C * d.scale ^ epsilon * d.scale ^ 2 *
            betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9 *
              (1 / Y + d.Q1 / d.U) := by
  obtain ⟨C, hC, hwhole⟩ := outside_wholeW_bound kappa hepsilon
  refine ⟨C + 80 * |CommonSmoothCutoff.cutoffMass|, by positivity,
    fun B sigma c0 d hsigma hd Y hY ↦ ?_⟩
  have hL : 1 ≤ betaLog d := (log_and_scale_bounds hsigma hd).2.2.1
  have hH : 1 ≤ capLog d := (log_and_scale_bounds hsigma hd).2.2.2.1
  have hU : 0 ≤ d.U := by linarith [hd.1]
  have hQ : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hX : 0 ≤ d.scale := zero_le_one.trans (one_le_scale hd)
  have hXeps : 1 ≤ d.scale ^ epsilon := Real.one_le_rpow (one_le_scale hd) hepsilon.le
  have hz := outside_zero_bound hsigma hd hY
  have hz' : outside d * ‖d.cleanedAlphaAtom.sharedLargePairedGCDZero Y‖ ≤
      (80 * |CommonSmoothCutoff.cutoffMass|) * d.scale ^ epsilon * d.scale ^ 2 *
        betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9 *
          (1 / Y + d.Q1 / d.U) := by
    apply hz.trans
    calc
      _ ≤ ((80 * |CommonSmoothCutoff.cutoffMass|) * d.scale ^ 2 *
          betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9 *
            (1 / Y + d.Q1 / d.U)) * d.scale ^ epsilon :=
        le_mul_of_one_le_right (by positivity) hXeps
      _ = _ := by ring
  calc
    _ ≤ outside d * (‖d.cleanedAlphaAtom.sharedLargePairedGCDW Y‖ +
        ‖d.cleanedAlphaAtom.sharedLargePairedGCDZero Y‖) :=
      mul_le_mul_of_nonneg_left
        (shared_nonzero_norm_le (mediumAdmissible_cleanedAlphaAtom hd) Y) (outside_nonneg d)
    _ = outside d * ‖d.cleanedAlphaAtom.sharedLargePairedGCDW Y‖ +
        outside d * ‖d.cleanedAlphaAtom.sharedLargePairedGCDZero Y‖ := by ring
    _ ≤ C * d.scale ^ epsilon * d.scale ^ 2 *
          betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9 *
            (1 / Y + d.Q1 / d.U) +
        (80 * |CommonSmoothCutoff.cutoffMass|) * d.scale ^ epsilon * d.scale ^ 2 *
          betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9 *
            (1 / Y + d.Q1 / d.U) :=
      add_le_add (hwhole B sigma c0 d hsigma hd Y hY) hz'
    _ = _ := by ring

private theorem first_factor_relative_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.Q1 / d.U ≤ d.scale ^ (-sigma) := by
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  apply (div_le_iff₀ hU).mpr
  simpa only [mul_comm] using hd.2.2.2.2.2.2.2.2.1.le

private theorem relative_power_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    1 / d.scale ^ (sigma / 4) + d.Q1 / d.U ≤ 2 * d.scale ^ (-(sigma / 4)) := by
  have hX1 := one_le_scale hd
  have hi : 1 / d.scale ^ (sigma / 4) = d.scale ^ (-(sigma / 4)) := by
    rw [Real.rpow_neg (zero_le_one.trans hX1), one_div]
  have hq : d.Q1 / d.U ≤ d.scale ^ (-(sigma / 4)) :=
    (first_factor_relative_bound hd).trans
      (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith))
  rw [hi]
  linarith

private theorem outside_nonzero_power_bound (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
        outside d * ‖d.cleanedAlphaAtom.sharedLargePairedGCDNonzero
          (d.scale ^ (sigma / 4))‖ ≤ C * d.scale ^ (2 - sigma / 8) := by
  obtain ⟨C, hC, hfinite⟩ := outside_nonzero_finite_bound kappa
    (by linarith : 0 < sigma / 16)
  obtain ⟨x0, hx0, hlogs⟩ := eventually_actual_log_cost_le_rpow
    (((2 ^ B) ^ 2 - 1) + 1) 9 sigma hsigma (by linarith : 0 < sigma / 16)
  refine ⟨2 * C, by positivity, x0, hx0, fun d hd hx ↦ ?_⟩
  have hX1 := one_le_scale hd
  have hX : 0 < d.scale := zero_lt_one.trans_le hX1
  have hY : 1 ≤ d.scale ^ (sigma / 4) := Real.one_le_rpow hX1 (by linarith)
  have hU : 0 ≤ d.U := by linarith [hd.1]
  have hQ : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
  have hY0 : 0 < d.scale ^ (sigma / 4) := Real.rpow_pos_of_pos hX _
  have hL : 0 ≤ betaLog d := zero_le_one.trans (log_and_scale_bounds hsigma hd).2.2.1
  have hH : 0 ≤ capLog d := zero_le_one.trans (log_and_scale_bounds hsigma hd).2.2.2.1
  have hlogs' : betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9 ≤
      d.scale ^ (sigma / 16) := hlogs B kappa c0 d hd hx
  calc
    _ ≤ C * d.scale ^ (sigma / 16) * d.scale ^ 2 *
        betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9 *
          (1 / d.scale ^ (sigma / 4) + d.Q1 / d.U) :=
      hfinite B sigma c0 d hsigma hd _ hY
    _ = (C * d.scale ^ (sigma / 16) * d.scale ^ 2) *
        (betaLog d ^ (((2 ^ B) ^ 2 - 1) + 1) * capLog d ^ 9) *
          (1 / d.scale ^ (sigma / 4) + d.Q1 / d.U) := by ring
    _ ≤ (C * d.scale ^ (sigma / 16) * d.scale ^ 2) *
        d.scale ^ (sigma / 16) * (2 * d.scale ^ (-(sigma / 4))) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hlogs' (by positivity))
        (relative_power_bound hsigma hd) (by positivity) (by positivity)
    _ = (2 * C) *
        (d.scale ^ (sigma / 16) * d.scale ^ (2 : ℝ) *
          d.scale ^ (sigma / 16) * d.scale ^ (-(sigma / 4))) := by
      rw [Real.rpow_two]
      ring
    _ = _ := by
      rw [← Real.rpow_add hX, ← Real.rpow_add hX, ← Real.rpow_add hX]
      congr 2
      ring

end SharedFirstFactorLargePairedGCDNonzero

open SharedFirstFactorLargePairedGCDNonzero

/-- Arbitrary logarithmic saving for the full same-mask large-paired-gcd
Fourier remainder, after the actual original beta and gamma1 moments. -/
theorem actual_betaL2_gamma1L2_cleaned_sharedLargePairedGCDNonzero_log_payment
    (B : ℕ) (sigma kappa c0 A : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          ‖d.cleanedAlphaAtom.sharedLargePairedGCDNonzero (d.scale ^ (sigma / 4))‖ ≤
            d.scale ^ 2 / (Real.log d.scale) ^ A := by
  obtain ⟨C, hC, x1, hx1, hpower⟩ := outside_nonzero_power_bound B sigma kappa c0 hsigma
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget C A hC.le (by linarith : 0 < sigma / 8))
  refine ⟨max x1 x2, lt_of_lt_of_le hx1 (le_max_left _ _), fun d hd hx ↦ ?_⟩
  exact (hpower d hd ((le_max_left _ _).trans hx)).trans
    (hx2 d.scale ((le_max_right _ _).trans hx))

end

end ImbalancedChen.Part3
