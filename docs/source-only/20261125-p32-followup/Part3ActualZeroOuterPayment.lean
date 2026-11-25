import ImbalancedChen.Part3ActualLogModeWeightedPhysicalDEnergy
import ImbalancedChen.Part3ActualZeroTagFreeEpsilonPayment
import Mathlib.Analysis.PSeries

/-!
# Actual completed zero difference: physical normalization and outer costs

This file continues the zero-difference term in the frozen 20261106 manuscript,
`analytic-appendix.tex`, `ana:W4-expansion` and `ana:bare-Cauchy-factor`.
It uses the existing actual six smooth pieces and original Fourier coefficients.
The original scalar is NOT identified with a zero/nonzero energy decomposition.

The public bounds retain the physical tail gcd D, its actual divisor delta,
the paired gcd g, the supported part l, both real-projection branches, and
the full root/residue triangle cost. In particular D is not assumed to be a
vanishing subpower, and no target-shaped zero budget is an input.

The finite D/divisor bound and the g/l enumeration below are unconditional.
Binding the final arithmetic enumeration to the complete original outer
scalar and passing its mode limits remain separate obligations. No spectral
estimate for the nonzero completed kernel is asserted here.

SOURCE WRITTEN; compilation and kernel verification are recorded separately.
-/

namespace ImbalancedChen.Part3.ActualZeroOuterPayment

noncomputable section

open Classical Finset
open GeneralDActiveOuterEnergySourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualCompletedZeroPaymentSourceOnly ActualM2FinitePoissonAdapterSourceOnly
open ActualPacketBCFCardEnergySourceOnly ActualModePhysicalDPrefactorSourceOnly
open ActualLogModeWeightedCauchySourceOnly ActualLogTagHSupportSourceOnly
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The zero-six geometry before the actual tag height and divisor envelope. -/
def zeroGeometry (e : MediumAtom) (D delta g l : ℕ) : ℝ :=
  1512 * scaleB e delta l * scaleC e D g l * scaleF e D g *
    (e.Q2 * (delta : ℝ) / (D : ℝ))

/-- The actual zero part of the SAME weighted six-piece energy. The two
real-projection branches retain their common coefficient norm and their 1/2. -/
def weightedZeroSix (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (K : Finset (ℤ × ℤ)) : ℝ :=
  ∑ m ∈ K, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ *
    ((actualZeroSix e D delta g l Z tag m false u k).re +
      (actualZeroSix e D delta g l Z tag m true u k).re) / 2

/-- The literal remaining completed six-piece energy. The subtraction is
inside the existing completed expression, not a replacement coefficient family.
`completedModePiece_eq_zero_add_nonzero` identifies each of its six differences
with the original nonzeroSource sum. Its sign is deliberately retained. -/
def weightedNonzeroSix (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (K : Finset (ℤ × ℤ)) : ℝ :=
  ∑ m ∈ K, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ *
    (((completedModeSix e D delta g l Z tag m false u k -
        actualZeroSix e D delta g l Z tag m false u k).re) +
      ((completedModeSix e D delta g l Z tag m true u k -
        actualZeroSix e D delta g l Z tag m true u k).re)) / 2

theorem weightedModeMass6_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)] (hdelta : 0 < delta) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (K : Finset (ℤ × ℤ)) :
    weightedModeMass6 e D delta g l Z tag u k K =
      weightedZeroSix e D delta g l Z tag u k K +
        weightedNonzeroSix e D delta g l Z tag u k K := by
  unfold weightedModeMass6 weightedZeroSix weightedNonzeroSix
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _hm
  rw [modeMass6_eq_completed_re he D delta g l hdelta hl,
    modeMass6_eq_completed_re he D delta g l hdelta hl]
  simp only [Complex.sub_re]
  ring

/-- A signed zero energy is bounded by its proved actual zero-six norm.
No positivity of an individual zero piece is used. -/
theorem weightedZeroSix_le_actual_tag
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hdeltaD : delta ∣ D)
    (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (K : Finset (ℤ × ℤ)) :
    weightedZeroSix e D delta g l Z tag u k K ≤
      zeroGeometry e D delta g l * (tagFrequencyBound tag : ℝ) *
        (actualTagTau e D delta tag : ℝ) * coefficientMass e D Z tag K := by
  let Z0 : ℝ := zeroGeometry e D delta g l * (tagFrequencyBound tag : ℝ) *
    (actualTagTau e D delta tag : ℝ)
  have hz (m : ℤ × ℤ) (negative : Bool) :
      (actualZeroSix e D delta g l Z tag m negative u k).re ≤ Z0 := by
    have hnorm := actualZeroSix_norm_le_tag he D delta g l hD hdelta hdeltaD
      hg hl Z tag m negative u k
    exact (Complex.re_le_norm _).trans (by
      convert hnorm using 1 <;> dsimp [Z0, zeroGeometry] <;> ring)
  calc
    _ ≤ ∑ m ∈ K, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m‖ * Z0 := by
      apply sum_le_sum
      intro m hm
      have havg :
          ((actualZeroSix e D delta g l Z tag m false u k).re +
            (actualZeroSix e D delta g l Z tag m true u k).re) / 2 ≤ Z0 := by
        linarith [hz m false, hz m true]
      have h := mul_le_mul_of_nonneg_left havg
        (norm_nonneg (_root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m))
      convert h using 1 <;> ring
    _ = _ := by
      rw [← sum_mul]
      dsimp only [Z0, coefficientMass]
      ring

/-- Actual finite scalar Cauchy after paying its zero difference. The
nonzero completed energy stays on the same right side with its original sign. -/
theorem actual_finite_log_mode_sq_le_paid_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hdeltaD : delta ∣ D)
    (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (K : Finset (ℤ × ℤ)) :
    let e := d.cleanedAlphaAtom
    ‖finiteLogScalar e Yb Ys D delta g l Z tag u k K‖ ^ 2 ≤
      normalizedPacketEnergy324 d D delta g l *
        (ordinaryTauMax (g*l)
          (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ) *
        coefficientMass e D Z tag K *
        (zeroGeometry e D delta g l * (tagFrequencyBound tag : ℝ) *
          (actualTagTau e D delta tag : ℝ) * coefficientMass e D Z tag K +
            weightedNonzeroSix e D delta g l Z tag u k K) := by
  dsimp only
  let e := d.cleanedAlphaAtom
  have he := mediumAdmissible_cleanedAlphaAtom hd
  have hc := actual_finite_log_mode_Cauchy_physicalD hd Yb Ys hD hdelta hg hl
    Z tag u k K
  dsimp only at hc
  rw [weightedModeMass6_eq_zero_add_nonzero he D delta g l hdelta hl] at hc
  have hz := weightedZeroSix_le_actual_tag he D delta g l hD hdelta hdeltaD hg hl
    Z tag u k K
  refine hc.trans (mul_le_mul_of_nonneg_left (add_le_add_right hz _) ?_)
  have hU : 0 ≤ d.U := zero_le_one.trans hd.1
  have hV : 0 ≤ d.V := zero_le_one.trans hd.2.1
  have hQ : 0 ≤ d.Q1 := zero_le_one.trans hd.2.2.1
  have hS : 0 ≤ d.Q2 := zero_le_one.trans hd.2.2.2.1
  have hR : 0 ≤ d.Q3 := zero_le_one.trans hd.2.2.2.2.1
  unfold normalizedPacketEnergy324 coefficientMass
  positivity

private theorem coefficientMass_nonneg (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (K : Finset (ℤ × ℤ)) : 0 ≤ coefficientMass e D Z tag K := by
  exact sum_nonneg (fun _ _ => norm_nonneg _)

private theorem weightedModeMass6_nonneg (e : MediumAtom) (D delta g l : ℕ)
    [NeZero (g*l)] (Z : ℝ) (tag : ℕ × Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (K : Finset (ℤ × ℤ)) :
    0 ≤ weightedModeMass6 e D delta g l Z tag u k K := by
  unfold weightedModeMass6
  apply sum_nonneg
  intro m _hm
  apply mul_nonneg (norm_nonneg _)
  apply div_nonneg _ (by norm_num)
  apply add_nonneg <;> exact sixSmoothMass_nonneg _ _ _ _

/-- Cross-tag Cauchy on the ACTUAL finite tag/residue carrier. Its first
factor is the sum of the original Fourier coefficient masses, not the
cardinality of the tags. Root fibres have not yet been combined. -/
theorem actual_tag_residue_scalar_sq_le_paid_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hdeltaD : delta ∣ D)
    (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (u : (ZMod (g*l))ˣ) (K : Finset (ℤ × ℤ)) :
    let e := d.cleanedAlphaAtom
    let T := actualTagResidueCarrier e D Z (g*l)
    ‖∑ q ∈ T, finiteLogScalar e Yb Ys D delta g l Z q.1 u q.2 K‖ ^ 2 ≤
      (normalizedPacketEnergy324 d D delta g l *
        (ordinaryTauMax (g*l)
          (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ)) *
        (∑ q ∈ T, coefficientMass e D Z q.1 K) *
        ((∑ q ∈ T, zeroGeometry e D delta g l * (tagFrequencyBound q.1 : ℝ) *
          (actualTagTau e D delta q.1 : ℝ) * coefficientMass e D Z q.1 K) +
          ∑ q ∈ T, weightedNonzeroSix e D delta g l Z q.1 u q.2 K) := by
  dsimp only
  let e := d.cleanedAlphaAtom
  let T := actualTagResidueCarrier e D Z (g*l)
  let E := normalizedPacketEnergy324 d D delta g l *
    (ordinaryTauMax (g*l)
      (packetBox (scaleB e delta l) (scaleC e D g l) (scaleF e D g)) : ℝ)
  let a := fun q : (ℕ × Bool) × ZMod (g*l) => coefficientMass e D Z q.1 K
  let W := fun q : (ℕ × Bool) × ZMod (g*l) =>
    weightedModeMass6 e D delta g l Z q.1 u q.2 K
  let r := fun q : (ℕ × Bool) × ZMod (g*l) =>
    ‖finiteLogScalar e Yb Ys D delta g l Z q.1 u q.2 K‖
  have he := mediumAdmissible_cleanedAlphaAtom hd
  have hS : 0 ≤ d.Q2 := zero_le_one.trans hd.2.2.2.1
  have hE : 0 ≤ E := by
    unfold E normalizedPacketEnergy324
    positivity
  have ha (q) : 0 ≤ a q := coefficientMass_nonneg e D Z q.1 K
  have hW (q) : 0 ≤ W q := weightedModeMass6_nonneg e D delta g l Z q.1 u q.2 K
  have hp (q) : r q ^ 2 ≤ a q * (E * W q) := by
    have h := actual_finite_log_mode_Cauchy_physicalD hd Yb Ys hD hdelta hg hl
      Z q.1 u q.2 K
    dsimp only at h
    convert h using 1 <;> dsimp [r, a, E, W] <;> ring
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul T
    (r := r) (f := a) (g := fun q => E * W q)
    (fun q _ => ha q) (fun q _ => mul_nonneg hE (hW q)) (fun q _ => hp q)
  have htri : ‖∑ q ∈ T, finiteLogScalar e Yb Ys D delta g l Z q.1 u q.2 K‖ ≤
      ∑ q ∈ T, r q := norm_sum_le _ _
  have hsquare : ‖∑ q ∈ T, finiteLogScalar e Yb Ys D delta g l Z q.1 u q.2 K‖^2 ≤
      (∑ q ∈ T, r q)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hpaid : (∑ q ∈ T, W q) ≤
      (∑ q ∈ T, zeroGeometry e D delta g l * (tagFrequencyBound q.1 : ℝ) *
        (actualTagTau e D delta q.1 : ℝ) * coefficientMass e D Z q.1 K) +
        ∑ q ∈ T, weightedNonzeroSix e D delta g l Z q.1 u q.2 K := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro q hq
    dsimp only [W]
    rw [weightedModeMass6_eq_zero_add_nonzero he D delta g l hdelta hl]
    exact add_le_add_right (weightedZeroSix_le_actual_tag he D delta g l
      hD hdelta hdeltaD hg hl Z q.1 u q.2 K) _
  calc
    _ ≤ (∑ q ∈ T, r q)^2 := hsquare
    _ ≤ (∑ q ∈ T, a q) * ∑ q ∈ T, E * W q := hcs
    _ = E * (∑ q ∈ T, a q) * (∑ q ∈ T, W q) := by rw [← mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpaid
      (mul_nonneg hE (sum_nonneg (fun q _ => ha q)))

/-- The coefficient norm in the zero term is the existing original Fourier
coefficient, not a caller-supplied amplitude bound. The uniform constant is
chosen before all atom, physical-feature, tag, root and finite-mode data. -/
theorem actual_weighted_zero_tags_uniform {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
      MediumAdmissible B sigma kappa c0 e → 0 ≤ sigma → 0 ≤ kappa →
      ∀ (Yb Ys : ℝ) (D delta g l : ℕ) [NeZero (g*l)],
      0 < D → 0 < delta → delta ∣ D → 0 < g → 0 < l →
      (fixedSlice e Yb Ys D delta g l).Nonempty →
      ∀ (Z : ℝ), 0 < Z → ∀ (b J : ℕ), eta/6+2 ≤ (b : ℝ) →
      ∀ (sign : Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
        (K : Finset (ℤ × ℤ)),
      (∑ j ∈ range J, weightedZeroSix e D delta g l Z (j,sign) u k K) ≤
        zeroGeometry e D delta g l *
          (C * _root_.P3ActualJointGSourceOnly.fourierCost b *
            e.scale ^ (5*kappa+eta) / physicalT0 e D) := by
  obtain ⟨C, hC, hbound⟩ := actual_coeff_tag_tau_free_epsilon heta
  refine ⟨C, hC, ?_⟩
  intro B sigma kappa c0 e he hsigma hkappa Yb Ys D delta g l inst
    hD hdelta hdeltaD hg hl hfixed Z hZ b J hb sign u k K
  have hgeom : 0 ≤ zeroGeometry e D delta g l := by
    have hU : 0 ≤ e.U := zero_le_one.trans he.1
    have hS : 0 ≤ e.Q2 := zero_le_one.trans he.2.2.2.1
    have hR : 0 ≤ e.Q3 := zero_le_one.trans he.2.2.2.2.1
    have hQ : 0 ≤ e.Q1 := zero_le_one.trans he.2.2.1
    unfold zeroGeometry scaleB scaleC scaleF
    positivity
  have hterm (j : ℕ) :
      weightedZeroSix e D delta g l Z (j,sign) u k K ≤
        zeroGeometry e D delta g l *
          ((∑' m : ℤ × ℤ, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z (j,sign) m‖) *
            (tagFrequencyBound (j,sign) : ℝ) * (actualTagTau e D delta (j,sign) : ℝ)) := by
    have hc := (_root_.P3ActualLogAdapterSourceOnly.coeff_l1_original_five
      he hkappa b D Z hZ (j,sign)).1
    have hfinite : coefficientMass e D Z (j,sign) K ≤
        ∑' m : ℤ × ℤ, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z (j,sign) m‖ :=
      hc.sum_le_tsum K (fun m _ => norm_nonneg _)
    have hz := weightedZeroSix_le_actual_tag he D delta g l hD hdelta hdeltaD hg hl
      Z (j,sign) u k K
    refine hz.trans ?_
    calc
      _ ≤ zeroGeometry e D delta g l * (tagFrequencyBound (j,sign) : ℝ) *
          (actualTagTau e D delta (j,sign) : ℝ) *
            ∑' m : ℤ × ℤ, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z (j,sign) m‖ :=
        mul_le_mul_of_nonneg_left hfinite (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ range J, zeroGeometry e D delta g l *
        ((∑' m : ℤ × ℤ, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z (j,sign) m‖) *
          (tagFrequencyBound (j,sign) : ℝ) * (actualTagTau e D delta (j,sign) : ℝ)) :=
      sum_le_sum (fun j _ => hterm j)
    _ = zeroGeometry e D delta g l *
        ∑ j ∈ range J,
          (∑' m : ℤ × ℤ, ‖_root_.P3ActualLogAdapterSourceOnly.coeff e D Z (j,sign) m‖) *
            (tagFrequencyBound (j,sign) : ℝ) * (actualTagTau e D delta (j,sign) : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hbound B sigma kappa c0 e he hsigma hkappa Yb Ys D delta g l hD hfixed
        Z hZ b J hb sign) hgeom

/-- The physical zero weight remaining after the proved tag-height payment. -/
def zeroPhysicalWeight (D delta g l : ℕ) : ℝ :=
  (D.divisors.card : ℝ) /
    ((g : ℝ)^2 * Real.sqrt ((l : ℝ)*(delta : ℝ)) * (D : ℝ)^2)

/-- Exact squared physical normalization. In particular the D^-4 factor
is present before taking the scalar square root; tau(D)^2 is not discarded. -/
theorem physical_zero_squared_normalization
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    {D delta g l : ℕ} (hD : 0 < D) (hdelta : 0 < delta)
    (hg : 0 < g) (hl : 0 < l) :
    normalizedPacketEnergy324 e D delta g l * zeroGeometry e D delta g l /
        physicalT0 e D =
      (324 * 1512 : ℝ) * (e.U^2 * e.V / e.Q1)^2 *
        (e.U^2 * e.Q3^2 * e.Q2 / e.scale) * zeroPhysicalWeight D delta g l ^ 2 := by
  have hU : 0 < e.U := zero_lt_one.trans_le he.1
  have hV : 0 < e.V := zero_lt_one.trans_le he.2.1
  have hQ : 0 < e.Q1 := zero_lt_one.trans_le he.2.2.1
  have hS : 0 < e.Q2 := zero_lt_one.trans_le he.2.2.2.1
  have hR : 0 < e.Q3 := zero_lt_one.trans_le he.2.2.2.2.1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hδr : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hld : 0 ≤ (l : ℝ)*(delta : ℝ) := by positivity
  unfold normalizedPacketEnergy324 zeroGeometry physicalT0 scaleB scaleC scaleF
    zeroPhysicalWeight MediumAtom.scale
  simp only [div_pow, mul_pow, Real.sq_sqrt hld]
  field_simp [hU.ne', hV.ne', hQ.ne', hS.ne', hR.ne',
    hDr.ne', hδr.ne', hgr.ne', hlr.ne']
  <;> ring

/-- The scalar square root has the original U^2*V/Q1 scale and the
manuscript's ordinary gap U^2*Q3^2*Q2/x. No fourth root is substituted. -/
theorem physical_zero_normalization
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    {D delta g l : ℕ} (hD : 0 < D) (hdelta : 0 < delta)
    (hg : 0 < g) (hl : 0 < l) :
    packetPrefactor e D delta g l *
        Real.sqrt (zeroGeometry e D delta g l / physicalT0 e D) =
      (18 * Real.sqrt 1512) * (e.U^2 * e.V / e.Q1) *
        Real.sqrt (e.U^2 * e.Q3^2 * e.Q2 / e.scale) *
          zeroPhysicalWeight D delta g l := by
  have hU : 0 ≤ e.U := zero_le_one.trans he.1
  have hV : 0 ≤ e.V := zero_le_one.trans he.2.1
  have hQ : 0 ≤ e.Q1 := zero_le_one.trans he.2.2.1
  have hS : 0 ≤ e.Q2 := zero_le_one.trans he.2.2.2.1
  have hR : 0 ≤ e.Q3 := zero_le_one.trans he.2.2.2.2.1
  have hz : 0 ≤ zeroGeometry e D delta g l / physicalT0 e D := by
    unfold zeroGeometry physicalT0 scaleB scaleC scaleF
    positivity
  have hgap : 0 ≤ e.U^2 * e.Q3^2 * e.Q2 / e.scale := by
    unfold MediumAtom.scale
    positivity
  have hw : 0 ≤ zeroPhysicalWeight D delta g l := by
    unfold zeroPhysicalWeight
    positivity
  apply (sq_eq_sq₀
    (mul_nonneg (actual_packetPrefactor_nonneg he D delta g l) (Real.sqrt_nonneg _))
    (by positivity)).mp
  calc
    _ = normalizedPacketEnergy324 e D delta g l * zeroGeometry e D delta g l /
        physicalT0 e D := by
      rw [mul_pow, packetPrefactor_sq e D delta g l hS, Real.sq_sqrt hz]
      ring
    _ = (324 * 1512 : ℝ) * (e.U^2 * e.V / e.Q1)^2 *
        (e.U^2 * e.Q3^2 * e.Q2 / e.scale) * zeroPhysicalWeight D delta g l ^ 2 :=
      physical_zero_squared_normalization he hD hdelta hg hl
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt hgap, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1512)]
      ring

/-- The root/residue multiplicity is an ordinary triangle cost, outside
the analytic square root. -/
theorem root_residue_count_le_square (A : ℕ) [NeZero A] :
    (Fintype.card (ZMod A)ˣ : ℝ) * (Fintype.card (ZMod A) : ℝ) ≤ (A : ℝ)^2 := by
  rw [ZMod.card_units_eq_totient, ZMod.card]
  have hphi : (Nat.totient A : ℝ) ≤ (A : ℝ) := by exact_mod_cast Nat.totient_le A
  simpa only [pow_two] using mul_le_mul_of_nonneg_right hphi (Nat.cast_nonneg A)

/-- The remaining D/delta factor after the full root/residue charge. -/
def physicalDivisorWeight (D delta : ℕ) : ℝ :=
  (D.divisors.card : ℝ) / ((D : ℝ)^2 * Real.sqrt (delta : ℝ))

theorem root_square_zeroPhysicalWeight_le
    {D delta g l : ℕ} (hD : 0 < D) (hdelta : 0 < delta)
    (hg : 0 < g) (hl : 0 < l) :
    ((g*l : ℕ) : ℝ)^2 * zeroPhysicalWeight D delta g l ≤
      (l : ℝ)^2 * physicalDivisorWeight D delta := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hδr : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast (Nat.succ_le_iff.mpr hl)
  have hsqrtl : 1 ≤ Real.sqrt (l : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlr
  have hsqrtδ : 0 < Real.sqrt (delta : ℝ) := Real.sqrt_pos.2 hδr
  have heq : ((g*l : ℕ) : ℝ)^2 * zeroPhysicalWeight D delta g l =
      ((l : ℝ)^2 * physicalDivisorWeight D delta) / Real.sqrt (l : ℝ) := by
    unfold zeroPhysicalWeight physicalDivisorWeight
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg l)]
    field_simp [hDr.ne', hgr.ne', hsqrtδ.ne',
      (zero_lt_one.trans_le hsqrtl).ne']
    <;> ring
  rw [heq]
  apply div_le_self
  · unfold physicalDivisorWeight
    positivity
  · exact hsqrtl

theorem sum_physicalDivisorWeight_le_tau_square (D : ℕ) :
    (∑ delta ∈ D.divisors, physicalDivisorWeight D delta) ≤
      (D.divisors.card : ℝ)^2 / (D : ℝ)^2 := by
  calc
    _ ≤ ∑ _delta ∈ D.divisors, (D.divisors.card : ℝ) / (D : ℝ)^2 := by
      apply sum_le_sum
      intro delta hdelta
      have hδr : (1 : ℝ) ≤ delta := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.pos_of_mem_divisors hdelta))
      have hroot : 1 ≤ Real.sqrt (delta : ℝ) := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hδr
      unfold physicalDivisorWeight
      rw [← div_div]
      exact div_le_self (by positivity) hroot
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul]
      ring

/-- All finite physical D ranges have one absolute divisor budget. The
proof uses the already proved tau subpower and a convergent 3/2 series.
There is no hypothesis restricting D to a small range. -/
theorem finite_physical_divisor_sum_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset ℕ,
      (∑ D ∈ S, ∑ delta ∈ D.divisors, physicalDivisorWeight D delta) ≤ C := by
  obtain ⟨K, hK, hTau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (ε := (1/4 : ℝ)) (by norm_num)
  have hs : Summable (fun D : ℕ => (D : ℝ)^(-3/2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  let P : ℝ := ∑' D : ℕ, (D : ℝ)^(-3/2 : ℝ)
  have hP : 0 ≤ P := tsum_nonneg (fun D => Real.rpow_nonneg (Nat.cast_nonneg D) _)
  refine ⟨1 + K^2*P, by positivity, fun S => ?_⟩
  have hpoint (D : ℕ) : (D.divisors.card : ℝ)^2 / (D : ℝ)^2 ≤
      K^2 * (D : ℝ)^(-3/2 : ℝ) := by
    by_cases hD : D = 0
    · subst D
      simp only [Nat.divisors_zero, card_empty, Nat.cast_zero, zero_pow,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div]
      positivity
    · have hDr : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
      have ht : (D.divisors.card : ℝ) ≤ K * (D : ℝ)^(1/4 : ℝ) := by
        simpa only [fouvryTau_two] using hTau D (Nat.pos_of_ne_zero hD)
      have hpow : ((D : ℝ)^(1/4 : ℝ))^2 / (D : ℝ)^2 =
          (D : ℝ)^(-3/2 : ℝ) := by
        calc
          _ = (D : ℝ)^((1/4 : ℝ)*2) / (D : ℝ)^(2 : ℝ) := by
            rw [Real.rpow_mul_natCast hDr.le, Real.rpow_natCast]
          _ = (D : ℝ)^((1/4 : ℝ)*2-2) := (Real.rpow_sub hDr _ _).symm
          _ = _ := by norm_num
      calc
        _ ≤ (K * (D : ℝ)^(1/4 : ℝ))^2 / (D : ℝ)^2 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) ht 2)
            (sq_nonneg _)
        _ = K^2 * (((D : ℝ)^(1/4 : ℝ))^2 / (D : ℝ)^2) := by ring
        _ = _ := by rw [hpow]
  calc
    _ ≤ ∑ D ∈ S, (D.divisors.card : ℝ)^2 / (D : ℝ)^2 :=
      sum_le_sum (fun D _ => sum_physicalDivisorWeight_le_tau_square D)
    _ ≤ ∑ D ∈ S, K^2 * (D : ℝ)^(-3/2 : ℝ) := sum_le_sum (fun D _ => hpoint D)
    _ = K^2 * ∑ D ∈ S, (D : ℝ)^(-3/2 : ℝ) := (mul_sum _ _ _).symm
    _ ≤ K^2 * P := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum S (fun D _ => Real.rpow_nonneg (Nat.cast_nonneg D) _)) (sq_nonneg K)
    _ ≤ 1 + K^2 * P := by linarith

/-- Exact full root-square cost, with conservative finite g/l enumeration.
For the actual cutoffs G,L <= x^(sigma/4), the arithmetic factor G*L^3
costs at most x^sigma. No uncharged root or residue Cauchy is involved. -/
theorem finite_root_feature_divisor_sum_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (G L : ℕ),
      (∑ D ∈ S, ∑ delta ∈ D.divisors,
        ∑ g ∈ Icc 1 G, ∑ l ∈ Icc 1 L,
          ((g*l : ℕ) : ℝ)^2 * zeroPhysicalWeight D delta g l) ≤
        C * (G : ℝ) * (L : ℝ)^3 := by
  obtain ⟨C, hC, hbound⟩ := finite_physical_divisor_sum_uniform
  refine ⟨C, hC, fun S G L => ?_⟩
  have hpoint (D delta : ℕ) (hdelta : delta ∈ D.divisors) :
      (∑ g ∈ Icc 1 G, ∑ l ∈ Icc 1 L,
        ((g*l : ℕ) : ℝ)^2 * zeroPhysicalWeight D delta g l) ≤
      ((G : ℝ)*(L : ℝ)^3) * physicalDivisorWeight D delta := by
    have hD : 0 < D := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hdelta).2
    have hδ : 0 < delta := Nat.pos_of_mem_divisors hdelta
    calc
      _ ≤ ∑ _g ∈ Icc 1 G, ∑ _l ∈ Icc 1 L,
          (L : ℝ)^2 * physicalDivisorWeight D delta := by
        apply sum_le_sum
        intro g hg
        apply sum_le_sum
        intro l hl
        have hgl := root_square_zeroPhysicalWeight_le hD hδ
          (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hg).1)
          (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hl).1)
        have hlL : (l : ℝ) ≤ L := by exact_mod_cast (mem_Icc.mp hl).2
        exact hgl.trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hlL 2) (by unfold physicalDivisorWeight; positivity))
      _ = _ := by
        simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
        ring
  calc
    _ ≤ ∑ D ∈ S, ∑ delta ∈ D.divisors,
        ((G : ℝ)*(L : ℝ)^3) * physicalDivisorWeight D delta :=
      sum_le_sum (fun D _ => sum_le_sum (fun delta hdelta => hpoint D delta hdelta))
    _ = ((G : ℝ)*(L : ℝ)^3) *
        (∑ D ∈ S, ∑ delta ∈ D.divisors, physicalDivisorWeight D delta) := by
      simp only [mul_sum]
    _ ≤ ((G : ℝ)*(L : ℝ)^3) * C :=
      mul_le_mul_of_nonneg_left (hbound S) (by positivity)
    _ = _ := by ring

/-- The same constant works for the actual x^(sigma/4) integer cutoffs,
with the complete root-square charge paid by x^sigma. -/
theorem finite_root_feature_divisor_sum_scale :
    ∃ C : ℝ, 0 < C ∧ ∀ (x sigma : ℝ), 0 < x → ∀ S : Finset ℕ,
      (∑ D ∈ S, ∑ delta ∈ D.divisors,
        ∑ g ∈ Icc 1 (Nat.floor (x^(sigma/4))),
          ∑ l ∈ Icc 1 (Nat.floor (x^(sigma/4))),
          ((g*l : ℕ) : ℝ)^2 * zeroPhysicalWeight D delta g l) ≤ C * x^sigma := by
  obtain ⟨C, hC, hbound⟩ := finite_root_feature_divisor_sum_uniform
  refine ⟨C, hC, fun x sigma hx S => ?_⟩
  let Y := x^(sigma/4)
  have hY : 0 ≤ Y := Real.rpow_nonneg hx.le _
  have hfloor : (Nat.floor Y : ℝ) ≤ Y := Nat.floor_le hY
  have hpow : Y^4 = x^sigma := by
    dsimp only [Y]
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    norm_num
  calc
    _ ≤ C * (Nat.floor Y : ℝ) * (Nat.floor Y : ℝ)^3 :=
      hbound S (Nat.floor Y) (Nat.floor Y)
    _ = C * (Nat.floor Y : ℝ)^4 := by ring
    _ ≤ C * Y^4 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 4) hC.le
    _ = _ := by rw [hpow]

end

end ImbalancedChen.Part3.ActualZeroOuterPayment
