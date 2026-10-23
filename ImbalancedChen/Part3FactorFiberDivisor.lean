import ImbalancedChen.Part3ComplexDispersion
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean

/-!
# Original factor fibers and the actual third-divisor moment payment

Different ordered triples can give the same complete physical modulus.
Their coefficients are summed, with all complex signs intact. The grouped
coefficient is not asserted to be one-bounded: its proved majorant is tau_3.

The full ordered-factor convolution is realized by two nested divisor
antidiagonals. An explicit injection retains every original three-factor
label, including repeated factors. Its exact cardinal is the pinned
fouvryTau 3, not an assumed multiplicity bound. The existing fixed-order
second moments then pay log exponents 8, 9 and 18 on the actual support.

The only external supplier is fixed goldbach commit
09b97db5764ade1246bfb77206baa1b124760958, DivisorMean.lean,
SHA256 4e119e53ec5df626bb7e02aa44bf950dbe721bd1f2767fba5fbf90c30784ff59.
It already belongs to the baseline source DAG; no new external bootstrap
is needed. The V/U primitive centers are not replaced or cancelled here.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace FactorFiber

/-- The full ordered three-factor convolution carrier for one modulus. -/
def orderedThreeFactors (q : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
  q.divisorsAntidiagonal.sigma (fun p ↦ p.2.divisorsAntidiagonal)

theorem card_orderedThreeFactors (q : ℕ) :
    (orderedThreeFactors q).card = fouvryTau 3 q := by
  have hcard (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors]
    exact Finset.card_map _
  calc
    _ = ∑ p ∈ q.divisorsAntidiagonal, p.2.divisors.card := by
      simp only [orderedThreeFactors, Finset.card_sigma, hcard]
    _ = ∑ n ∈ q.divisors, n.divisors.card :=
      Nat.sum_divisorsAntidiagonal' (fun _ n ↦ n.divisors.card)
    _ = _ := by rw [show 3 = 2 + 1 from rfl, fouvryTau_succ]; simp only [fouvryTau_two]

def tripleToConvolution (r : ℕ × ℕ × ℕ) : Σ _ : ℕ × ℕ, ℕ × ℕ :=
  ⟨(r.1, r.2.1 * r.2.2), (r.2.1, r.2.2)⟩

theorem tripleToConvolution_injective : Function.Injective tripleToConvolution := by
  intro r s h
  exact Prod.ext (congrArg (fun p ↦ p.1.1) h) (congrArg (fun p ↦ p.2) h)

end FactorFiber

def MediumAtom.physicalFactorModuli (d : MediumAtom) : Finset ℕ :=
  d.complexFactorLabels.image complexFactorModulus

def MediumAtom.physicalFactorFiber (d : MediumAtom) (q : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  d.complexFactorLabels.filter (fun r ↦ complexFactorModulus r = q)

def MediumAtom.groupedFactorGamma (d : MediumAtom) (q : ℕ) : ℂ :=
  ∑ r ∈ d.physicalFactorFiber q, d.complexFactorGamma r

/-- The exact complex grouping is performed before any norm is taken. -/
theorem MediumAtom.sum_factorLabels_eq_grouped (d : MediumAtom) (F : ℕ → ℂ) :
    (∑ r ∈ d.complexFactorLabels, d.complexFactorGamma r * F (complexFactorModulus r)) =
      ∑ q ∈ d.physicalFactorModuli, d.groupedFactorGamma q * F q := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := d.complexFactorLabels) (t := d.physicalFactorModuli)
    (g := complexFactorModulus) (fun r hr ↦ Finset.mem_image_of_mem _ hr)
    (fun r ↦ d.complexFactorGamma r * F (complexFactorModulus r))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro q _
  rw [MediumAtom.groupedFactorGamma, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [(Finset.mem_filter.mp hr).2]

theorem MediumAtom.signedError_eq_groupedFactorGamma (d : MediumAtom) :
    d.signedError =
      ∑ q ∈ d.physicalFactorModuli, d.groupedFactorGamma q * d.discrepancy q := by
  rw [← d.sum_factorLabels_eq_grouped d.discrepancy]
  simp only [MediumAtom.signedError, MediumAtom.complexFactorLabels,
    MediumAtom.complexFactorGamma, complexFactorModulus, Finset.sum_product]

/-- The same literal primitive kernel remains in the actual centered row. -/
theorem MediumAtom.complexCenteredRow_eq_groupedFactorGamma (d : MediumAtom) (n : ℕ) :
    d.complexCenteredRow n =
      ∑ q ∈ d.physicalFactorModuli, d.groupedFactorGamma q *
        ∑ m ∈ d.betaCarrier, d.beta m * complexPrimitiveKernel d.residue q n m := by
  calc
    _ = ∑ r ∈ d.complexFactorLabels, d.complexFactorGamma r *
        ∑ m ∈ d.betaCarrier, d.beta m *
          complexPrimitiveKernel d.residue (complexFactorModulus r) n m := by
      rw [MediumAtom.complexCenteredRow_eq_sum]
      simp only [MediumAtom.complexRowLabels, Finset.sum_product,
        MediumAtom.complexRowContribution, Finset.mul_sum, mul_assoc]
    _ = _ := d.sum_factorLabels_eq_grouped
      (fun q : ℕ ↦ ∑ m ∈ d.betaCarrier, d.beta m * complexPrimitiveKernel d.residue q n m)

private theorem factorCarrier_bounds {Q : ℝ} (hQ : 1 ≤ Q) {q : ℕ}
    (hq : q ∈ factorCarrier Q) : 0 < q ∧ (q : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hq
  have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  refine ⟨by omega, ?_⟩
  exact (show (q : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
    (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

private theorem factorLabel_mem {d : MediumAtom} {r : ℕ × ℕ × ℕ}
    (hr : r ∈ d.complexFactorLabels) :
    r.1 ∈ factorCarrier d.Q1 ∧ r.2.1 ∈ factorCarrier d.Q2 ∧
      r.2.2 ∈ factorCarrier d.Q3 := by
  obtain ⟨h1, h23⟩ := Finset.mem_product.mp hr
  exact ⟨h1, (Finset.mem_product.mp h23).1, (Finset.mem_product.mp h23).2⟩

/-- Every original ordered label embeds, without identifying equal factors. -/
theorem MediumAtom.card_physicalFactorFiber_le_tauThree
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (q : ℕ) :
    (d.physicalFactorFiber q).card ≤ fouvryTau 3 q := by
  rw [← FactorFiber.card_orderedThreeFactors]
  apply Finset.card_le_card_of_injOn FactorFiber.tripleToConvolution
  · intro r hr
    obtain ⟨hr, hq⟩ := Finset.mem_filter.mp hr
    obtain ⟨h1, h2, h3⟩ := factorLabel_mem hr
    obtain ⟨_, _, hQ1, hQ2, hQ3, _⟩ := hd
    have hp1 := (factorCarrier_bounds hQ1 h1).1
    have hp2 := (factorCarrier_bounds hQ2 h2).1
    have hp3 := (factorCarrier_bounds hQ3 h3).1
    apply Finset.mem_sigma.mpr
    refine ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨?_, ?_⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (Nat.mul_pos hp2 hp3).ne'⟩⟩
    · simpa only [FactorFiber.tripleToConvolution, complexFactorModulus, mul_assoc] using hq
    · rw [← hq]
      exact (Nat.mul_pos (Nat.mul_pos hp1 hp2) hp3).ne'
  · exact FactorFiber.tripleToConvolution_injective.injOn

private theorem complexFactorGamma_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {r : ℕ × ℕ × ℕ}
    (hr : r ∈ d.complexFactorLabels) : ‖d.complexFactorGamma r‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hd
  obtain ⟨hr1, hr2, hr3⟩ := factorLabel_mem hr
  rw [MediumAtom.complexFactorGamma, norm_mul, norm_mul]
  calc
    ‖d.gamma1 r.1‖ * ‖d.gamma2 r.2.1‖ * ‖d.gamma3 r.2.2‖ ≤ 1 * 1 * 1 :=
      mul_le_mul (mul_le_mul (h1 _ hr1).1 (h2 _ hr2).1 (norm_nonneg _) zero_le_one)
        (h3 _ hr3).1 (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The actual grouped complex coefficient has order three, with no
normalization by its multiplicity and no one-bounded-coefficient premise. -/
theorem MediumAtom.groupedFactorGamma_norm_le_tauThree
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (q : ℕ) :
    ‖d.groupedFactorGamma q‖ ≤ (fouvryTau 3 q : ℝ) := by
  calc
    _ ≤ ∑ r ∈ d.physicalFactorFiber q, ‖d.complexFactorGamma r‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ d.physicalFactorFiber q, (1 : ℝ) :=
      Finset.sum_le_sum (fun r hr ↦
        complexFactorGamma_norm_le_one hd (Finset.mem_filter.mp hr).1)
    _ = ((d.physicalFactorFiber q).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast d.card_physicalFactorFiber_le_tauThree hd q

def MediumAtom.physicalFactorCap (d : MediumAtom) : ℝ := 8 * d.Q1 * d.Q2 * d.Q3

theorem MediumAtom.one_le_physicalFactorCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.physicalFactorCap := by
  obtain ⟨_, _, hQ1, hQ2, hQ3, _⟩ := hd
  unfold MediumAtom.physicalFactorCap
  calc
    1 ≤ 8 * (1 : ℝ) * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr

theorem MediumAtom.physicalFactorModuli_subset_cap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.physicalFactorModuli ⊆ Finset.Ioc 0 (Nat.floor d.physicalFactorCap) := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hr1, hr2, hr3⟩ := factorLabel_mem hr
  obtain ⟨_, _, hQ1, hQ2, hQ3, _⟩ := hd
  obtain ⟨hp1, hb1⟩ := factorCarrier_bounds hQ1 hr1
  obtain ⟨hp2, hb2⟩ := factorCarrier_bounds hQ2 hr2
  obtain ⟨hp3, hb3⟩ := factorCarrier_bounds hQ3 hr3
  apply Finset.mem_Ioc.mpr
  refine ⟨Nat.mul_pos (Nat.mul_pos hp1 hp2) hp3, Nat.le_floor ?_⟩
  calc
    ((complexFactorModulus r : ℕ) : ℝ) = (r.1 : ℝ) * r.2.1 * r.2.2 := by simp [complexFactorModulus]
    _ ≤ (2 * d.Q1) * (2 * d.Q2) * (2 * d.Q3) := by gcongr
    _ = d.physicalFactorCap := by unfold MediumAtom.physicalFactorCap; ring

/-- Ordinary second moment, with the full explicit logarithm exponent eight. -/
theorem MediumAtom.sum_groupedFactorGamma_norm_sq_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ ^ 2) ≤
      d.physicalFactorCap * (1 + Real.log d.physicalFactorCap) ^ 8 := by
  exact sum_alpha_sq_le_fouvryTau (k := 3) (by norm_num)
    (d.one_le_physicalFactorCap hd) d.physicalFactorModuli
    (d.physicalFactorModuli_subset_cap hd) (fun q ↦ ‖d.groupedFactorGamma q‖)
    (fun q _ ↦ by simpa only [abs_norm] using d.groupedFactorGamma_norm_le_tauThree hd q)

/-- The reciprocal moment costs the explicit fixed logarithm exponent nine. -/
theorem MediumAtom.sum_groupedFactorGamma_norm_sq_div_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ ^ 2 / q) ≤
      (1 + Real.log d.physicalFactorCap) ^ 9 := by
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, (fouvryTau 3 q : ℝ) ^ 2 / q := by
      apply Finset.sum_le_sum
      intro q _
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (d.groupedFactorGamma_norm_le_tauThree hd q) 2)
        (Nat.cast_nonneg _)
    _ ≤ ∑ q ∈ Finset.Ioc 0 (Nat.floor d.physicalFactorCap),
        (fouvryTau 3 q : ℝ) ^ 2 / q :=
      Finset.sum_le_sum_of_subset_of_nonneg (d.physicalFactorModuli_subset_cap hd)
        (fun _ _ _ ↦ by positivity)
    _ ≤ _ := sum_fouvryTau_sq_div_le_real 3 (d.one_le_physicalFactorCap hd)

/-- Totient division is paid without a squarefree restriction or lost labels. -/
theorem MediumAtom.sum_groupedFactorGamma_norm_sq_div_totient_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖ ^ 2 / q.totient) ≤
      (1 + Real.log d.physicalFactorCap) ^ 18 := by
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, (fouvryTau 3 q : ℝ) ^ 2 / q.totient := by
      apply Finset.sum_le_sum
      intro q _
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (d.groupedFactorGamma_norm_le_tauThree hd q) 2)
        (Nat.cast_nonneg _)
    _ ≤ ∑ q ∈ Finset.Ioc 0 (Nat.floor d.physicalFactorCap),
        (fouvryTau 3 q : ℝ) ^ 2 / q.totient :=
      Finset.sum_le_sum_of_subset_of_nonneg (d.physicalFactorModuli_subset_cap hd)
        (fun _ _ _ ↦ by positivity)
    _ ≤ _ := sum_fouvryTau_sq_div_totient_le_real 3 (d.one_le_physicalFactorCap hd)

end

end ImbalancedChen.Part3
