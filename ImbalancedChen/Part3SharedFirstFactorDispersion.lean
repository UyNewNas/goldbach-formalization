import ImbalancedChen.Part3TransposedDispersion

/-!
# Actual Cauchy in original beta and the first physical factor

The first factor remains outside the squared row. Its full primitive
dyadic carrier is used, so no coefficient-dependent subset becomes an
arbitrary weight in the later first-factor sum. The original gamma1 is
retained at the signed entrance and in its actual outside L2 factor.

Each point-mass slice is a genuine atom with the original U,V,Q1,Q2,Q3,
signed residue, alpha, beta and alpha interval. Only gamma1 is replaced
by the indicator of the first factor. Original admissibility supplies
its primitive gate. No admissibility is asserted for a transposed atom.

The new outside factor is betaL2 times gamma1L2, bounded by 4VQ1 times
the actual beta divisor-moment logarithm. The literal slice W-2V+U and
complete Poisson series are retained. This leaf supplies no energy,
zero-mode payment, or migration of the old independent-first-factor W.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter
open scoped BigOperators Topology

def MediumAtom.q1SliceAtom (d : MediumAtom) (p : ℕ) : MediumAtom :=
  { d with gamma1 := fun q ↦ if q = p then 1 else 0 }

def MediumAtom.primitiveFirstFactorCarrier (d : MediumAtom) : Finset ℕ :=
  (factorCarrier d.Q1).filter (fun p ↦ p.Coprime d.residue.natAbs)

def MediumAtom.sharedFirstFactorRows (d : MediumAtom) : Finset ((ℕ × ℕ) × ℕ) :=
  (factorCarrier d.Q2 ×ˢ factorCarrier d.Q3) ×ˢ d.transposedAtom.betaCarrier

def MediumAtom.sharedFirstFactorCoefficient (d : MediumAtom)
    (l : (ℕ × ℕ) × ℕ) : ℂ :=
  d.gamma2 l.1.1 * d.gamma3 l.1.2 * d.transposedAtom.beta l.2

namespace SharedFirstFactorDispersion

private theorem gamma1_gate
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) :
    ‖d.gamma1 p‖ ≤ 1 ∧ (d.gamma1 p ≠ 0 → p.Coprime d.residue.natAbs) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hg, _, _⟩ := hd
  exact hg p hp

private theorem factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {p : ℕ}
    (hp : p ∈ factorCarrier Q) : 0 < p := by
  have hlo := (Finset.mem_Icc.mp hp).1
  have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  omega

private theorem card_factorCarrier_le {Q : ℝ} (hQ : 1 ≤ Q) :
    ((factorCarrier Q).card : ℝ) ≤ 2 * Q := by
  have hsub : factorCarrier Q ⊆ Ioc 0 (Nat.floor (2 * Q)) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
    exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hcard
  exact (show ((factorCarrier Q).card : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by
    exact_mod_cast hcard).trans (Nat.floor_le (by linarith))

end SharedFirstFactorDispersion

@[simp] theorem MediumAtom.q1SliceAtom_scale (d : MediumAtom) (p : ℕ) :
    (d.q1SliceAtom p).scale = d.scale := rfl

@[simp] theorem MediumAtom.q1SliceAtom_auxSWError (d : MediumAtom)
    (p k q b : ℕ) : (d.q1SliceAtom p).auxSWError k q b = d.auxSWError k q b := rfl

/-- The same C0 and the same uniform family constants work for every slice. -/
theorem uniformAuxiliarySW_q1SliceFamily {ι : Type*} (F : ι → MediumAtom)
    {C0 : ℕ} (hSW : UniformAuxiliarySW F C0) :
    UniformAuxiliarySW (fun ip : ι × ℕ ↦ (F ip.1).q1SliceAtom ip.2) C0 := by
  intro A hA
  obtain ⟨C, hC, x0, hx0, hbound⟩ := hSW A hA
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro ip hx k q b hk hq hb
  exact hbound ip.1 hx k q b hk hq hb

/-- A slice has original geometry; its new point mass is primitive. -/
theorem mediumAdmissible_q1SliceAtom
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) :
    MediumAdmissible B sigma kappa c0 (d.q1SliceAtom p) := by
  obtain ⟨_hp, hpa⟩ := Finset.mem_filter.mp hp
  obtain ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, hBeta, _hGamma1, hGamma2, hGamma3⟩ := hd
  refine ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, hBeta, ?_, hGamma2, hGamma3⟩
  intro q _
  change ‖(if q = p then (1 : ℂ) else 0)‖ ≤ 1 ∧
    ((if q = p then (1 : ℂ) else 0) ≠ 0 → q.Coprime d.residue.natAbs)
  by_cases hqp : q = p
  · subst q
    constructor
    · simpa only [ite_true, norm_one] using (le_refl (1 : ℝ))
    · exact fun _ ↦ hpa
  · constructor
    · simpa only [if_neg hqp, norm_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
    · intro hn
      exact (hn (if_neg hqp)).elim

theorem MediumAtom.q1SliceAtom_signedError (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) :
    (d.q1SliceAtom p).signedError =
      ∑ q2 ∈ factorCarrier d.Q2, ∑ q3 ∈ factorCarrier d.Q3,
        d.gamma2 q2 * d.gamma3 q3 * d.discrepancy (p * q2 * q3) := by
  change (∑ q ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
    ∑ q3 ∈ factorCarrier d.Q3,
      (if q = p then (1 : ℂ) else 0) * d.gamma2 q2 * d.gamma3 q3 *
        d.discrepancy (q * q2 * q3)) = _
  rw [Finset.sum_eq_single p]
  · simp only [ite_true, one_mul]
  · intro q _ hqp
    simp only [if_neg hqp, zero_mul, Finset.sum_const_zero]
  · intro hnot
    exact (hnot hp).elim

/-- Exact signed deletion of the nonprimitive first-factor labels only. -/
theorem MediumAtom.signedError_eq_q1Slice_sum
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.signedError = ∑ p ∈ d.primitiveFirstFactorCarrier,
      d.gamma1 p * (d.q1SliceAtom p).signedError := by
  have hfull : d.signedError = ∑ p ∈ factorCarrier d.Q1,
      d.gamma1 p * (d.q1SliceAtom p).signedError := by
    change (∑ p ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
      ∑ q3 ∈ factorCarrier d.Q3,
        d.gamma1 p * d.gamma2 q2 * d.gamma3 q3 * d.discrepancy (p * q2 * q3)) = _
    apply Finset.sum_congr rfl
    intro p hp
    rw [MediumAtom.q1SliceAtom_signedError d hp]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q2 _
    apply Finset.sum_congr rfl
    intro q3 _
    ring
  rw [hfull]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hgamma : d.gamma1 p = 0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr
      ⟨hp, (SharedFirstFactorDispersion.gamma1_gate hd hp).2 hn⟩)
  simp only [hgamma, zero_mul]

private theorem q1Slice_signedError_eq_rows (d : MediumAtom) (p : ℕ) :
    (d.q1SliceAtom p).signedError = ∑ m ∈ d.betaCarrier,
      d.beta m * (d.q1SliceAtom p).transposedAtom.complexCenteredRow m := by
  have h := (d.q1SliceAtom p).transposedAtom.signedError_eq_complexCenteredRows
  rw [MediumAtom.transposedAtom_signedError, MediumAtom.transposedAtom_alphaCarrier] at h
  exact h

/-- The original beta and gamma1 are jointly outside the same squared row. -/
theorem MediumAtom.signedError_eq_sharedFirstFactorRows
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.signedError = ∑ p ∈ d.primitiveFirstFactorCarrier, ∑ m ∈ d.betaCarrier,
      (d.gamma1 p * d.beta m) *
        (d.q1SliceAtom p).transposedAtom.complexCenteredRow m := by
  rw [d.signedError_eq_q1Slice_sum hd]
  apply Finset.sum_congr rfl
  intro p _
  rw [q1Slice_signedError_eq_rows, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem MediumAtom.signedError_norm_sq_le_sharedFirstFactorRows
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ‖d.signedError‖ ^ 2 ≤
      (∑ m ∈ d.betaCarrier, ‖d.beta m‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          ∑ p ∈ d.primitiveFirstFactorCarrier, ∑ m ∈ d.betaCarrier,
            ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2 := by
  rw [d.signedError_eq_sharedFirstFactorRows hd]
  calc
    _ ≤ (∑ z ∈ d.primitiveFirstFactorCarrier ×ˢ d.betaCarrier,
          ‖d.gamma1 z.1 * d.beta z.2‖ ^ 2) *
        ∑ z ∈ d.primitiveFirstFactorCarrier ×ˢ d.betaCarrier,
          ‖(d.q1SliceAtom z.1).transposedAtom.complexCenteredRow z.2‖ ^ 2 := by
      simpa only [Finset.sum_product] using
        complex_finset_cauchy_norm_sq (d.primitiveFirstFactorCarrier ×ˢ d.betaCarrier)
          (fun z ↦ d.gamma1 z.1 * d.beta z.2)
          (fun z ↦ (d.q1SliceAtom z.1).transposedAtom.complexCenteredRow z.2)
    _ = _ := by
      simp only [Finset.sum_product, norm_mul, mul_pow,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

private theorem q1Slice_rows_le_commonSmooth (d : MediumAtom) (hV : 1 ≤ d.V) (p : ℕ) :
    (∑ m ∈ d.betaCarrier,
      ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2) ≤
        ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
          d.transposedAtom.commonSmoothWeight m *
            ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2 := by
  have hsub : d.betaCarrier ⊆ d.transposedAtom.commonSmoothCarrier := by
    intro m hm
    apply d.transposedSmoothWeight_support_subset hV
    rw [d.transposedSmoothWeight_eq_one_on_beta hV hm]
    norm_num
  calc
    _ = ∑ m ∈ d.betaCarrier, d.transposedAtom.commonSmoothWeight m *
        ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [d.transposedSmoothWeight_eq_one_on_beta hV hm, one_mul]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ ↦ mul_nonneg (d.transposedAtom.commonSmoothWeight_nonneg m) (sq_nonneg _))

/-- One original-V cutoff, chosen before the first factor and every row. -/
theorem MediumAtom.signedError_norm_sq_le_sharedFirstFactorSmoothRows
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ‖d.signedError‖ ^ 2 ≤
      (∑ m ∈ d.betaCarrier, ‖d.beta m‖ ^ 2) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) *
          ∑ p ∈ d.primitiveFirstFactorCarrier,
            ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
              d.transposedAtom.commonSmoothWeight m *
                ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2 := by
  apply (d.signedError_norm_sq_le_sharedFirstFactorRows hd).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun p _ ↦ q1Slice_rows_le_commonSmooth d hd.2.1 p)

theorem MediumAtom.sharedFirstFactorSmoothRows_eq_dispersion (d : MediumAtom) :
    (∑ p ∈ d.primitiveFirstFactorCarrier,
      ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        d.transposedAtom.commonSmoothWeight m *
          ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2) =
      ∑ p ∈ d.primitiveFirstFactorCarrier,
        ((d.q1SliceAtom p).transposedAtom.complexDispersionW
            d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight -
          2 * (d.q1SliceAtom p).transposedAtom.complexDispersionV
            d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight +
          (d.q1SliceAtom p).transposedAtom.complexDispersionU
            d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight) := by
  apply Finset.sum_congr rfl
  intro p _
  exact MediumAtom.complex_dispersion_identity _ _ _

/-- The honest additional Q1 outside cost is explicit. -/
theorem MediumAtom.sharedFirstFactor_outside_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ m ∈ d.betaCarrier, ‖d.beta m‖ ^ 2) *
      (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) ≤
        4 * d.V * d.Q1 * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) := by
  have hgamma : (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) ≤ 2 * d.Q1 := by
    calc
      _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hh := (SharedFirstFactorDispersion.gamma1_gate hd (Finset.mem_filter.mp hp).1).1
        simpa only [one_pow] using
          (sq_le_sq₀ (norm_nonneg (d.gamma1 p)) (by norm_num : (0 : ℝ) ≤ 1)).2 hh
      _ = (d.primitiveFirstFactorCarrier.card : ℝ) := by simp
      _ ≤ ((factorCarrier d.Q1).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ _ := SharedFirstFactorDispersion.card_factorCarrier_le hd.2.2.1
  have hbeta := mediumAdmissible_beta_norm_sq_sum_le hd
  have hbetaNonneg : 0 ≤ 2 * d.V *
      (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) :=
    (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)).trans hbeta
  calc
    _ ≤ (2 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) * (2 * d.Q1) :=
      mul_le_mul hbeta hgamma (by positivity) hbetaNonneg
    _ = _ := by ring

theorem MediumAtom.gamma1L2_primitive_eq
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2) =
      ∑ p ∈ factorCarrier d.Q1, ‖d.gamma1 p‖ ^ 2 := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hgamma : d.gamma1 p = 0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr
      ⟨hp, (SharedFirstFactorDispersion.gamma1_gate hd hp).2 hn⟩)
  simp only [hgamma, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- This is a reduction to a new energy; it does not supply that energy. -/
theorem MediumAtom.signedError_norm_sq_le_sharedFirstFactorMomentDispersion
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ‖d.signedError‖ ^ 2 ≤
      (4 * d.V * d.Q1 * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        ∑ p ∈ d.primitiveFirstFactorCarrier,
          ((d.q1SliceAtom p).transposedAtom.complexDispersionW
              d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight -
            2 * (d.q1SliceAtom p).transposedAtom.complexDispersionV
              d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight +
            (d.q1SliceAtom p).transposedAtom.complexDispersionU
              d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight) := by
  have h := d.signedError_norm_sq_le_sharedFirstFactorSmoothRows hd
  rw [d.sharedFirstFactorSmoothRows_eq_dispersion] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right (d.sharedFirstFactor_outside_le hd)
  rw [← d.sharedFirstFactorSmoothRows_eq_dispersion]
  exact Finset.sum_nonneg (fun p _ ↦ Finset.sum_nonneg (fun m _ ↦
    mul_nonneg (d.transposedAtom.commonSmoothWeight_nonneg m) (sq_nonneg _)))

namespace SharedFirstFactorDispersion

private theorem slice_rows (d : MediumAtom) (p : ℕ) :
    (d.q1SliceAtom p).transposedAtom.complexRowLabels =
      d.transposedAtom.complexRowLabels := rfl

private theorem slice_coefficient (d : MediumAtom) (p : ℕ)
    (l : (ℕ × ℕ × ℕ) × ℕ) :
    (d.q1SliceAtom p).transposedAtom.complexBetaCoefficient l =
      (if l.1.1 = p then (1 : ℂ) else 0) *
        d.gamma2 l.1.2.1 * d.gamma3 l.1.2.2 * d.transposedAtom.beta l.2 := rfl

/-- The private reindexer is applied below to the literal constructed CRT kernel. -/
private theorem sum_slice_coefficient (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1)
    (f : ((ℕ × ℕ × ℕ) × ℕ) → ℂ) :
    (∑ l ∈ (d.q1SliceAtom p).transposedAtom.complexRowLabels,
      (d.q1SliceAtom p).transposedAtom.complexBetaCoefficient l * f l) =
      ∑ l ∈ d.sharedFirstFactorRows,
        d.sharedFirstFactorCoefficient l * f ((p, l.1.1, l.1.2), l.2) := by
  rw [slice_rows]
  simp only [MediumAtom.complexRowLabels, MediumAtom.complexFactorLabels,
    MediumAtom.sharedFirstFactorRows, Finset.sum_product]
  change (∑ q ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
    ∑ q3 ∈ factorCarrier d.Q3, ∑ n ∈ d.transposedAtom.betaCarrier,
      (d.q1SliceAtom p).transposedAtom.complexBetaCoefficient ((q, q2, q3), n) *
        f ((q, q2, q3), n)) = _
  rw [Finset.sum_eq_single p]
  · simp only [slice_coefficient, ite_true, one_mul,
      MediumAtom.sharedFirstFactorCoefficient]
  · intro q _ hqp
    simp only [slice_coefficient, if_neg hqp, zero_mul, Finset.sum_const_zero]
  · intro hnot
    exact (hnot hp).elim

private theorem sum_star_slice_coefficient (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1)
    (f : ((ℕ × ℕ × ℕ) × ℕ) → ℂ) :
    (∑ l ∈ (d.q1SliceAtom p).transposedAtom.complexRowLabels,
      star ((d.q1SliceAtom p).transposedAtom.complexBetaCoefficient l) * f l) =
      ∑ l ∈ d.sharedFirstFactorRows,
        star (d.sharedFirstFactorCoefficient l) * f ((p, l.1.1, l.1.2), l.2) := by
  calc
    _ = star (∑ l ∈ (d.q1SliceAtom p).transposedAtom.complexRowLabels,
        (d.q1SliceAtom p).transposedAtom.complexBetaCoefficient l * star (f l)) := by
      simp only [star_sum, star_mul', star_star]
    _ = star (∑ l ∈ d.sharedFirstFactorRows,
        d.sharedFirstFactorCoefficient l * star (f ((p, l.1.1, l.1.2), l.2))) :=
      congrArg star (sum_slice_coefficient d hp (fun l ↦ star (f l)))
    _ = _ := by simp only [star_sum, star_mul', star_star]

private theorem pair_sum_slice_coefficient (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1)
    (K : ((ℕ × ℕ × ℕ) × ℕ) → ((ℕ × ℕ × ℕ) × ℕ) → ℂ) :
    (∑ l ∈ (d.q1SliceAtom p).transposedAtom.complexRowLabels,
      ∑ l' ∈ (d.q1SliceAtom p).transposedAtom.complexRowLabels,
        (d.q1SliceAtom p).transposedAtom.complexBetaCoefficient l *
          star ((d.q1SliceAtom p).transposedAtom.complexBetaCoefficient l') * K l l') =
      ∑ l ∈ d.sharedFirstFactorRows, ∑ l' ∈ d.sharedFirstFactorRows,
        d.sharedFirstFactorCoefficient l * star (d.sharedFirstFactorCoefficient l') *
          K ((p, l.1.1, l.1.2), l.2) ((p, l'.1.1, l'.1.2), l'.2) := by
  calc
    _ = ∑ l ∈ (d.q1SliceAtom p).transposedAtom.complexRowLabels,
        (d.q1SliceAtom p).transposedAtom.complexBetaCoefficient l *
          ∑ l' ∈ (d.q1SliceAtom p).transposedAtom.complexRowLabels,
            star ((d.q1SliceAtom p).transposedAtom.complexBetaCoefficient l') * K l l' := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ l ∈ d.sharedFirstFactorRows, d.sharedFirstFactorCoefficient l *
        ∑ l' ∈ (d.q1SliceAtom p).transposedAtom.complexRowLabels,
          star ((d.q1SliceAtom p).transposedAtom.complexBetaCoefficient l') *
            K ((p, l.1.1, l.1.2), l.2) l' :=
      sum_slice_coefficient d hp _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      rw [sum_star_slice_coefficient d hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l' _
      ring

end SharedFirstFactorDispersion

/-- Both physical moduli have the identical original first factor. -/
theorem sharedFirstFactor_gcd (p v1 v2 : ℕ) :
    (p * v1).gcd (p * v2) = p * v1.gcd v2 := Nat.gcd_mul_left p v1 v2

theorem sharedFirstFactor_lcm (p v1 v2 : ℕ) :
    (p * v1).lcm (p * v2) = p * v1.lcm v2 := Nat.lcm_mul_left p v1 v2

theorem sharedFirstFactor_compatible_iff (p v1 v2 n1 n2 : ℕ) :
    ComplexCRT.Compatible (p * v1) (p * v2) n1 n2 ↔
      n1.Coprime (p * v1) ∧ n2.Coprime (p * v2) ∧
        Nat.ModEq (p * v1.gcd v2) n1 n2 := by
  rw [ComplexCRT.Compatible, sharedFirstFactor_gcd]

/-- The reduced labels have no independent second copy of the first factor. -/
theorem MediumAtom.q1SliceDispersionW_eq_sharedCRT
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) (S : Finset ℕ) (w : ℕ → ℝ) :
    ((d.q1SliceAtom p).transposedAtom.complexDispersionW S w : ℂ) =
      ∑ l ∈ d.sharedFirstFactorRows, ∑ l' ∈ d.sharedFirstFactorRows,
        d.sharedFirstFactorCoefficient l * star (d.sharedFirstFactorCoefficient l') *
          (ComplexCRT.constructedProgressionWeight S w d.residue
            (p * (l.1.1 * l.1.2)) (p * (l'.1.1 * l'.1.2)) l.2 l'.2 : ℂ) := by
  have h := (d.q1SliceAtom p).transposedDispersionW_eq_constructedCRT
    (mediumAdmissible_q1SliceAtom hd hp) S w
  apply h.trans
  rw [show (d.q1SliceAtom p).residue = d.residue from rfl]
  simpa only [complexFactorModulus, Nat.mul_assoc] using
    SharedFirstFactorDispersion.pair_sum_slice_coefficient d (Finset.mem_filter.mp hp).1
      (fun l l' ↦ (ComplexCRT.constructedProgressionWeight S w d.residue
        (complexFactorModulus l.1) (complexFactorModulus l'.1) l.2 l'.2 : ℂ))

namespace SharedFirstFactorDispersion

private theorem reduced_modulus_pos
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {l : (ℕ × ℕ) × ℕ}
    (hl : l ∈ d.sharedFirstFactorRows) : 0 < l.1.1 * l.1.2 := by
  have hf := (Finset.mem_product.mp hl).1
  exact Nat.mul_pos (factor_pos hd.2.2.2.1 (Finset.mem_product.mp hf).1)
    (factor_pos hd.2.2.2.2.1 (Finset.mem_product.mp hf).2)

private theorem shared_progression_poisson
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier)
    {l l' : (ℕ × ℕ) × ℕ} (hl : l ∈ d.sharedFirstFactorRows)
    (hl' : l' ∈ d.sharedFirstFactorRows) :
    (ComplexCRT.constructedProgressionWeight d.transposedAtom.commonSmoothCarrier
      d.transposedAtom.commonSmoothWeight d.residue
      (p * (l.1.1 * l.1.2)) (p * (l'.1.1 * l'.1.2)) l.2 l'.2 : ℂ) =
      ((if ComplexCRT.Compatible (p * (l.1.1 * l.1.2))
          (p * (l'.1.1 * l'.1.2)) l.2 l'.2 then
        (d.V / ((p * (l.1.1 * l.1.2)).lcm (p * (l'.1.1 * l'.1.2)) : ℝ)) *
          CommonSmoothCutoff.cutoffMass +
            (∑' h : ℤ, CommonSmoothCutoff.poissonNonzeroFrequency
              (d.V / ((p * (l.1.1 * l.1.2)).lcm (p * (l'.1.1 * l'.1.2)) : ℝ))
              ((ComplexCRT.residue (p * (l.1.1 * l.1.2)) (p * (l'.1.1 * l'.1.2))
                l.2 l'.2 d.residue : ℝ) /
                  ((p * (l.1.1 * l.1.2)).lcm (p * (l'.1.1 * l'.1.2)) : ℝ)) h).re
      else 0 : ℝ) : ℂ) := by
  have hpos : 0 < p := factor_pos hd.2.2.1 (Finset.mem_filter.mp hp).1
  have hL : 0 < (p * (l.1.1 * l.1.2)).lcm (p * (l'.1.1 * l'.1.2)) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero
      (Nat.mul_pos hpos (reduced_modulus_pos hd hl)).ne'
      (Nat.mul_pos hpos (reduced_modulus_pos hd hl')).ne')
  unfold ComplexCRT.constructedProgressionWeight
  by_cases hc : ComplexCRT.Compatible (p * (l.1.1 * l.1.2))
      (p * (l'.1.1 * l'.1.2)) l.2 l'.2
  · simp only [if_pos hc]
    have he := CommonSmoothCutoff.scaledDyadicCutoff_finset_progression_eq_main_add_fourier
      (M := d.transposedAtom.U) (lt_of_lt_of_le zero_lt_one hd.2.1)
      d.transposedAtom.commonSmoothCarrier
      (fun m hm ↦ d.transposedSmoothWeight_support_subset hd.2.1 hm) hL
      (ComplexCRT.residue (p * (l.1.1 * l.1.2)) (p * (l'.1.1 * l'.1.2))
        l.2 l'.2 d.residue)
    simpa only [MediumAtom.commonSmoothWeight,
      show d.transposedAtom.U = d.V from rfl] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) he
  · simp only [if_neg hc]

private theorem factor_le_twice {Q : ℝ} (hQ : 1 ≤ Q) {p : ℕ}
    (hp : p ∈ factorCarrier Q) : (p : ℝ) ≤ 2 * Q :=
  (Nat.cast_le.mpr (Finset.mem_Icc.mp hp).2).trans (Nat.floor_le (by linarith))

private theorem reduced_modulus_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {l : (ℕ × ℕ) × ℕ}
    (hl : l ∈ d.sharedFirstFactorRows) :
    ((l.1.1 * l.1.2 : ℕ) : ℝ) ≤ 4 * d.Q2 * d.Q3 := by
  have hf := (Finset.mem_product.mp hl).1
  have h2 := factor_le_twice hd.2.2.2.1 (Finset.mem_product.mp hf).1
  have h3 := factor_le_twice hd.2.2.2.2.1 (Finset.mem_product.mp hf).2
  rw [Nat.cast_mul]
  calc
    _ ≤ (2 * d.Q2) * (2 * d.Q3) :=
      mul_le_mul h2 h3 (Nat.cast_nonneg _) (by linarith [hd.2.2.2.1])
    _ = _ := by ring

end SharedFirstFactorDispersion

/-- Full original-V Poisson, with a single shared p and every integer h. -/
theorem MediumAtom.q1SliceDispersionW_eq_sharedPoisson
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) :
    ((d.q1SliceAtom p).transposedAtom.complexDispersionW
      d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight : ℂ) =
      ∑ l ∈ d.sharedFirstFactorRows, ∑ l' ∈ d.sharedFirstFactorRows,
        d.sharedFirstFactorCoefficient l * star (d.sharedFirstFactorCoefficient l') *
          ((if ComplexCRT.Compatible (p * (l.1.1 * l.1.2))
              (p * (l'.1.1 * l'.1.2)) l.2 l'.2 then
            (d.V / ((p * (l.1.1 * l.1.2)).lcm (p * (l'.1.1 * l'.1.2)) : ℝ)) *
              CommonSmoothCutoff.cutoffMass +
                (∑' h : ℤ, CommonSmoothCutoff.poissonNonzeroFrequency
                  (d.V / ((p * (l.1.1 * l.1.2)).lcm (p * (l'.1.1 * l'.1.2)) : ℝ))
                  ((ComplexCRT.residue (p * (l.1.1 * l.1.2)) (p * (l'.1.1 * l'.1.2))
                    l.2 l'.2 d.residue : ℝ) /
                      ((p * (l.1.1 * l.1.2)).lcm (p * (l'.1.1 * l'.1.2)) : ℝ)) h).re
          else 0 : ℝ) : ℂ) := by
  rw [d.q1SliceDispersionW_eq_sharedCRT hd hp]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro l' hl'
  rw [SharedFirstFactorDispersion.shared_progression_poisson hd hp hl hl']

/-- Literal centers and the full nonzero part are summed on the same p carrier. -/
theorem MediumAtom.sharedFirstFactor_centered_identity
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ((∑ p ∈ d.primitiveFirstFactorCarrier,
      ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        d.transposedAtom.commonSmoothWeight m *
          ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ d.primitiveFirstFactorCarrier,
        (((d.q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
          2 * ((d.q1SliceAtom p).transposedAtom.complexDispersionV
            d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight : ℂ) +
          ((d.q1SliceAtom p).transposedAtom.complexDispersionU
            d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight : ℂ)) +
          (d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact (d.q1SliceAtom p).transposed_dispersion_identity_with_commonPoisson
    (mediumAdmissible_q1SliceAtom hd hp)

/-- The shared first factor enters the physical lcm once, not squared. -/
theorem MediumAtom.sharedFirstFactor_lcm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier)
    {l l' : (ℕ × ℕ) × ℕ} (hl : l ∈ d.sharedFirstFactorRows)
    (hl' : l' ∈ d.sharedFirstFactorRows) :
    (((p * (l.1.1 * l.1.2)).lcm (p * (l'.1.1 * l'.1.2)) : ℕ) : ℝ) ≤
      32 * d.Q1 * d.Q2 ^ 2 * d.Q3 ^ 2 := by
  have hpbound := SharedFirstFactorDispersion.factor_le_twice hd.2.2.1
    (Finset.mem_filter.mp hp).1
  have h1 := SharedFirstFactorDispersion.reduced_modulus_le hd hl
  have h2 := SharedFirstFactorDispersion.reduced_modulus_le hd hl'
  have hdiv : (l.1.1 * l.1.2).lcm (l'.1.1 * l'.1.2) ≤
      (l.1.1 * l.1.2) * (l'.1.1 * l'.1.2) :=
    Nat.le_of_dvd (Nat.mul_pos (SharedFirstFactorDispersion.reduced_modulus_pos hd hl)
      (SharedFirstFactorDispersion.reduced_modulus_pos hd hl')) (Nat.lcm_dvd_mul _ _)
  have hQ20 : 0 ≤ d.Q2 := by linarith [hd.2.2.2.1]
  have hQ30 : 0 ≤ d.Q3 := by linarith [hd.2.2.2.2.1]
  rw [sharedFirstFactor_lcm, Nat.cast_mul]
  calc
    _ ≤ (p : ℝ) * (((l.1.1 * l.1.2 : ℕ) : ℝ) *
        ((l'.1.1 * l'.1.2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hdiv) (Nat.cast_nonneg _)
    _ ≤ (2 * d.Q1) * ((4 * d.Q2 * d.Q3) * (4 * d.Q2 * d.Q3)) :=
      mul_le_mul hpbound
        (mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity))
        (by positivity) (by linarith [hd.2.2.1])
    _ = _ := by ring

/-- A support-frequency gate is transported without deleting either sign. -/
theorem MediumAtom.sharedFirstFactor_frequency_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier)
    {l l' : (ℕ × ℕ) × ℕ} (hl : l ∈ d.sharedFirstFactorRows)
    (hl' : l' ∈ d.sharedFirstFactorRows) {Z : ℝ} (hZ : 0 ≤ Z) (h : ℤ)
    (hh : |(h : ℝ)| ≤
      (((p * (l.1.1 * l.1.2)).lcm (p * (l'.1.1 * l'.1.2)) : ℝ) * Z) / d.V) :
    |(h : ℝ)| ≤ 32 * d.Q1 * d.Q2 ^ 2 * d.Q3 ^ 2 * Z / d.V := by
  exact hh.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (d.sharedFirstFactor_lcm_le hd hp hl hl') hZ)
    (by linarith [hd.2.1]))

end

end ImbalancedChen.Part3
