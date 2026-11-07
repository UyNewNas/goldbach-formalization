import ImbalancedChen.Part3MediumActualPreliminaryCauchy
import ImbalancedChen.Part3MediumReceiverCutoffArithmetic
import ImbalancedChen.Part3OriginalGevreySharedRowDictionary
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual paperPsi is inserted on original q,m supports, where it is one,
BEFORE outer Cauchy. Positivity then enlarges only the quadratic carrier.
The SAME paperPsi and actual lambdaTrim are used in literal S1/S2/S3.
General beta is retained in its actual L2 sum, with an explicit finite
ordinary-divisor-moment bound rather than a one-bounded beta assumption.
-/
namespace ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalGevreySharedRowDictionary20261028
open ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter
open ImbalancedChen.Part3.MediumDeletedIndicatorShift20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumActualPostSquareDeletion20261028
open ImbalancedChen.Part3OriginalCanonicalS2Stages

/-- Real positive version of the already fixed source q weight. -/
def paperQWeight (atom : MediumAtom) (q : ℕ) : ℝ :=
  paperPsi ((q : ℝ) / atom.Q1)

theorem paperQWeight_cast (atom : MediumAtom) (q : ℕ) :
    (paperQWeight atom q : ℂ) = actualPsiQWeight atom q := rfl

private theorem original_factor_real_bounds {Q : ℝ} (hQ : 0 < Q)
    {q : ℕ} (hq : q ∈ factorCarrier Q) : Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hq
  constructor
  · exact (Nat.le_ceil Q).trans (by exact_mod_cast hlo)
  · exact (show (q : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

/-- The actual profile, not a postulated majorant, equals one on the
original closed dyadic support including both original endpoints. -/
theorem actualPsi_eq_one_on_factorCarrier {Q : ℝ} (hQ : 0 < Q)
    {q : ℕ} (hq : q ∈ factorCarrier Q) : paperPsi ((q : ℝ) / Q) = 1 := by
  obtain ⟨hlo, hhi⟩ := original_factor_real_bounds hQ hq
  apply paperPsi_eq_one_on_unit_interval
  exact ⟨(le_div_iff₀ hQ).mpr (by simpa using hlo),
    (div_le_iff₀ hQ).mpr hhi⟩

theorem factorCarrier_subset_paperPsiNaturalCarrier {Q : ℝ} (hQ : 0 < Q) :
    factorCarrier Q ⊆ paperPsiNaturalCarrier Q := by
  intro q hq
  obtain ⟨hlo, hhi⟩ := original_factor_real_bounds hQ hq
  apply mem_Icc.mpr
  exact ⟨Nat.ceil_le.mpr (by linarith), Nat.le_floor (by linarith)⟩

/-- Smooth q,m supports are the actual profile's [length/2,5length/2]
natural carriers. The exact d fibre stays in its original dyadic block. -/
def smoothOuterCarrier (atom : MediumAtom) (k : Key) : Finset OuterIndex :=
  paperPsiNaturalCarrier atom.Q1 ×ˢ (dyadicWindow k.d ×ˢ paperPsiNaturalCarrier atom.V)

def jointPsi (atom : MediumAtom) (t : OuterIndex) : ℝ :=
  paperQWeight atom t.1 * paperMWeight atom t.2.2

theorem jointPsi_nonneg (atom : MediumAtom) (t : OuterIndex) : 0 ≤ jointPsi atom t :=
  mul_nonneg (paperPsi_nonneg _) (paperPsi_nonneg _)

theorem jointPsi_eq_one_original {atom : MediumAtom} {k : Key}
    (hQ : 0 < atom.Q1) (hM : 0 < atom.V) {t : OuterIndex}
    (ht : t ∈ outerCarrier atom k) : jointPsi atom t = 1 := by
  obtain ⟨hq, hdm⟩ := mem_product.mp ht
  obtain ⟨hd, hm⟩ := mem_product.mp hdm
  have hm' : t.2.2 ∈ factorCarrier atom.V := hm
  simp only [jointPsi, paperQWeight, paperMWeight,
    actualPsi_eq_one_on_factorCarrier hQ hq,
    actualPsi_eq_one_on_factorCarrier hM hm', one_mul]

theorem outerCarrier_subset_smooth {atom : MediumAtom} {k : Key}
    (hQ : 0 < atom.Q1) (hM : 0 < atom.V) :
    outerCarrier atom k ⊆ smoothOuterCarrier atom k := by
  intro t ht
  obtain ⟨hq, hdm⟩ := mem_product.mp ht
  obtain ⟨hd, hm⟩ := mem_product.mp hdm
  exact mem_product.mpr ⟨factorCarrier_subset_paperPsiNaturalCarrier hQ hq,
    mem_product.mpr ⟨hd, factorCarrier_subset_paperPsiNaturalCarrier hM hm⟩⟩

/-- Both majorants are inserted into the exact LINEAR block source
before Cauchy. No sign or coefficient is replaced at this stage. -/
theorem blockSource_eq_actualPsi_inserted (atom : MediumAtom) (z y : ℝ)
    (k : Key) (hQ : 0 < atom.Q1) (hM : 0 < atom.V) :
    blockSource atom z y k = ∑ t ∈ outerCarrier atom k,
      outerCoefficient atom t * (jointPsi atom t : ℂ) *
        preliminaryRow atom z y k t.1 t.2.1 t.2.2 := by
  unfold blockSource
  apply sum_congr rfl
  intro t ht
  rw [jointPsi_eq_one_original hQ hM ht]
  simp

def smoothQuadratic (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ smoothOuterCarrier atom k, jointPsi atom t *
    ‖preliminaryRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2

/-- Only a nonnegative quadratic form is enlarged to smooth support. -/
theorem sharpQuadratic_le_actualPsi (atom : MediumAtom) (z y : ℝ)
    (k : Key) (hQ : 0 < atom.Q1) (hM : 0 < atom.V) :
    (∑ t ∈ outerCarrier atom k,
      ‖preliminaryRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2) ≤
      smoothQuadratic atom z y k := by
  calc
    _ = ∑ t ∈ outerCarrier atom k, jointPsi atom t *
        ‖preliminaryRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2 := by
      apply sum_congr rfl
      intro t ht
      rw [jointPsi_eq_one_original hQ hM ht, one_mul]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (outerCarrier_subset_smooth hQ hM)
      (fun t ht hnot => mul_nonneg (jointPsi_nonneg atom t) (sq_nonneg _))

/-- General beta keeps its ACTUAL L2 multiplier. No beta unit gate is
assumed for this actual same-profile Cauchy/majorant bound. -/
theorem blockSource_norm_sq_le_l2_actualPsi (atom : MediumAtom) (z y : ℝ)
    (k : Key) (hQ : 0 < atom.Q1) (hM : 0 < atom.V) :
    ‖blockSource atom z y k‖ ^ 2 ≤
      (∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2) *
        smoothQuadratic atom z y k := by
  have h0 : 0 ≤ ∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  exact (blockSource_norm_sq_le_preliminary_dispersion atom z y k).trans
    (mul_le_mul_of_nonneg_left (sharpQuadratic_le_actualPsi atom z y k hQ hM) h0)

/-- Literal S1, S2 and S3 of THIS same-d dispersion and THIS profile. -/
def samePsiS1 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ smoothOuterCarrier atom k, jointPsi atom t *
    ‖principalRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2

def samePsiS2 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ smoothOuterCarrier atom k, jointPsi atom t *
    (progressionRow atom z y k t.1 t.2.1 t.2.2 *
      star (principalRow atom z y k t.1 t.2.1 t.2.2)).re

def samePsiS3 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ smoothOuterCarrier atom k, jointPsi atom t *
    ‖progressionRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2

theorem samePsi_dispersion_identity (atom : MediumAtom) (z y : ℝ) (k : Key) :
    smoothQuadratic atom z y k =
      samePsiS3 atom z y k - 2 * samePsiS2 atom z y k + samePsiS1 atom z y k := by
  unfold smoothQuadratic samePsiS1 samePsiS2 samePsiS3
  simp_rw [preliminaryRow_eq_progression_sub_principal]
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, starRingEnd_apply]
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  ring

def meanEntry (atom : MediumAtom) (z y : ℝ) (k : Key)
    (t : OuterIndex) (i : ℕ × ℕ) : ℂ :=
  lambdaTrim atom z y k t.2.1 i.1 * atom.alpha i.2 *
    literalMeanKernel atom t.1 t.2.1 i.1 i.2 t.2.2

def deletedEntry (atom : MediumAtom) (z y : ℝ) (k : Key)
    (t : OuterIndex) (i : ℕ × ℕ) : ℂ :=
  lambdaTrim atom z y k t.2.1 i.1 * atom.alpha i.2 *
    deletedIndicator atom.residue ((t.1 * t.2.1) * i.1) i.2 t.2.2

/-- Original q,d,m plus two INDEPENDENT (r,n) labels. The physical
moduli are respectively q*d*r and q*d*s, and m is literally shared. -/
def literalS1 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ smoothOuterCarrier atom k, (jointPsi atom t : ℂ) *
    ∑ i ∈ innerCarrier atom k, ∑ j ∈ innerCarrier atom k,
      meanEntry atom z y k t i * star (meanEntry atom z y k t j)

def literalS2 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ smoothOuterCarrier atom k, (jointPsi atom t : ℂ) *
    ∑ i ∈ innerCarrier atom k, ∑ j ∈ innerCarrier atom k,
      deletedEntry atom z y k t i * star (meanEntry atom z y k t j)

def literalS3 (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ smoothOuterCarrier atom k, (jointPsi atom t : ℂ) *
    ∑ i ∈ innerCarrier atom k, ∑ j ∈ innerCarrier atom k,
      deletedEntry atom z y k t i * star (deletedEntry atom z y k t j)

private theorem cast_norm_sq (v : ℂ) : ((‖v‖ : ℂ) ^ 2) = v * star v :=
  (Complex.mul_conj' v).symm

/-- The S1 carrier is the actual same-mean quadratic carrier, not an
unrelated coefficient array. All complex lambda/alpha signs are retained. -/
theorem samePsiS1_cast_eq_literal (atom : MediumAtom) (z y : ℝ) (k : Key) :
    (samePsiS1 atom z y k : ℂ) = literalS1 atom z y k := by
  unfold samePsiS1 literalS1
  rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  apply sum_congr rfl
  intro t ht
  rw [cast_norm_sq]
  unfold principalRow meanEntry
  rw [star_sum, sum_mul_sum]

/-- The original ordered S2 cross term contributes its real part. -/
theorem samePsiS2_eq_literal_re (atom : MediumAtom) (z y : ℝ) (k : Key) :
    samePsiS2 atom z y k = (literalS2 atom z y k).re := by
  have hp : literalS2 atom z y k =
      ∑ t ∈ smoothOuterCarrier atom k, (jointPsi atom t : ℂ) *
        (progressionRow atom z y k t.1 t.2.1 t.2.2 *
          star (principalRow atom z y k t.1 t.2.1 t.2.2)) := by
    unfold literalS2
    apply sum_congr rfl
    intro t ht
    unfold progressionRow principalRow deletedEntry meanEntry
    rw [star_sum, sum_mul_sum]
  rw [hp]
  simp [samePsiS2, Complex.mul_re]

theorem samePsiS3_cast_eq_literal (atom : MediumAtom) (z y : ℝ) (k : Key) :
    (samePsiS3 atom z y k : ℂ) = literalS3 atom z y k := by
  unfold samePsiS3 literalS3
  rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  apply sum_congr rfl
  intro t ht
  rw [cast_norm_sq]
  unfold progressionRow deletedEntry
  rw [star_sum, sum_mul_sum]

/-- Physical same-profile dispersion bound with the original beta L2. -/
theorem blockSource_norm_sq_le_samePsi_S123 (atom : MediumAtom) (z y : ℝ)
    (k : Key) (hQ : 0 < atom.Q1) (hM : 0 < atom.V) :
    ‖blockSource atom z y k‖ ^ 2 ≤
      (∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2) *
        (samePsiS3 atom z y k - 2 * samePsiS2 atom z y k + samePsiS1 atom z y k) := by
  simpa only [samePsi_dispersion_identity] using
    blockSource_norm_sq_le_l2_actualPsi atom z y k hQ hM

/-- The actual coprime alpha mass, for a later S1 common-m dictionary. -/
def alphaCoprime (atom : MediumAtom) (ell r : ℕ) : ℂ :=
  ∑ n ∈ atom.alphaCarrier, if n.Coprime (ell * r) then atom.alpha n else 0

/-- The mean factorization follows from the actual (nm,qdr)=1 gate;
no primitive-class hypothesis is silently substituted for it. -/
theorem sum_literalMean_eq_alphaCoprime (atom : MediumAtom) (q d r m : ℕ) :
    (∑ n ∈ atom.alphaCarrier, atom.alpha n * literalMeanKernel atom q d r n m) =
      if m.Coprime ((q * d) * r) then
        alphaCoprime atom (q * d) r / (Nat.totient ((q * d) * r) : ℂ) else 0 := by
  by_cases hm : m.Coprime ((q * d) * r)
  · simp only [if_pos hm]
    unfold literalMeanKernel alphaCoprime
    rw [sum_div]
    apply sum_congr rfl
    intro n hn
    by_cases hnC : n.Coprime ((q * d) * r) <;>
      simp [Nat.coprime_mul_iff_left, hm, hnC]
  · unfold literalMeanKernel
    simp [Nat.coprime_mul_iff_left, hm]

/-- Explicit ordinary-divisor-moment payment for general beta. This is
an exact finite bound; no unproved asymptotic mean is supplied. -/
def betaDivisorL2 (atom : MediumAtom) (B : ℕ) : ℝ :=
  ∑ m ∈ atom.betaCarrier, (m.divisors.card : ℝ) ^ (2 * B)

theorem actual_outer_l2_le_divisor_payment (atom : MediumAtom) (k : Key) (B : ℕ)
    (hb : ∀ m ∈ atom.betaCarrier, ‖atom.beta m‖ ≤ (m.divisors.card : ℝ) ^ B) :
    (∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2) ≤
      ∑ q ∈ factorCarrier atom.Q1, ∑ _d ∈ dyadicWindow k.d,
        ‖atom.gamma1 q‖ ^ 2 * betaDivisorL2 atom B := by
  unfold outerCarrier outerCoefficient betaDivisorL2
  simp only [sum_product, norm_mul, mul_pow]
  apply sum_le_sum
  intro q hq
  apply sum_le_sum
  intro d hd
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hpow := pow_le_pow_left₀ (norm_nonneg (atom.beta m)) (hb m hm) 2
  simpa only [← pow_mul, Nat.mul_comm B 2] using hpow

theorem actual_outer_l2_le_gamma_divisor_moments (atom : MediumAtom) (k : Key) (B : ℕ)
    (hb : ∀ m ∈ atom.betaCarrier, ‖atom.beta m‖ ≤ (m.divisors.card : ℝ) ^ B) :
    (∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2) ≤
      (∑ q ∈ factorCarrier atom.Q1, ‖atom.gamma1 q‖ ^ 2) *
        (dyadicWindow k.d).card * betaDivisorL2 atom B := by
  have h := actual_outer_l2_le_divisor_payment atom k B hb
  have heq :
      (∑ q ∈ factorCarrier atom.Q1, ∑ _d ∈ dyadicWindow k.d,
        ‖atom.gamma1 q‖ ^ 2 * betaDivisorL2 atom B) =
      (∑ q ∈ factorCarrier atom.Q1, ‖atom.gamma1 q‖ ^ 2) *
        (dyadicWindow k.d).card * betaDivisorL2 atom B := by
    simp only [sum_const, nsmul_eq_mul]
    rw [sum_mul]
    rw [sum_mul]
    apply sum_congr rfl
    intro q hq
    ring
  exact h.trans_eq heq

theorem smoothQuadratic_nonneg (atom : MediumAtom) (z y : ℝ) (k : Key) :
    0 ≤ smoothQuadratic atom z y k :=
  sum_nonneg fun t ht => mul_nonneg (jointPsi_nonneg atom t) (sq_nonneg _)

/-- General divisor-bounded beta is paid by its explicit original
finite moment. No truncation or auxiliary one-bounded beta is hidden. -/
theorem blockSource_norm_sq_le_betaDivisor_moments
    (atom : MediumAtom) (z y : ℝ) (k : Key) (B : ℕ)
    (hQ : 0 < atom.Q1) (hM : 0 < atom.V)
    (hb : ∀ m ∈ atom.betaCarrier, ‖atom.beta m‖ ≤ (m.divisors.card : ℝ) ^ B) :
    ‖blockSource atom z y k‖ ^ 2 ≤
      ((∑ q ∈ factorCarrier atom.Q1, ‖atom.gamma1 q‖ ^ 2) *
        (dyadicWindow k.d).card * betaDivisorL2 atom B) *
      (samePsiS3 atom z y k - 2 * samePsiS2 atom z y k + samePsiS1 atom z y k) := by
  have h := (blockSource_norm_sq_le_l2_actualPsi atom z y k hQ hM).trans
    (mul_le_mul_of_nonneg_right (actual_outer_l2_le_gamma_divisor_moments atom k B hb)
      (smoothQuadratic_nonneg atom z y k))
  simpa only [samePsi_dispersion_identity] using h

/-- Original inclusive-smooth trim, stated directly with the manuscript's
zSmoothPart. The analytic cutoff is z; the strict receiver translation is
not silently substituted for the original rough-support statement. -/
def originalRetainedRows (atom : MediumAtom) (z y : ℝ) : Finset RowLabel :=
  atom.complexRowLabels.filter fun l =>
    (rowModuli l).1 ≠ 0 ∧ (rowModuli l).2 ≠ 0 ∧
    (zSmoothPart z (rowModuli l).1 : ℝ) ≤ y ∧
    (zSmoothPart z (rowModuli l).2 : ℝ) ≤ y

theorem originalRetainedRows_eq_receiver (atom : MediumAtom) (z y : ℝ)
    (hz : 0 ≤ z) :
    originalRetainedRows atom z y = retainedRows atom (strictReceiverCutoff z) y := by
  ext l
  simp only [originalRetainedRows, retainedRows, mem_filter, Retained,
    originalSmooth_eq_receiver z hz]

def originalRetainedSource (atom : MediumAtom) (z y : ℝ) : ℂ :=
  ∑ l ∈ originalRetainedRows atom z y, deletedLinearTerm atom l

/-- This is the ORIGINAL inclusive-z linear source and the SAME actual
paperPsi, now connected to the strict receiver at its exact translated
integer support. No boundary-prime exceptional term is discarded. -/
theorem originalRetainedSource_eq_actualPsi_blocks (atom : MediumAtom)
    (z y : ℝ) (hz : 0 ≤ z) (hQ : 0 < atom.Q1) (hM : 0 < atom.V) :
    originalRetainedSource atom z y =
      ∑ k ∈ keyBank atom (strictReceiverCutoff z) y,
        ∑ t ∈ outerCarrier atom k, outerCoefficient atom t * (jointPsi atom t : ℂ) *
          preliminaryRow atom (strictReceiverCutoff z) y k t.1 t.2.1 t.2.2 := by
  unfold originalRetainedSource
  rw [originalRetainedRows_eq_receiver atom z y hz]
  change retainedSource atom (strictReceiverCutoff z) y = _
  rw [retainedSource_eq_sum_blockSource]
  apply sum_congr rfl
  intro k hk
  exact blockSource_eq_actualPsi_inserted atom (strictReceiverCutoff z) y k hQ hM

end
end ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
