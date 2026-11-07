import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapModulusConvolution
import ImbalancedChen.CurrentChenP5CausalRhoFactorization

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The positive original sixth row and the negative ORIGINAL JOINT tenth/eleventh
native row are pushed to ONE signed physical coefficient. The sixth row uses
its genuine even-exit small/rough lower coefficient; the joint row keeps the
literal cell-selected near-cap upper Rosser coefficient. No extra beta is
silently multiplied into that coefficient. The same E is used throughout.

The joint low band is unmasked, and the entire high band keeps the original
last-pair complement. Fallback counts are retained. The construction neither
deletes the full clamp cell nor asserts a density/H248 or distribution licence.
-/

namespace ImbalancedChen.P5JointNativeSignedRegroup
noncomputable section
open Classical
open scoped BigOperators
open P5SelectedMaskTransport
open P5Z.U1011OriginalSixteenArithmeticProducts
open P5Z.U1011OriginalSixteenJointNearCapCompiler


structure LowerData where
  policy : (ℕ × ℕ) → List ℕ → Bool
  w : (ℕ × ℕ) → ℝ
  L : (ℕ × ℕ) → ℝ

def lowerRows (N : ℕ) (E : ℕ × ℕ → Prop) : Finset (ℕ × ℕ) :=
  (sixthSupport N).filter (fun t => ¬ E t)

def lowerDivisors (D : LowerData) (N : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  actualLowerSmallRoughModuli (D.policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t)
    (P5CausalRhoQuotientBridge.cutoff N)

def lowerRho (D : LowerData) (N : ℕ) (t : ℕ × ℕ) (d : ℕ) : ℝ :=
  actualLowerSmallRoughRho (D.policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t)
    (P5CausalRhoQuotientBridge.cutoff N) (D.L t) d

abbrev LowerMark := Σ _ : ℕ × ℕ, ℕ
def lowerMarks (D : LowerData) (N : ℕ) (E : ℕ × ℕ → Prop) : Finset LowerMark :=
  (lowerRows N E).sigma (lowerDivisors D N)
def lowerModulus (m : LowerMark) : ℕ := (m.1.1 * m.1.2) * m.2
def lowerSupport (D : LowerData) (N : ℕ) (E : ℕ × ℕ → Prop) : Finset ℕ :=
  (lowerMarks D N E).image lowerModulus
def lowerSigma (D : LowerData) (N : ℕ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ m ∈ (lowerMarks D N E).filter (fun m => lowerModulus m = q), lowerRho D N m.1 m.2

def support (D : LowerData) (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : Finset ℕ :=
  lowerSupport D N E ∪ P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport n N eta E
def sigma (D : LowerData) (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  lowerSigma D N E q - P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q

def lowBand (N : ℕ) (t : P5Z.U11Adaptive.Four) : Prop :=
  (t.2.2 : ℝ) < (N : ℝ) ^ (19 / 125 : ℝ)
def lowMarks (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) :=
  (P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.marks n N eta E).filter
    (fun m => lowBand N m.1)
def highMarks (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) :=
  (P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.marks n N eta E).filter
    (fun m => ¬ lowBand N m.1)
def nativeLowSigma (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ m ∈ (lowMarks n N eta E).filter
    (fun m => P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulus m = q),
    P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.weight n N eta m
def nativeHighSigma (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ m ∈ (highMarks n N eta E).filter
    (fun m => P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulus m = q),
    P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.weight n N eta m

/-- This is an identity of the ACTUAL active native divisor marks. Neither
the cell plan nor the divisor coefficient changes when E changes below H. -/
theorem lowMarks_unmasked (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) :
    lowMarks n N eta E = lowMarks n N eta (fun _ => False) := by
  ext m
  by_cases hlow : lowBand N m.1
  · simp only [lowMarks, Finset.mem_filter, hlow, and_true]
    simp only [P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.marks,
      Finset.mem_sigma, P5Z.U1011OriginalSixteenJointNativeCompiler.ordinaryTuples,
      P5U1011JointOverlap.jointSelector, chenY1011JointPrimeSelector,
      Finset.mem_filter, show (m.1.2.2 : ℝ) < (N : ℝ) ^ (19 / 125 : ℝ) from hlow,
      true_or]
  · simp only [lowMarks, Finset.mem_filter, hlow, and_false]

theorem nativeLowSigma_unmasked (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) :
    nativeLowSigma n N eta E q = nativeLowSigma n N eta (fun _ => False) q := by
  unfold nativeLowSigma
  rw [lowMarks_unmasked n N eta E]

/-- Equality at H is kept on the high side, with the SAME original last-pair
complement and the full original upper endpoint D. -/
theorem highMark_original_mask {n N : ℕ} {eta : ℚ} {E : ℕ × ℕ → Prop}
    {m : P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.Mark}
    (hm : m ∈ highMarks n N eta E) :
    (N : ℝ) ^ (19 / 125 : ℝ) ≤ (m.1.2.2 : ℝ) ∧
      (m.1.2.2 : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ) ∧ ¬ E m.1.2 := by
  obtain ⟨hm, hhigh⟩ := Finset.mem_filter.mp hm
  have ht := (Finset.mem_sigma.mp hm).1
  have hs := (Finset.mem_filter.mp ht).1
  have hb := P5U1011JointOverlap.joint_band_and_mask hs
  exact ⟨le_of_not_gt hhigh, hb.2.2.1, hb.2.2.2.resolve_left hhigh⟩

theorem native_sigma_low_high (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (q : ℕ) :
    P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q =
      nativeLowSigma n N eta (fun _ => False) q + nativeHighSigma n N eta E q := by
  have hl : (lowMarks n N eta E).filter
      (fun m => P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulus m = q) =
      (P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.fibre n N eta E q).filter
        (fun m => lowBand N m.1) := by
    ext m
    simp only [lowMarks, P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.fibre,
      Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  have hh : (highMarks n N eta E).filter
      (fun m => P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulus m = q) =
      (P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.fibre n N eta E q).filter
        (fun m => ¬ lowBand N m.1) := by
    ext m
    simp only [highMarks, P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.fibre,
      Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  rw [← nativeLowSigma_unmasked n N eta E q]
  unfold nativeLowSigma nativeHighSigma
  rw [hl, hh]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem signed_sigma_actual_bands (D : LowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (q : ℕ) :
    sigma D n N eta E q = lowerSigma D N E q -
      nativeLowSigma n N eta (fun _ => False) q - nativeHighSigma n N eta E q := by
  unfold sigma
  rw [native_sigma_low_high]
  ring

theorem lowerSigma_zero_off_support (D : LowerData) (N : ℕ) (E : ℕ × ℕ → Prop)
    {q : ℕ} (hq : q ∉ lowerSupport D N E) : lowerSigma D N E q = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm, heq⟩ := Finset.mem_filter.mp hm
  exact (hq (Finset.mem_image.mpr ⟨m, hm, heq⟩)).elim

theorem lower_pushforward (D : LowerData) (N : ℕ) (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors D N t,
      lowerRho D N t d * F ((t.1 * t.2) * d)) =
      ∑ q ∈ lowerSupport D N E, lowerSigma D N E q * F q := by
  have hm : (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors D N t,
      lowerRho D N t d * F ((t.1 * t.2) * d)) =
      ∑ m ∈ lowerMarks D N E, lowerRho D N m.1 m.2 * F (lowerModulus m) := by
    rw [lowerMarks, Finset.sum_sigma]
    rfl
  rw [hm]
  have hf := Finset.sum_fiberwise_of_maps_to (s := lowerMarks D N E)
    (t := lowerSupport D N E) (g := lowerModulus)
    (fun m hm => Finset.mem_image_of_mem lowerModulus hm)
    (fun m => lowerRho D N m.1 m.2 * F (lowerModulus m))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro q hq
  unfold lowerSigma
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

/-- One physical coefficient, before ANY norm or density estimate. Shared
moduli are subtracted inside the fibre, rather than counted as disjoint. -/
theorem signed_pushforward (D : LowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors D N t,
      lowerRho D N t d * F ((t.1 * t.2) * d)) -
    (∑ t ∈ ordinaryTuples n N E, ∑ d ∈
      P5Z.U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      coefficient n N eta t d * F (fullPrefix t * d)) =
      ∑ q ∈ support D n N eta E, sigma D n N eta E q * F q := by
  rw [lower_pushforward, P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.exact_pushforward]
  have hl : (∑ q ∈ lowerSupport D N E, lowerSigma D N E q * F q) =
      ∑ q ∈ support D n N eta E, lowerSigma D N E q * F q := by
    apply Finset.sum_subset (Finset.subset_union_left)
    intro q hq hnot
    rw [lowerSigma_zero_off_support D N E hnot, zero_mul]
  have hu : (∑ q ∈ P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport n N eta E, P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q * F q) =
      ∑ q ∈ support D n N eta E, P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q * F q := by
    apply Finset.sum_subset (Finset.subset_union_right)
    intro q hq hnot
    rw [P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma_zero_off_support hnot, zero_mul]
  rw [hl, hu, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  unfold sigma
  ring

/-- The positive branch of the signed coefficient keeps its TRUE lower
attachment: rough-positive uses beta-minus and rough-negative beta-plus.
There is no factorization or sign premise about the physical rho. -/
theorem signed_lower_smallrough_identity (D : LowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ t ∈ lowerRows N E,
      ∑ s ∈ actualSmallRosserSupport N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t),
      ∑ r ∈ fixedEvenRoughSupport (D.policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t)
        (P5CausalRhoQuotientBridge.cutoff N),
      P5CausalRhoFactorization.coefficient (D.policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t)
        (P5CausalRhoQuotientBridge.cutoff N) (D.L t) (s, r) *
        F (((t.1 * t.2) * s) * r)) -
    (∑ t ∈ ordinaryTuples n N E, ∑ d ∈
      P5Z.U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      coefficient n N eta t d * F (fullPrefix t * d)) =
      ∑ q ∈ support D n N eta E, sigma D n N eta E q * F q := by
  rw [← signed_pushforward D n N eta E F]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact (P5CausalRhoFactorization.signed_physical_sum_nested (D.policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (t.1 * t.2)
    (D.w t) (P5CausalRhoQuotientBridge.cutoff N) (D.L t) F).symm

def mainTerm (D : LowerData) (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (M : ℝ) : ℝ :=
  ∑ q ∈ support D n N eta E, sigma D n N eta E q * (M / (Nat.totient q : ℝ))
def signedAP (D : LowerData) (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) (M : ℝ) : ℝ :=
  ∑ q ∈ support D n N eta E, sigma D n N eta E q * chenQuotientPrimeAPError N M q
def signedCentre (D : LowerData) (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ q ∈ support D n N eta E, sigma D n N eta E q * chenCentrePrimeAPCount N N q
def estimator (D : LowerData) (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ q ∈ support D n N eta E, sigma D n N eta E q *
    (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)
def fallback (n N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ t ∈ fallbackTuples n N E, P5Z.U11Adaptive.weight N t

theorem same_sigma_main_AP_centre (D : LowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (M : ℝ) :
    estimator D n N eta E = mainTerm D n N eta E M +
      signedAP D n N eta E M - signedCentre D n N eta E := by
  unfold estimator mainTerm signedAP signedCentre
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  unfold chenQuotientPrimeAPError
  ring

/-- The lower side's totient product is licensed by the actual sixth
multiplier and the actual small/rough carrier, not by a matching premise. -/
theorem lower_row_phi_peeling (D : LowerData) (N : ℕ) {t : ℕ × ℕ}
    (ht : t ∈ sixthSupport N) (hw : D.w t ≤ P5CausalRhoQuotientBridge.cutoff N)
    (M : ℝ) :
    (∑ d ∈ lowerDivisors D N t, lowerRho D N t d *
      (M / (Nat.totient ((t.1 * t.2) * d) : ℝ))) =
      M / (Nat.totient (t.1 * t.2) : ℝ) *
        physicalDensitySum (lowerDivisors D N t) (lowerRho D N t) := by
  unfold physicalDensitySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hcop := P5CausalRhoQuotientBridge.moduli_coprime_multiplier
    (D.policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (t.1 * t.2) (D.w t) (P5CausalRhoQuotientBridge.cutoff N)
    hw (P5CausalRhoQuotientBridge.row_multiplier_rough ht) hd
  rw [Nat.totient_mul hcop, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Literal true-li main of the ONE signed sigma. The upper summand is
exactly the existing same-bank near-cap native main; the lower one retains
its actual even-exit density. Neither density is replaced by H248. -/
theorem same_sigma_true_li_main (D : LowerData) {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ lowerRows N E, D.w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    mainTerm D n N eta E (MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N) =
      (∑ t ∈ lowerRows N E,
        MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N /
          (Nat.totient (t.1 * t.2) : ℝ) *
          physicalDensitySum (lowerDivisors D N t) (lowerRho D N t)) -
      ∑ t ∈ ordinaryTuples n N E,
        P5Z.U1011OriginalSixteenJointNearCapCompiler.main n N eta t := by
  have h := signed_pushforward D n N eta E
    (fun q => MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N /
      (Nat.totient q : ℝ))
  change _ = mainTerm D n N eta E _ at h
  rw [P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.exact_pushforward,
    ← P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.main_pushforward hN heta E] at h
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact lower_row_phi_peeling D N (Finset.mem_filter.mp ht).1 (hw t ht) _

/-- Concrete finite transfer to the original signed U6-U10-U11 expression.
Only genuine small-attachment legality gates occur as hypotheses. -/
theorem original_joint_signed_lower (D : LowerData) {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hgates : ∀ t ∈ lowerRows N E,
      1 < D.L t ∧ D.w t ≤ D.L t ∧ D.w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    estimator D n N eta E - fallback n N E ≤
      currentChenUpsilon6 N E - currentChenUpsilon10 N - currentChenUpsilon11 N E := by
  have hl : (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors D N t,
      lowerRho D N t d * (chenPrimeAPCount N N ((t.1 * t.2) * d) -
        chenCentrePrimeAPCount N N ((t.1 * t.2) * d))) ≤ currentChenUpsilon6 N E := by
    rw [currentChenUpsilon6_eq_siftedQuotientPrimeSource]
    exact Finset.sum_le_sum (fun t ht =>
      P5CausalRhoQuotientBridge.rowEstimator_le_actual N D.policy D.w D.L t (hgates t ht))
  have hu := P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.original_count_upper_sigma (n := n) hN heta E
  have heq := signed_pushforward D n N eta E
    (fun q => chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)
  change _ - _ = estimator D n N eta E at heq
  have hn : (∑ t ∈ ordinaryTuples n N E, ∑ d ∈
      P5Z.U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      coefficient n N eta t d * (chenPrimeAPCount N N (fullPrefix t * d) -
        chenCentrePrimeAPCount N N (fullPrefix t * d))) =
      ∑ q ∈ P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport n N eta E, P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q *
        (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q) :=
    P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.exact_pushforward n N eta E _
  rw [hn] at heq
  change currentChenUpsilon10 N + currentChenUpsilon11 N E ≤ fallback n N E + _ at hu
  linarith only [hl, hu, heq]

def otherRows (N : ℕ) : ℝ :=
  3 * currentChenUpsilon1 N + currentChenUpsilon2 N - currentChenUpsilon3 N -
    currentChenUpsilon4 N + currentChenUpsilon5 N - 2 * currentChenUpsilon7 N -
    currentChenUpsilon8 N - currentChenUpsilon9 N

/-- The original paired weight, including the literal +U6/-U10/-U11 signs,
receives the SAME signed sigma for its main, AP and centre terms. -/
theorem original_paired_lower_same_sigma (D : LowerData) {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) (M : ℝ)
    (hgates : ∀ t ∈ lowerRows N E,
      1 < D.L t ∧ D.w t ≤ D.L t ∧ D.w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    otherRows N + mainTerm D n N eta E M + signedAP D n N eta E M -
      signedCentre D n N eta E - fallback n N E ≤ currentChenPairedPrimeSum N E := by
  have h := original_joint_signed_lower D hN heta E hgates
  rw [same_sigma_main_AP_centre D n N eta E M] at h
  rw [currentChenPairedPrimeSum_eq_upsilon]
  unfold otherRows
  linarith only [h]

end
end ImbalancedChen.P5JointNativeSignedRegroup
