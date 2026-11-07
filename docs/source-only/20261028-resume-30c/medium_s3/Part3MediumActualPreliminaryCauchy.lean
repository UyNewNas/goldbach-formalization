import ImbalancedChen.Part3MediumOwnedCanonicalReindex
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Paper medium module 102--124, 156--160, 193--221, 251--257.
The preliminary outer Cauchy is taken on the LINEAR retained signed
source, over (q,d,m), before its (r,n) row is squared. It is not a
postulated identification of independent labels in a pre-existing W.
All d in one dyadic key remain inside this one Cauchy application.
-/
namespace ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumOwnedCanonicalReindex20261028
open ImbalancedChen.Part3.MediumActualPostSquareDeletion20261028
open ImbalancedChen.Part3.MediumInstalledFactorChoiceMap20261028
open ImbalancedChen.Part3.MediumDeletedIndicatorShift20261028
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028

/-- The exact original coprime mean, unchanged when nm=a is removed. -/
def physicalMeanKernel (atom : MediumAtom) (n : ℕ) (l : RowLabel) : ℂ :=
  (if (n * l.2).Coprime (complexFactorModulus l.1) then 1 else 0) /
    (Nat.totient (complexFactorModulus l.1) : ℂ)

def physicalDeletedKernel (atom : MediumAtom) (n : ℕ) (l : RowLabel) : ℂ :=
  deletedCongruence atom n l - physicalMeanKernel atom n l

theorem primitiveKernel_eq_deleted_add_exact (atom : MediumAtom)
    (n : ℕ) (l : RowLabel) :
    complexPrimitiveKernel atom.residue (complexFactorModulus l.1) n l.2 =
      physicalDeletedKernel atom n l + exactCongruence atom n l := by
  change fullCongruence atom n l - physicalMeanKernel atom n l = _
  rw [fullCongruence_eq_deleted_add_exact]
  unfold physicalDeletedKernel
  ring

def deletedLinearTerm (atom : MediumAtom) (l : RowLabel) : ℂ :=
  ∑ n ∈ atom.alphaCarrier, atom.alpha n * atom.complexFactorGamma l.1 *
    atom.beta l.2 * physicalDeletedKernel atom n l

def retainedSource (atom : MediumAtom) (z y : ℝ) : ℂ :=
  ∑ l ∈ retainedRows atom z y, deletedLinearTerm atom l

def discardedRows (atom : MediumAtom) (z y : ℝ) : Finset RowLabel :=
  atom.complexRowLabels.filter (fun l => ¬ Retained z y (rowModuli l))

def discardedSource (atom : MediumAtom) (z y : ℝ) : ℂ :=
  ∑ l ∈ discardedRows atom z y, deletedLinearTerm atom l

def exactProductCorrection (atom : MediumAtom) : ℂ :=
  ∑ l ∈ atom.complexRowLabels, ∑ n ∈ atom.alphaCarrier,
    atom.alpha n * atom.complexFactorGamma l.1 * atom.beta l.2 *
      exactCongruence atom n l

/-- Exact deletion/trim decomposition of the installed signedError.
No estimate for either correction, and no m-dependent SW, is assumed. -/
theorem signedError_eq_retained_discarded_exact (atom : MediumAtom) (z y : ℝ) :
    atom.signedError = retainedSource atom z y + discardedSource atom z y +
      exactProductCorrection atom := by
  have hraw : atom.signedError =
      ∑ l ∈ atom.complexRowLabels, ∑ n ∈ atom.alphaCarrier,
        atom.alpha n * atom.complexFactorGamma l.1 * atom.beta l.2 *
          complexPrimitiveKernel atom.residue (complexFactorModulus l.1) n l.2 := by
    rw [MediumAtom.signedError_eq_complexCenteredRows]
    simp only [MediumAtom.complexCenteredRow_eq_sum, mul_sum,
      MediumAtom.complexRowContribution]
    rw [sum_comm]
    apply sum_congr rfl
    intro l hl
    apply sum_congr rfl
    intro n hn
    ring
  have hsplit : (∑ l ∈ atom.complexRowLabels, deletedLinearTerm atom l) =
      retainedSource atom z y + discardedSource atom z y := by
    unfold retainedSource discardedSource retainedRows discardedRows
    simp only [sum_filter]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro l hl
    by_cases h : Retained z y (rowModuli l) <;> simp [h]
  rw [hraw, ← hsplit]
  unfold deletedLinearTerm exactProductCorrection
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro l hl
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  rw [primitiveKernel_eq_deleted_add_exact]
  ring

/-- Literal same-mean deleted kernel on the physical modulus q*d*r. -/
def literalMeanKernel (atom : MediumAtom) (q d r n m : ℕ) : ℂ :=
  (if (n * m).Coprime ((q * d) * r) then 1 else 0) /
    (Nat.totient ((q * d) * r) : ℂ)

def literalDeletedKernel (atom : MediumAtom) (q d r n m : ℕ) : ℂ :=
  deletedIndicator atom.residue ((q * d) * r) n m -
    literalMeanKernel atom q d r n m

theorem physicalDeletedKernel_installed_eq_literal (atom : MediumAtom)
    (q d r n m : ℕ) (p : Factor)
    (hd : p.s * p.t = d) (hr : p.u * p.v = r) :
    physicalDeletedKernel atom n (installedLabel q m p) =
      literalDeletedKernel atom q d r n m := by
  unfold physicalDeletedKernel physicalMeanKernel literalDeletedKernel literalMeanKernel
  rw [installed_deleted_indicator_eq_literal atom q m d r n p hd hr,
    installed_modulus_eq_literal q m d r p hd hr]
  simp only [installedLabel]
  congr 1
  simp [deletedIndicator, Nat.mul_comm]

/-- The actual trimmed Lambda, not an externally supplied coefficient. -/
def lambdaTrim (atom : MediumAtom) (z y : ℝ) (k : Key) (d r : ℕ) : ℂ :=
  ∑ p ∈ trimmedChoices atom z y k d r, ((fixedBlock k d).factorData atom z).term p

abbrev OuterIndex := ℕ × ℕ × ℕ

def outerCarrier (atom : MediumAtom) (k : Key) : Finset OuterIndex :=
  factorCarrier atom.Q1 ×ˢ (dyadicWindow k.d ×ˢ atom.betaCarrier)

def outerCoefficient (atom : MediumAtom) (t : OuterIndex) : ℂ :=
  atom.gamma1 t.1 * atom.beta t.2.2

/-- The r,n labels remain independent inside each fixed q,d,m row. -/
def innerCarrier (atom : MediumAtom) (k : Key) : Finset (ℕ × ℕ) :=
  dyadicWindow k.w ×ˢ atom.alphaCarrier

def preliminaryRow (atom : MediumAtom) (z y : ℝ) (k : Key)
    (q d m : ℕ) : ℂ :=
  ∑ i ∈ innerCarrier atom k,
    lambdaTrim atom z y k d i.1 * atom.alpha i.2 *
      literalDeletedKernel atom q d i.1 i.2 m

def blockSource (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ outerCarrier atom k, outerCoefficient atom t *
    preliminaryRow atom z y k t.1 t.2.1 t.2.2

/-- Pointwise arithmetic/weight identity before ANY Cauchy. -/
theorem selected_term_eq_literal (atom : MediumAtom) (z y : ℝ) (k : Key)
    (q d r m n : ℕ) (p : Factor)
    (hp : p ∈ trimmedChoices atom z y k d r) :
    atom.alpha n * atom.complexFactorGamma (q, p.u * p.s, p.v * p.t) *
      atom.beta m * physicalDeletedKernel atom n ((q, p.u * p.s, p.v * p.t), m) =
    atom.gamma1 q * atom.beta m *
      ((fixedBlock k d).factorData atom z).term p * atom.alpha n *
      literalDeletedKernel atom q d r n m := by
  have hpChoice := (mem_filter.mp hp).1
  obtain ⟨hd, hr, ha⟩ := choice_products hpChoice
  rw [show atom.complexFactorGamma (q, p.u * p.s, p.v * p.t) =
      atom.gamma1 q * ((fixedBlock k d).factorData atom z).term p from
      installed_factor_coefficient_eq_choice atom _ q m p rfl rfl]
  rw [show physicalDeletedKernel atom n ((q, p.u * p.s, p.v * p.t), m) =
      literalDeletedKernel atom q d r n m from
      physicalDeletedKernel_installed_eq_literal atom q d r n m p hd hr]
  ring

/-- The original factor choices collapse only AFTER the beta variable
has been moved to the outside. Both sum swaps are exact finite Fubini. -/
theorem fixed_d_source_eq_preliminary (atom : MediumAtom) (z y : ℝ)
    (k : Key) (q d : ℕ) :
    (∑ r ∈ dyadicWindow k.w, ∑ p ∈ trimmedChoices atom z y k d r,
      ∑ m ∈ atom.betaCarrier, ∑ n ∈ atom.alphaCarrier,
        atom.alpha n * atom.complexFactorGamma (q, p.u * p.s, p.v * p.t) *
          atom.beta m * physicalDeletedKernel atom n ((q, p.u * p.s, p.v * p.t), m)) =
      ∑ m ∈ atom.betaCarrier, outerCoefficient atom (q, d, m) *
        preliminaryRow atom z y k q d m := by
  calc
    _ = ∑ r ∈ dyadicWindow k.w, ∑ m ∈ atom.betaCarrier,
        ∑ p ∈ trimmedChoices atom z y k d r, ∑ n ∈ atom.alphaCarrier,
          atom.alpha n * atom.complexFactorGamma (q, p.u * p.s, p.v * p.t) *
            atom.beta m * physicalDeletedKernel atom n ((q, p.u * p.s, p.v * p.t), m) := by
      apply sum_congr rfl
      intro r hr
      exact sum_comm
    _ = ∑ m ∈ atom.betaCarrier, ∑ r ∈ dyadicWindow k.w,
        ∑ p ∈ trimmedChoices atom z y k d r, ∑ n ∈ atom.alphaCarrier,
          atom.alpha n * atom.complexFactorGamma (q, p.u * p.s, p.v * p.t) *
            atom.beta m * physicalDeletedKernel atom n ((q, p.u * p.s, p.v * p.t), m) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro m hm
      unfold preliminaryRow innerCarrier outerCoefficient
      simp only [sum_product, mul_sum]
      apply sum_congr rfl
      intro r hr
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      unfold lambdaTrim
      simp only [sum_mul, mul_sum]
      apply sum_congr rfl
      intro p hp
      simpa only [mul_assoc] using selected_term_eq_literal atom z y k q d r m n p hp

/-- Full retained original signed source is decomposed into finitely
many blocks BEFORE applying preliminary Cauchy. No estimate is inserted. -/
theorem retainedSource_eq_sum_blockSource (atom : MediumAtom) (z y : ℝ) :
    retainedSource atom z y = ∑ k ∈ keyBank atom z y, blockSource atom z y k := by
  unfold retainedSource deletedLinearTerm
  rw [sum_retainedRows_eq_global_canonical]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  unfold blockSource outerCarrier
  simp only [sum_product]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro d hd
  exact fixed_d_source_eq_preliminary atom z y k q d

/-- This is the preliminary Cauchy that creates common q,d,m in its
quadratic row. It does not remove cross terms from an already squared W. -/
theorem blockSource_norm_sq_le_preliminary_dispersion
    (atom : MediumAtom) (z y : ℝ) (k : Key) :
    ‖blockSource atom z y k‖ ^ 2 ≤
      (∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2) *
        ∑ t ∈ outerCarrier atom k,
          ‖preliminaryRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2 :=
  complex_finset_cauchy_norm_sq (outerCarrier atom k) (outerCoefficient atom)
    (fun t => preliminaryRow atom z y k t.1 t.2.1 t.2.2)

def progressionRow (atom : MediumAtom) (z y : ℝ) (k : Key) (q d m : ℕ) : ℂ :=
  ∑ i ∈ innerCarrier atom k, lambdaTrim atom z y k d i.1 * atom.alpha i.2 *
    deletedIndicator atom.residue ((q * d) * i.1) i.2 m

def principalRow (atom : MediumAtom) (z y : ℝ) (k : Key) (q d m : ℕ) : ℂ :=
  ∑ i ∈ innerCarrier atom k, lambdaTrim atom z y k d i.1 * atom.alpha i.2 *
    literalMeanKernel atom q d i.1 i.2 m

theorem preliminaryRow_eq_progression_sub_principal
    (atom : MediumAtom) (z y : ℝ) (k : Key) (q d m : ℕ) :
    preliminaryRow atom z y k q d m =
      progressionRow atom z y k q d m - principalRow atom z y k q d m := by
  unfold preliminaryRow progressionRow principalRow literalDeletedKernel
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  ring

def dispersionW (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ outerCarrier atom k, ‖progressionRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2

def dispersionV (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ outerCarrier atom k,
    (progressionRow atom z y k t.1 t.2.1 t.2.2 *
      star (principalRow atom z y k t.1 t.2.1 t.2.2)).re

def dispersionU (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ outerCarrier atom k, ‖principalRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2

/-- Actual finite three-term dispersion, with the same original mean.
Neither U nor V is replaced by its principal asymptotic. -/
theorem preliminary_dispersion_identity (atom : MediumAtom) (z y : ℝ) (k : Key) :
    (∑ t ∈ outerCarrier atom k, ‖preliminaryRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2) =
      dispersionW atom z y k - 2 * dispersionV atom z y k + dispersionU atom z y k := by
  unfold dispersionW dispersionV dispersionU
  simp_rw [preliminaryRow_eq_progression_sub_principal]
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, starRingEnd_apply]
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  ring

/-- The two inner (rough modulus, alpha integer) labels are independent.
They share q,d,m because they are squared INSIDE that actual outer fibre. -/
theorem progressionRow_square_eq_independent_inner_pairs
    (atom : MediumAtom) (z y : ℝ) (k : Key) (q d m : ℕ) :
    progressionRow atom z y k q d m * star (progressionRow atom z y k q d m) =
      ∑ i ∈ innerCarrier atom k, ∑ j ∈ innerCarrier atom k,
        (lambdaTrim atom z y k d i.1 * atom.alpha i.2 *
          deletedIndicator atom.residue ((q * d) * i.1) i.2 m) *
        star (lambdaTrim atom z y k d j.1 * atom.alpha j.2 *
          deletedIndicator atom.residue ((q * d) * j.1) j.2 m) := by
  unfold progressionRow
  rw [star_sum, sum_mul_sum]

/-- One-bounded original gamma1 and beta give the actual finite outer
multiplier; every d in the block is counted once in this one sum. -/
theorem outerCoefficient_l2_le_card (atom : MediumAtom) (k : Key)
    (hg : ∀ q ∈ factorCarrier atom.Q1, ‖atom.gamma1 q‖ ≤ 1)
    (hb : ∀ m ∈ atom.betaCarrier, ‖atom.beta m‖ ≤ 1) :
    (∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2) ≤
      ((outerCarrier atom k).card : ℝ) := by
  calc
    _ ≤ ∑ _t ∈ outerCarrier atom k, (1 : ℝ) := by
      apply sum_le_sum
      intro t ht
      obtain ⟨hq, hdm⟩ := mem_product.mp ht
      obtain ⟨hd, hm⟩ := mem_product.mp hdm
      have ht1 : ‖outerCoefficient atom t‖ ≤ 1 := by
        rw [outerCoefficient, norm_mul]
        calc
          _ ≤ (1 : ℝ) * 1 := mul_le_mul (hg _ hq) (hb _ hm) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      simpa only [one_pow] using
        (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2 ht1
    _ = _ := by simp

theorem outerCarrier_card (atom : MediumAtom) (k : Key) :
    (outerCarrier atom k).card = (factorCarrier atom.Q1).card *
      ((dyadicWindow k.d).card * atom.betaCarrier.card) := by
  simp [outerCarrier]

/-- Cauchy and dispersion are connected for this SAME block and mean. -/
theorem blockSource_norm_sq_le_card_mul_dispersion
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hg : ∀ q ∈ factorCarrier atom.Q1, ‖atom.gamma1 q‖ ≤ 1)
    (hb : ∀ m ∈ atom.betaCarrier, ‖atom.beta m‖ ≤ 1) :
    ‖blockSource atom z y k‖ ^ 2 ≤ ((outerCarrier atom k).card : ℝ) *
      (dispersionW atom z y k - 2 * dispersionV atom z y k + dispersionU atom z y k) := by
  have h := blockSource_norm_sq_le_preliminary_dispersion atom z y k
  have hnonneg : 0 ≤ ∑ t ∈ outerCarrier atom k,
      ‖preliminaryRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hmult := mul_le_mul_of_nonneg_right (outerCoefficient_l2_le_card atom k hg hb) hnonneg
  have hfinal := h.trans hmult
  simpa only [preliminary_dispersion_identity] using hfinal

/-- A concrete finite M*Y-type multiplier, using the original q and
beta supports and the upper endpoint 2D of the one dyadic d block. -/
theorem outerCarrier_card_le_physical_lengths (atom : MediumAtom) (k : Key) :
    (outerCarrier atom k).card ≤
      (Nat.floor (2 * atom.Q1) + 1) *
        (2 ^ (k.d + 1) * (Nat.floor (2 * atom.V) + 1)) := by
  have hq : (factorCarrier atom.Q1).card ≤ Nat.floor (2 * atom.Q1) + 1 := by
    have hsub : factorCarrier atom.Q1 ⊆ range (Nat.floor (2 * atom.Q1) + 1) := by
      intro q hq
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hq).2)
    simpa only [card_range] using card_le_card hsub
  have hd : (dyadicWindow k.d).card ≤ 2 ^ (k.d + 1) := by
    have hsub : dyadicWindow k.d ⊆ range (2 ^ (k.d + 1)) := by
      intro d hd
      exact mem_range.mpr (mem_Ico.mp hd).2
    simpa only [card_range] using card_le_card hsub
  have hm : atom.betaCarrier.card ≤ Nat.floor (2 * atom.V) + 1 := by
    have hsub : atom.betaCarrier ⊆ range (Nat.floor (2 * atom.V) + 1) := by
      intro m hm
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hm).2)
    simpa only [card_range] using card_le_card hsub
  rw [outerCarrier_card]
  exact Nat.mul_le_mul hq (Nat.mul_le_mul hd hm)

theorem blockSource_norm_sq_le_physical_MY_dispersion
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hg : ∀ q ∈ factorCarrier atom.Q1, ‖atom.gamma1 q‖ ≤ 1)
    (hb : ∀ m ∈ atom.betaCarrier, ‖atom.beta m‖ ≤ 1) :
    ‖blockSource atom z y k‖ ^ 2 ≤
      (((Nat.floor (2 * atom.Q1) + 1) *
        (2 ^ (k.d + 1) * (Nat.floor (2 * atom.V) + 1)) : ℕ) : ℝ) *
      (dispersionW atom z y k - 2 * dispersionV atom z y k + dispersionU atom z y k) := by
  have hnonneg : 0 ≤
      dispersionW atom z y k - 2 * dispersionV atom z y k + dispersionU atom z y k := by
    rw [← preliminary_dispersion_identity]
    exact sum_nonneg fun _ _ => sq_nonneg _
  have hcard : ((outerCarrier atom k).card : ℝ) ≤
      (((Nat.floor (2 * atom.Q1) + 1) *
        (2 ^ (k.d + 1) * (Nat.floor (2 * atom.V) + 1)) : ℕ) : ℝ) := by
    exact_mod_cast outerCarrier_card_le_physical_lengths atom k
  exact (blockSource_norm_sq_le_card_mul_dispersion atom z y k hg hb).trans
    (mul_le_mul_of_nonneg_right hcard hnonneg)

end
end ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
