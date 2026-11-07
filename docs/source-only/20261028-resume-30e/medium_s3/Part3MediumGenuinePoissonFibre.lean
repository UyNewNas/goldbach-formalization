import ImbalancedChen.Part3MediumLiteralS3Stages
import Mathlib.Tactic

/-! Source only; uncompiled; zero formal credit.
Genuine same-d restored S3 m-fibre, its constructed physical CRT residue,
complete lcm and actual paperPsi zero/nonzero Fourier packet. Primitive
moduli are DERIVED from original gamma support and nonzero lambdaTrim.
No clean-lcm simplification, finite-h cutoff or spectral bound is assumed.
-/
namespace ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028
noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumLiteralS3Deleted20261028
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3.OriginalGevreyActualPsiFourierIBP20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalGevreySharedRowDictionary20261028
open ImbalancedChen.Part3.OriginalPhysicalPoissonTruncation20261028

abbrev FibreIndex := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))

def fibreCarrier (atom : MediumAtom) (k : Key) : Finset FibreIndex :=
  ((paperPsiNaturalCarrier atom.Q1).filter (fun q => q.Coprime atom.residue.natAbs) ×ˢ
    dyadicWindow k.d) ×ˢ (innerCarrier atom k ×ˢ innerCarrier atom k)

def lift (v : FibreIndex) (m : ℕ) : PairIndex := ((v.1.1, v.1.2, m), v.2)

def leftModulus (v : FibreIndex) : ℕ := (v.1.1 * v.1.2) * v.2.1.1

def rightModulus (v : FibreIndex) : ℕ := (v.1.1 * v.1.2) * v.2.2.1

def completeL (v : FibreIndex) : ℕ := (leftModulus v).lcm (rightModulus v)

def constructedResidue (atom : MediumAtom) (v : FibreIndex) : ℤ :=
  ComplexCRT.residue (leftModulus v) (rightModulus v) v.2.1.2 v.2.2.2 atom.residue

def compatible (v : FibreIndex) : Prop :=
  ComplexCRT.Compatible (leftModulus v) (rightModulus v) v.2.1.2 v.2.2.2

def headCoefficient (atom : MediumAtom) (z y : ℝ) (k : Key) (v : FibreIndex) : ℂ :=
  (paperQWeight atom v.1.1 : ℂ) * lambdaTrim atom z y k v.1.2 v.2.1.1 *
    star (lambdaTrim atom z y k v.1.2 v.2.2.1) *
    atom.alpha v.2.1.2 * star (atom.alpha v.2.2.2)

def restoredFibre (atom : MediumAtom) (z y : ℝ) (k : Key) (v : FibreIndex) : ℂ :=
  ∑ m ∈ paperPsiNaturalCarrier atom.V, S3FullTerm atom z y k (lift v m)

private theorem fullIndicator_eq_modEq (a : ℤ) (L n m : ℕ) :
    fullIndicator a L n m = if Int.ModEq L ((m : ℤ) * n) a then 1 else 0 := by
  have hp : ((n * m : ℕ) : ℤ) = (m : ℤ) * n := by push_cast; ring
  simp only [fullIndicator, Int.ModEq, hp]

/-- Literal pre-Poisson source identity, including both independent rough
and alpha labels and the same q,d. The m weight is actual paperMWeight. -/
theorem restoredFibre_eq_productProgression (atom : MediumAtom) (z y : ℝ)
    (k : Key) (v : FibreIndex) :
    restoredFibre atom z y k v = headCoefficient atom z y k v *
      (ComplexCRT.productProgressionWeight (paperPsiNaturalCarrier atom.V)
        (paperMWeight atom) atom.residue (leftModulus v) (rightModulus v)
        v.2.1.2 v.2.2.2 : ℂ) := by
  unfold restoredFibre ComplexCRT.productProgressionWeight
  rw [Complex.ofReal_sum, mul_sum]
  apply sum_congr rfl
  intro m hm
  unfold S3FullTerm pairCoefficient jointPsi lift oldIndex headCoefficient leftModulus rightModulus
  rw [fullIndicator_eq_modEq, fullIndicator_eq_modEq]
  by_cases h1 : Int.ModEq ((v.1.1 * v.1.2) * v.2.1.1)
      ((m : ℤ) * v.2.1.2) atom.residue <;>
    by_cases h2 : Int.ModEq ((v.1.1 * v.1.2) * v.2.2.1)
      ((m : ℤ) * v.2.2.2) atom.residue <;>
      simp [h1, h2, Complex.ofReal_mul] <;> ring

private theorem dyadic_member_pos {k n : ℕ} (hn : n ∈ dyadicWindow k) : 0 < n :=
  (pow_pos (by norm_num : (0 : ℕ) < 2) k).trans_le (mem_Ico.mp hn).1

theorem fibre_moduli_positive {atom : MediumAtom} {k : Key} (hQ : 0 < atom.Q1)
    {v : FibreIndex} (hv : v ∈ fibreCarrier atom k) :
    0 < leftModulus v ∧ 0 < rightModulus v ∧ 0 < completeL v := by
  obtain ⟨hqd, hij⟩ := mem_product.mp hv
  obtain ⟨hq, hd⟩ := mem_product.mp hqd
  have hqN := (mem_filter.mp hq).1
  have hqLo := (mem_Icc.mp hqN).1
  have hqReal : (0 : ℝ) < Nat.ceil (atom.Q1 / 2) :=
    lt_of_lt_of_le (by linarith) (Nat.le_ceil _)
  have hqPos : 0 < v.1.1 := (by exact_mod_cast hqReal : 0 < Nat.ceil (atom.Q1 / 2)).trans_le hqLo
  obtain ⟨hi, hj⟩ := mem_product.mp hij
  have hr := dyadic_member_pos (mem_product.mp hi).1
  have hs := dyadic_member_pos (mem_product.mp hj).1
  have hqdPos := mul_pos hqPos (dyadic_member_pos hd)
  have hL := mul_pos hqdPos hr
  have hR := mul_pos hqdPos hs
  exact ⟨hL, hR, Nat.lcm_pos hL hR⟩

/-- Primitive physical moduli follow from the actual gamma/choice gates.
The statement does not assert every preliminary d or rough index active. -/
theorem active_fibre_moduli_primitive
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (z y : ℝ) (k : Key) {v : FibreIndex} (hv : v ∈ fibreCarrier atom k)
    (hr : lambdaTrim atom z y k v.1.2 v.2.1.1 ≠ 0)
    (hs : lambdaTrim atom z y k v.1.2 v.2.2.1 ≠ 0) :
    Int.gcd atom.residue (leftModulus v) = 1 ∧
      Int.gcd atom.residue (rightModulus v) = 1 := by
  have hq := (mem_filter.mp (mem_product.mp (mem_product.mp hv).1).1).2
  have hdr := lambdaTrim_support_residue_product hA z y k v.1.2 v.2.1.1 hr
  have hds := lambdaTrim_support_residue_product hA z y k v.1.2 v.2.2.1 hs
  have hL : (leftModulus v).Coprime atom.residue.natAbs := by
    simpa only [leftModulus, Nat.mul_assoc] using Nat.coprime_mul_iff_left.mpr ⟨hq, hdr⟩
  have hR : (rightModulus v).Coprime atom.residue.natAbs := by
    simpa only [rightModulus, Nat.mul_assoc] using Nat.coprime_mul_iff_left.mpr ⟨hq, hds⟩
  constructor
  · simpa only [Int.gcd, Int.natAbs_natCast, Nat.gcd_comm] using hL.gcd_eq_one
  · simpa only [Int.gcd, Int.natAbs_natCast, Nat.gcd_comm] using hR.gcd_eq_one

def zeroMode (atom : MediumAtom) (v : FibreIndex) : ℂ :=
  if compatible v then (atom.V / (completeL v : ℝ)) • (𝓕 paperPsiComplex) 0 else 0

def nonzeroModes (atom : MediumAtom) (v : FibreIndex) : ℂ :=
  if compatible v then ∑' h : ℤ,
    paperPsiNonzeroMode (atom.V / (completeL v : ℝ))
      ((constructedResidue atom v : ℝ) / completeL v) h else 0

/-- Genuine constructed CRT and actual paperPsi Poisson summand, with
zero mode and BOTH signed frequency directions. No lcm is replaced by
a product until a later clean-gate theorem proves that replacement. -/
theorem active_restoredFibre_eq_genuine_Poisson
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (z y : ℝ) (k : Key) {v : FibreIndex} (hv : v ∈ fibreCarrier atom k)
    (hr : lambdaTrim atom z y k v.1.2 v.2.1.1 ≠ 0)
    (hs : lambdaTrim atom z y k v.1.2 v.2.2.1 ≠ 0) :
    restoredFibre atom z y k v = headCoefficient atom z y k v *
      (zeroMode atom v + nonzeroModes atom v) := by
  have hQ : 0 < atom.Q1 := zero_lt_one.trans_le hA.2.2.1
  have hM : 0 < atom.V := zero_lt_one.trans_le hA.2.1
  obtain ⟨hL, hR, hLCM⟩ := fibre_moduli_positive hQ hv
  obtain ⟨haL, haR⟩ := active_fibre_moduli_primitive hA z y k hv hr hs
  rw [restoredFibre_eq_productProgression,
    ComplexCRT.productProgressionWeight_eq_constructed _ _ hL haL haR]
  unfold ComplexCRT.constructedProgressionWeight zeroMode nonzeroModes
  by_cases hc : compatible v
  · simp only [compatible] at hc
    simp only [compatible, if_pos hc]
    have hfinite :
        ((∑ m ∈ paperPsiNaturalCarrier atom.V,
          if Int.ModEq (completeL v) (m : ℤ) (constructedResidue atom v)
            then paperMWeight atom m else 0 : ℝ) : ℂ) =
        ∑ m ∈ paperPsiNaturalCarrier atom.V,
          if Int.ModEq (completeL v) (m : ℤ) (constructedResidue atom v)
            then scaledPaperPsi atom.V m else 0 := by
      simp [paperMWeight, scaledPaperPsi, paperPsiComplex, Complex.ofReal_sum]
    rw [show (leftModulus v).lcm (rightModulus v) = completeL v from rfl]
    change headCoefficient atom z y k v *
      ((∑ m ∈ paperPsiNaturalCarrier atom.V,
        if Int.ModEq (completeL v) (m : ℤ) (constructedResidue atom v)
          then paperMWeight atom m else 0 : ℝ) : ℂ) = _
    rw [hfinite, paperPsi_finite_residue_poisson_packet hM hLCM]
  · have hc' : ¬ComplexCRT.Compatible (leftModulus v) (rightModulus v) v.2.1.2 v.2.2.2 := hc
    simp [hc, hc', compatible]

/-- Zero lambda fibres are genuinely zero, so the active-source theorem
extends to EVERY original fibre without an active-support hypothesis. -/
theorem restoredFibre_eq_genuine_Poisson
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (z y : ℝ) (k : Key) {v : FibreIndex} (hv : v ∈ fibreCarrier atom k) :
    restoredFibre atom z y k v = headCoefficient atom z y k v *
      (zeroMode atom v + nonzeroModes atom v) := by
  by_cases hr : lambdaTrim atom z y k v.1.2 v.2.1.1 = 0
  · rw [restoredFibre_eq_productProgression]
    simp [headCoefficient, hr]
  by_cases hs : lambdaTrim atom z y k v.1.2 v.2.2.1 = 0
  · rw [restoredFibre_eq_productProgression]
    simp [headCoefficient, hs]
  exact active_restoredFibre_eq_genuine_Poisson hA z y k hv hr hs

/-- Exact carrier dictionary for lifting a fixed same-d pair and its
common smoothing variable. The primitive q gate is not omitted. -/
theorem lift_mem_paired_iff (atom : MediumAtom) (k : Key) (v : FibreIndex) (m : ℕ) :
    lift v m ∈ pairedCarrier atom k ↔
      v ∈ fibreCarrier atom k ∧ m ∈ paperPsiNaturalCarrier atom.V := by
  simp only [lift, pairedCarrier, fibreCarrier, primitiveSmoothOuter,
    smoothOuterCarrier, mem_product, mem_filter]
  tauto

def retainedModes (atom : MediumAtom) (H : ℕ) (v : FibreIndex) : ℂ :=
  if compatible v then ∑ h ∈ signedWindow H,
    paperPsiNonzeroMode (atom.V / (completeL v : ℝ))
      ((constructedResidue atom v : ℝ) / completeL v) h else 0

def omittedModes (atom : MediumAtom) (H : ℕ) (v : FibreIndex) : ℂ :=
  if compatible v then
    finitePacketError atom.V (completeL v) (constructedResidue atom v) H else 0

/-- Finite h is a real source packet with its actual omitted series;
H remains an explicit caller integer, never a replacement modulus. -/
theorem nonzeroModes_eq_retained_add_omitted {atom : MediumAtom} {k : Key}
    (hQ : 0 < atom.Q1) (hM : 0 < atom.V) {v : FibreIndex}
    (hv : v ∈ fibreCarrier atom k) (H : ℕ) :
    nonzeroModes atom v = retainedModes atom H v + omittedModes atom H v := by
  unfold nonzeroModes retainedModes omittedModes
  by_cases hc : compatible v
  · simp only [if_pos hc]
    have hL := (fibre_moduli_positive hQ hv).2.2
    rw [finitePacketError_eq_omitted hM hL]
    have he := nonzero_packet_truncation_identity
      (div_pos hM (show (0 : ℝ) < completeL v by exact_mod_cast hL)) H
      ((constructedResidue atom v : ℝ) / completeL v)
    linear_combination he
  · simp [hc]

/-- The genuine finite-H Poisson source, with its zero mode and signed
error. Nothing declares the zero term to cancel in S1-2Re(S2)+S3. -/
theorem restoredFibre_eq_zero_retained_error
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (z y : ℝ) (k : Key) {v : FibreIndex} (hv : v ∈ fibreCarrier atom k) (H : ℕ) :
    restoredFibre atom z y k v = headCoefficient atom z y k v *
      (zeroMode atom v + retainedModes atom H v + omittedModes atom H v) := by
  rw [restoredFibre_eq_genuine_Poisson hA z y k hv,
    nonzeroModes_eq_retained_add_omitted (zero_lt_one.trans_le hA.2.2.1)
      (zero_lt_one.trans_le hA.2.1) hv H]
  ring

def fibreOf (t : PairIndex) : FibreIndex := ((t.1.1, t.1.2.1), t.2)

@[simp] theorem lift_fibreOf (t : PairIndex) : lift (fibreOf t) t.1.2.2 = t := by
  rcases t with ⟨⟨q, d, m⟩, ij⟩
  rfl

/-- Actual carrier bijection: the common m is moved to the innermost
sum while q,d and both independent (r,n) labels remain unchanged. -/
theorem sum_paired_eq_fibres (atom : MediumAtom) (k : Key) (F : PairIndex → ℂ) :
    (∑ t ∈ pairedCarrier atom k, F t) =
      ∑ v ∈ fibreCarrier atom k, ∑ m ∈ paperPsiNaturalCarrier atom.V, F (lift v m) := by
  calc
    _ = ∑ vm ∈ fibreCarrier atom k ×ˢ paperPsiNaturalCarrier atom.V,
        F (lift vm.1 vm.2) := by
      apply sum_bij (fun t ht => (fibreOf t, t.1.2.2))
      · intro t ht
        apply mem_product.mpr
        apply (lift_mem_paired_iff atom k (fibreOf t) t.1.2.2).mp
        simpa only [lift_fibreOf] using ht
      · intro t ht t' ht' heq
        have he := congrArg (fun vm : FibreIndex × ℕ => lift vm.1 vm.2) heq
        simpa only [lift_fibreOf] using he
      · intro vm hvm
        obtain ⟨hv, hm⟩ := mem_product.mp hvm
        refine ⟨lift vm.1 vm.2, (lift_mem_paired_iff atom k vm.1 vm.2).mpr ⟨hv, hm⟩, ?_⟩
        rfl
      · intro t ht
        simp only [lift_fibreOf]
    _ = _ := by rw [sum_product]

/-- Exact OFF-DIAGONAL restored source passed to Poisson. In particular
it is not the whole original square with its diagonal silently omitted. -/
theorem offDiagonal_full_eq_restored_fibres (atom : MediumAtom) (z y : ℝ) (k : Key) :
    (∑ t ∈ offDiagonalCarrier atom k, S3FullTerm atom z y k t) =
      ∑ v ∈ fibreCarrier atom k,
        if v.2.1.2 ≠ v.2.2.2 then restoredFibre atom z y k v else 0 := by
  unfold offDiagonalCarrier
  rw [sum_filter, sum_paired_eq_fibres]
  apply sum_congr rfl
  intro v hv
  by_cases h : v.2.1.2 ≠ v.2.2.2 <;>
    simp [oldIndex, lift, restoredFibre, h]

/-- Genuine Poisson export for the SAME common-d source, allowing the
later physical caller to choose H(v). The zero mode and signed omitted
series remain separate, so no principal variance is cancelled by fiat. -/
theorem offDiagonal_Poisson_source_identity
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (z y : ℝ) (k : Key) (H : FibreIndex → ℕ) :
    (∑ t ∈ offDiagonalCarrier atom k, S3FullTerm atom z y k t) =
      ∑ v ∈ fibreCarrier atom k, if v.2.1.2 ≠ v.2.2.2 then
        headCoefficient atom z y k v *
          (zeroMode atom v + retainedModes atom (H v) v + omittedModes atom (H v) v)
        else 0 := by
  rw [offDiagonal_full_eq_restored_fibres]
  apply sum_congr rfl
  intro v hv
  by_cases h : v.2.1.2 ≠ v.2.2.2
  · rw [if_pos h, if_pos h, restoredFibre_eq_zero_retained_error hA z y k hv (H v)]
  · simp [h]

end
end ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028
