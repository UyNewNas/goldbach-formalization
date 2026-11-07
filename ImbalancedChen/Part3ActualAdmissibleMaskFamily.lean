import ImbalancedChen.Part3ActualSignedKernelMask

/-!
SOURCEONLY / UNCOMPILED / NOT ACCEPTED -- 20261024z P3 continuation 3.
ASSEMBLY: append this entire declaration fragment AFTER the complete
Part3ActualSignedKernelMask.lean.txt, SHA256
2f5871d60bca3da68cc5dbb174663773951c981f7e987073853c8d1c2fcf94c2.
Its real imports provide DistributionTargets and Mathlib.Tactic. This file
does not import a nonexistent module named after a source-text candidate.

The actual MediumAdmissible conjunction is proved, including all three
nonzero-to-coprime gates. UniformAuxiliarySW is definitionally unchanged:
it uses alpha, its original interval, U and scale, and no gamma field.
There is no RestrictedMediumTarget/Obligation premise or conclusion here.
-/

namespace ImbalancedChen.Part3.ActualAdmissibleMaskFamily_20261024z
noncomputable section
open Classical
open scoped BigOperators
open ActualSignedKernelMask_20261024z (withGamma1Mask)

def withGamma2Mask (d : MediumAtom) (mask : ℕ → ℂ) : MediumAtom :=
  { d with gamma2 := fun q => d.gamma2 q * mask q }

def withGamma3Mask (d : MediumAtom) (mask : ℕ → ℂ) : MediumAtom :=
  { d with gamma3 := fun q => d.gamma3 q * mask q }

/-- The only changed admissibility clauses: a genuine norm contraction and
the old nonzero support gate, recovered from nonzero of the product. -/
private theorem masked_gamma_gate (q a : ℕ) (gamma mask : ℂ)
    (hg : ‖gamma‖ ≤ 1 ∧ (gamma ≠ 0 → Nat.Coprime q a))
    (hm : ‖mask‖ ≤ 1) :
    ‖gamma*mask‖ ≤ 1 ∧ (gamma*mask ≠ 0 → Nat.Coprime q a) := by
  constructor
  · rw [norm_mul]
    exact (mul_le_mul hg.1 hm (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro hprod
    apply hg.2
    intro hz
    apply hprod
    simp only [hz, zero_mul]

theorem mediumAdmissible_withGamma1Mask
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom} (mask : ℕ → ℂ)
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hm : ∀ q ∈ factorCarrier d.Q1, ‖mask q‖ ≤ 1) :
    MediumAdmissible B sigma kappa c0 (withGamma1Mask d mask) := by
  rcases hd with ⟨hU, hV, hQ1, hQ2, hQ3, hlog, hlo, hhi, hI, hII,
    hIII, hIV, ha, harough, hb, hg1, hg2, hg3⟩
  dsimp only [MediumAdmissible, withGamma1Mask]
  refine ⟨hU, hV, hQ1, hQ2, hQ3, hlog, hlo, hhi, hI, hII,
    hIII, hIV, ha, harough, hb, ?_, hg2, hg3⟩
  intro q hq
  exact masked_gamma_gate q d.residue.natAbs (d.gamma1 q) (mask q) (hg1 q hq) (hm q hq)

theorem mediumAdmissible_withGamma2Mask
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom} (mask : ℕ → ℂ)
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hm : ∀ q ∈ factorCarrier d.Q2, ‖mask q‖ ≤ 1) :
    MediumAdmissible B sigma kappa c0 (withGamma2Mask d mask) := by
  rcases hd with ⟨hU, hV, hQ1, hQ2, hQ3, hlog, hlo, hhi, hI, hII,
    hIII, hIV, ha, harough, hb, hg1, hg2, hg3⟩
  dsimp only [MediumAdmissible, withGamma2Mask]
  refine ⟨hU, hV, hQ1, hQ2, hQ3, hlog, hlo, hhi, hI, hII,
    hIII, hIV, ha, harough, hb, hg1, ?_, hg3⟩
  intro q hq
  exact masked_gamma_gate q d.residue.natAbs (d.gamma2 q) (mask q) (hg2 q hq) (hm q hq)

theorem mediumAdmissible_withGamma3Mask
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom} (mask : ℕ → ℂ)
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hm : ∀ q ∈ factorCarrier d.Q3, ‖mask q‖ ≤ 1) :
    MediumAdmissible B sigma kappa c0 (withGamma3Mask d mask) := by
  rcases hd with ⟨hU, hV, hQ1, hQ2, hQ3, hlog, hlo, hhi, hI, hII,
    hIII, hIV, ha, harough, hb, hg1, hg2, hg3⟩
  dsimp only [MediumAdmissible, withGamma3Mask]
  refine ⟨hU, hV, hQ1, hQ2, hQ3, hlog, hlo, hhi, hI, hII,
    hIII, hIV, ha, harough, hb, hg1, hg2, ?_⟩
  intro q hq
  exact masked_gamma_gate q d.residue.natAbs (d.gamma3 q) (mask q) (hg3 q hq) (hm q hq)

def withAllGammaMasks (d : MediumAtom) (mask1 mask2 mask3 : ℕ → ℂ) : MediumAtom :=
  withGamma3Mask (withGamma2Mask (withGamma1Mask d mask1) mask2) mask3

theorem mediumAdmissible_withAllGammaMasks
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (mask1 mask2 mask3 : ℕ → ℂ)
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hm1 : ∀ q ∈ factorCarrier d.Q1, ‖mask1 q‖ ≤ 1)
    (hm2 : ∀ q ∈ factorCarrier d.Q2, ‖mask2 q‖ ≤ 1)
    (hm3 : ∀ q ∈ factorCarrier d.Q3, ‖mask3 q‖ ≤ 1) :
    MediumAdmissible B sigma kappa c0 (withAllGammaMasks d mask1 mask2 mask3) := by
  exact mediumAdmissible_withGamma3Mask mask3
    (mediumAdmissible_withGamma2Mask mask2
      (mediumAdmissible_withGamma1Mask mask1 hd hm1) hm2) hm3

theorem withAllGammaMasks_original_data (d : MediumAtom) (mask1 mask2 mask3 : ℕ → ℂ) :
    (withAllGammaMasks d mask1 mask2 mask3).residue = d.residue ∧
      (withAllGammaMasks d mask1 mask2 mask3).alpha = d.alpha ∧
      (withAllGammaMasks d mask1 mask2 mask3).beta = d.beta ∧
      (withAllGammaMasks d mask1 mask2 mask3).alphaCarrier = d.alphaCarrier ∧
      (withAllGammaMasks d mask1 mask2 mask3).betaCarrier = d.betaCarrier ∧
      (withAllGammaMasks d mask1 mask2 mask3).Q1 = d.Q1 ∧
      (withAllGammaMasks d mask1 mask2 mask3).Q2 = d.Q2 ∧
      (withAllGammaMasks d mask1 mask2 mask3).Q3 = d.Q3 ∧
      (withAllGammaMasks d mask1 mask2 mask3).intervalLo = d.intervalLo ∧
      (withAllGammaMasks d mask1 mask2 mask3).intervalHi = d.intervalHi ∧
      (withAllGammaMasks d mask1 mask2 mask3).U = d.U ∧
      (withAllGammaMasks d mask1 mask2 mask3).V = d.V ∧
      (withAllGammaMasks d mask1 mask2 mask3).scale = d.scale := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem withAllGammaMasks_discrepancy (d : MediumAtom) (mask1 mask2 mask3 : ℕ → ℂ)
    (q : ℕ) :
    (withAllGammaMasks d mask1 mask2 mask3).discrepancy q = d.discrepancy q := by
  rfl

theorem withAllGammaMasks_auxSWError (d : MediumAtom) (mask1 mask2 mask3 : ℕ → ℂ)
    (k q b : ℕ) :
    (withAllGammaMasks d mask1 mask2 mask3).auxSWError k q b = d.auxSWError k q b := by
  rfl

/-- Original signed discrepancy and all three independent factor masks. -/
theorem withAllGammaMasks_signedError (d : MediumAtom) (mask1 mask2 mask3 : ℕ → ℂ) :
    (withAllGammaMasks d mask1 mask2 mask3).signedError =
      ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
        ∑ q3 ∈ factorCarrier d.Q3,
          d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 *
            (mask1 q1 * mask2 q2 * mask3 q3) * d.discrepancy (q1*q2*q3) := by
  unfold MediumAtom.signedError
  apply Finset.sum_congr rfl
  intro q1 _hq1
  apply Finset.sum_congr rfl
  intro q2 _hq2
  apply Finset.sum_congr rfl
  intro q3 _hq3
  change (d.gamma1 q1 * mask1 q1) * (d.gamma2 q2 * mask2 q2) *
    (d.gamma3 q3 * mask3 q3) * d.discrepancy (q1*q2*q3) = _
  ring

variable {ι : Type*}

/-- No mask norm assumption is needed: the entire SW proposition is the
same one, with its original order of all constants and quantifiers. -/
theorem uniformAuxiliarySW_withGamma1Mask_iff (F : ι → MediumAtom)
    (mask : ι → ℕ → ℂ) (C0 : ℕ) :
    UniformAuxiliarySW (fun i => withGamma1Mask (F i) (mask i)) C0 ↔
      UniformAuxiliarySW F C0 := by
  rfl

theorem uniformAuxiliarySW_withGamma2Mask_iff (F : ι → MediumAtom)
    (mask : ι → ℕ → ℂ) (C0 : ℕ) :
    UniformAuxiliarySW (fun i => withGamma2Mask (F i) (mask i)) C0 ↔
      UniformAuxiliarySW F C0 := by
  rfl

theorem uniformAuxiliarySW_withGamma3Mask_iff (F : ι → MediumAtom)
    (mask : ι → ℕ → ℂ) (C0 : ℕ) :
    UniformAuxiliarySW (fun i => withGamma3Mask (F i) (mask i)) C0 ↔
      UniformAuxiliarySW F C0 := by
  rfl

theorem uniformAuxiliarySW_withAllGammaMasks_iff (F : ι → MediumAtom)
    (mask1 mask2 mask3 : ι → ℕ → ℂ) (C0 : ℕ) :
    UniformAuxiliarySW
      (fun i => withAllGammaMasks (F i) (mask1 i) (mask2 i) (mask3 i)) C0 ↔
        UniformAuxiliarySW F C0 := by
  rfl

/-- Simultaneous actual input supplier for a whole masked family. This
stops at admissibility and SW, without assuming a distribution target. -/
theorem maskedFamily_actual_inputs
    (B C0 : ℕ) (sigma kappa c0 : ℝ) (F : ι → MediumAtom)
    (mask1 mask2 mask3 : ι → ℕ → ℂ)
    (hF : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hm1 : ∀ i, ∀ q ∈ factorCarrier (F i).Q1, ‖mask1 i q‖ ≤ 1)
    (hm2 : ∀ i, ∀ q ∈ factorCarrier (F i).Q2, ‖mask2 i q‖ ≤ 1)
    (hm3 : ∀ i, ∀ q ∈ factorCarrier (F i).Q3, ‖mask3 i q‖ ≤ 1)
    (hSW : UniformAuxiliarySW F C0) :
    (∀ i, MediumAdmissible B sigma kappa c0
      (withAllGammaMasks (F i) (mask1 i) (mask2 i) (mask3 i))) ∧
      UniformAuxiliarySW
        (fun i => withAllGammaMasks (F i) (mask1 i) (mask2 i) (mask3 i)) C0 := by
  constructor
  · intro i
    exact mediumAdmissible_withAllGammaMasks (mask1 i) (mask2 i) (mask3 i)
      (hF i) (hm1 i) (hm2 i) (hm3 i)
  · exact (uniformAuxiliarySW_withAllGammaMasks_iff F mask1 mask2 mask3 C0).mpr hSW

/-- Both pieces of a genuine 0/1 first-factor partition remain admissible. -/
theorem mediumAdmissible_gamma1_indicator_and_complement
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (M : Finset ℕ) :
    MediumAdmissible B sigma kappa c0
      (withGamma1Mask d ((M : Set ℕ).indicator (fun _ => (1 : ℂ)))) ∧
    MediumAdmissible B sigma kappa c0
      (withGamma1Mask d (fun q => 1-(M : Set ℕ).indicator (fun _ => (1 : ℂ)) q)) := by
  constructor
  · apply mediumAdmissible_withGamma1Mask _ hd
    intro q _hq
    by_cases hq : q ∈ M <;> simp [hq]
  · apply mediumAdmissible_withGamma1Mask _ hd
    intro q _hq
    by_cases hq : q ∈ M <;> simp [hq]

/-- The two real [0,1] weights used in a soft partition are both legal. -/
theorem mediumAdmissible_gamma1_real_and_complement
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (w : ℕ → ℝ)
    (hw : ∀ q ∈ factorCarrier d.Q1, 0 ≤ w q ∧ w q ≤ 1) :
    MediumAdmissible B sigma kappa c0
      (withGamma1Mask d (fun q => (w q : ℂ))) ∧
    MediumAdmissible B sigma kappa c0
      (withGamma1Mask d (fun q => ((1-w q : ℝ) : ℂ))) := by
  constructor
  · apply mediumAdmissible_withGamma1Mask _ hd
    intro q hq
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw q hq).1]
    exact (hw q hq).2
  · apply mediumAdmissible_withGamma1Mask _ hd
    intro q hq
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hw q hq).2)]
    have h := (hw q hq).1
    linarith

end
end ImbalancedChen.Part3.ActualAdmissibleMaskFamily_20261024z
