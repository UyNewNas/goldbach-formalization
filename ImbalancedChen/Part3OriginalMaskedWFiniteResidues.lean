import ImbalancedChen.Part3OriginalBothSmallMaskedW
import ImbalancedChen.Part3ComplexCRTFiniteFourier
import ImbalancedChen.Part3KloostermanCompleteSecondMoment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 2.

An upstream source bridge for ORIGINAL masked W. At a fixed original
factor pair, beta pairs are pushed onto their actual CRT residue, with
the same beta gcd mask and compatibility gate. The whole-W identity
retains the factor gcd mask, both complex gammas, all factor labels and
the single original common S,w. Finite Fourier inversion uses the exact
finite smoothing transform, not a substituted Schwartz amplitude and
not the downstream completed-square coefficient from phase 1.
-/

namespace ImbalancedChen.Part3.OriginalMaskedWFiniteResidues20261026b
noncomputable section
open Classical Finset OriginalBothSmallMaskedW20261026b
open scoped BigOperators

def progression (d : MediumAtom) (L : ℕ) (b : ℤ) : ℂ :=
  ((∑ n ∈ d.commonSmoothCarrier,
    if Int.ModEq L (n : ℤ) b then d.commonSmoothWeight n else 0 : ℝ) : ℂ)

def originalPair (d : MediumAtom) (Y : ℝ) (q r : ℕ) : ℂ :=
  ∑ n1 ∈ d.betaCarrier, ∑ n2 ∈ d.betaCarrier,
    if Y < (n1.gcd n2 : ℝ) then 0 else
      d.beta n1 * star (d.beta n2) *
        (ComplexCRT.constructedProgressionWeight d.commonSmoothCarrier d.commonSmoothWeight
          d.residue q r n1 n2 : ℂ)

def residueCoefficient (d : MediumAtom) (Y : ℝ) (q r : ℕ)
    [NeZero (q.lcm r)] (v : ZMod (q.lcm r)) : ℂ :=
  ∑ n1 ∈ d.betaCarrier, ∑ n2 ∈ d.betaCarrier,
    if Y < (n1.gcd n2 : ℝ) then 0 else
      if ComplexCRT.Compatible q r n1 n2 ∧
          (ComplexCRT.residue q r n1 n2 d.residue : ZMod (q.lcm r)) = v then
        d.beta n1 * star (d.beta n2) else 0

/-- Actual signed beta-pair transform, fixed before taking any norm. -/
def additiveCoefficient (d : MediumAtom) (Y : ℝ) (q r : ℕ)
    [NeZero (q.lcm r)] (h : ZMod (q.lcm r)) : ℂ :=
  ∑ v : ZMod (q.lcm r), residueCoefficient d Y q r v * ZMod.stdAddChar (-h*v)

private theorem progression_cast (d : MediumAtom) (L : ℕ) [NeZero L] (b : ℤ) :
    progression d L (((b : ZMod L).val : ℕ) : ℤ) = progression d L b := by
  have he : Int.ModEq L (((b : ZMod L).val : ℕ) : ℤ) b := by
    apply (ZMod.intCast_eq_intCast_iff _ _ L).mp
    simp
  unfold progression
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hh : Int.ModEq L (n : ℤ) (((b : ZMod L).val : ℕ) : ℤ) ↔
      Int.ModEq L (n : ℤ) b := ⟨fun h => h.trans he, fun h => h.trans he.symm⟩
  rw [hh]

theorem originalPair_eq_residue_source (d : MediumAtom) (Y : ℝ) (q r : ℕ)
    [NeZero (q.lcm r)] :
    originalPair d Y q r = ∑ v : ZMod (q.lcm r),
      residueCoefficient d Y q r v * progression d (q.lcm r) (v.val : ℤ) := by
  unfold residueCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold originalPair
  apply Finset.sum_congr rfl
  intro n1 hn1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n2 hn2
  by_cases hy : Y < (n1.gcd n2 : ℝ)
  · simp [hy]
  · simp only [if_neg hy]
    unfold ComplexCRT.constructedProgressionWeight
    by_cases hc : ComplexCRT.Compatible q r n1 n2
    · simp only [hc, true_and, if_true, ite_mul, zero_mul]
      rw [Finset.sum_eq_single (ComplexCRT.residue q r n1 n2 d.residue : ZMod (q.lcm r))]
      · simp only [if_pos rfl, progression_cast]
        rfl
      · intro v hv hne
        exact if_neg (Ne.symm hne)
      · simp
    · simp [hc]

/-- The physical finite smoothing transform, with every frequency modulo
the COMPLETE lcm. There is no incomplete-to-complete replacement. -/
theorem originalPair_eq_full_finiteFourier (d : MediumAtom) (Y : ℝ) (q r : ℕ)
    [NeZero (q.lcm r)] :
    originalPair d Y q r = (q.lcm r : ℂ)⁻¹ *
      ∑ h : ZMod (q.lcm r), additiveCoefficient d Y q r h *
        finiteSourceAdditiveFourier d.commonSmoothCarrier d.commonSmoothWeight (q.lcm r) h := by
  rw [originalPair_eq_residue_source]
  unfold progression additiveCoefficient
  simp_rw [finiteProgressionWeight_eq_fullFourier]
  simp only [Finset.mul_sum, Finset.sum_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- True complete second moment of the ORIGINAL signed pair transform.
All CRT-residue collisions stay inside the squared source coefficient.
No individual-frequency or spectral estimate is extracted from Parseval. -/
theorem original_signed_coefficient_complete_energy
    (d : MediumAtom) (Y : ℝ) (q r : ℕ) [NeZero (q.lcm r)] :
    (∑ h : ZMod (q.lcm r), ‖additiveCoefficient d Y q r h‖^2) =
      (q.lcm r : ℝ) * ∑ v : ZMod (q.lcm r), ‖residueCoefficient d Y q r v‖^2 := by
  calc
    _ = ∑ h : ZMod (q.lcm r),
        ‖∑ v : ZMod (q.lcm r), residueCoefficient d Y q r v * ZMod.stdAddChar (h*v)‖^2 := by
      unfold additiveCoefficient
      apply Finset.sum_bij (fun h _ => -h)
      · intro h hh
        exact Finset.mem_univ _
      · intro h hh h' hh' heq
        exact neg_injective heq
      · intro h hh
        exact ⟨-h, Finset.mem_univ _, neg_neg h⟩
      · intro h hh
        rfl
    _ = _ := OriginalSmoothPoissonTail.CompleteSecondMomentSourceOnly.complete_additive_energy
      (q.lcm r) (residueCoefficient d Y q r)

private theorem ite_zero_sum {α : Type*} (p : Prop) (S : Finset α) (f : α → ℂ) :
    (if p then 0 else ∑ a ∈ S, f a) = ∑ a ∈ S, if p then 0 else f a := by
  classical
  by_cases hp : p <;> simp [hp]

/-- Exact regrouping of ORIGINAL both-small W by its ORIGINAL factor pair.
There is no assertion that a factor coefficient is independent of q,r. -/
theorem original_maskedW_factor_source (d : MediumAtom) (Y D : ℝ) :
    wholeW d Y D =
      ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
        d.complexFactorGamma a * star (d.complexFactorGamma b) *
          (if D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) then 0 else
            originalPair d Y (complexFactorModulus a) (complexFactorModulus b)) := by
  unfold wholeW factorPairW originalPair
  simp_rw [Finset.mul_sum, ite_zero_sum]
  simp_rw [Finset.sum_comm (s := d.betaCarrier) (t := d.complexFactorLabels)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro n1 hn1
  apply Finset.sum_congr rfl
  intro n2 hn2
  split_ifs <;> ring

/-- At each literal original factor pair, full finite Fourier inversion
is a proved source equality. This is the upstream bridge one may compose
with the original factor-source equality above. -/
theorem original_factorPair_finiteFourier
    (d : MediumAtom) (Y D : ℝ) (a b : ℕ × ℕ × ℕ)
    [NeZero ((complexFactorModulus a).lcm (complexFactorModulus b))] :
    d.complexFactorGamma a * star (d.complexFactorGamma b) *
        (if D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) then 0 else
          originalPair d Y (complexFactorModulus a) (complexFactorModulus b)) =
      d.complexFactorGamma a * star (d.complexFactorGamma b) *
        (if D < ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) then 0 else
          (((complexFactorModulus a).lcm (complexFactorModulus b) : ℂ)⁻¹ *
            ∑ h : ZMod ((complexFactorModulus a).lcm (complexFactorModulus b)),
              additiveCoefficient d Y (complexFactorModulus a) (complexFactorModulus b) h *
                finiteSourceAdditiveFourier d.commonSmoothCarrier d.commonSmoothWeight
                  ((complexFactorModulus a).lcm (complexFactorModulus b)) h)) := by
  rw [originalPair_eq_full_finiteFourier]

end
end ImbalancedChen.Part3.OriginalMaskedWFiniteResidues20261026b
