import ImbalancedChen.Part3ActualModeJointBetaPositiveCount
import ImbalancedChen.Part3ActualClosedTCountLicense
import ImbalancedChen.Part3ActualM2FinitePoissonAdapter
import ImbalancedChen.Part3ActualCompletedSquarePushforward

/-!
SOURCEONLY / UNCOMPILED. Only real actual imports: M2 adapter a608 and
joint completed-square17dd. No proposed physical-D or future fBlock import.
The actual omega includes the exact shortened signed dyadic block. This
file proves its support, deletes zero weighted sources, and replaces both
inner global h windows by Htag=2*2^j in each SAME joint beta(z,y).
Every existing source restriction may be retained as a predicate P; its
truth is never an assumption on the actual h support. The t carriers,
two fixedUnit gates, actual lambda/gamma2, reciprocal kernel, output map,
tag h sign and independently selected f sign all remain literal.
No estimate, Cauchy factor, embedding premise or spectral bound is added.
-/

namespace ImbalancedChen.Part3.ActualLogTagHSupportSourceOnly
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset CommonSmoothCutoff
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly ActualSeparatedRowPacketMatchSourceOnly
open scoped BigOperators

/-- Inclusive natural upper cap. The exact block is still imposed by omega. -/
def tagFrequencyBound (tag : ℕ × Bool) : ℕ :=
  2 * _root_.P3ActualLogAdapterSourceOnly.Hnat tag.1

lemma tagFrequencyBound_eq (tag : ℕ × Bool) :
    tagFrequencyBound tag = 2 ^ (tag.1 + 1) := by
  simp only [tagFrequencyBound, _root_.P3ActualLogAdapterSourceOnly.Hnat,
    pow_succ, Nat.mul_comm]

/-- The inverse window implication is elementary; no analytic hypothesis. -/
private lemma mem_frequencyWindow_of_natAbs {H : ℕ} {h : ℤ}
    (hn : h ≠ 0) (hH : h.natAbs ≤ H) : h ∈ poissonNonzeroFrequencyWindow H := by
  have h1 : 1 ≤ h.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn)
  unfold poissonNonzeroFrequencyWindow
  apply mem_union.mpr
  rcases le_total 0 h with hp | hm
  · left
    apply mem_image.mpr
    refine ⟨h.natAbs, mem_Icc.mpr ⟨h1, hH⟩, ?_⟩
    rw [Int.natCast_natAbs, abs_of_nonneg hp]
  · right
    apply mem_image.mpr
    refine ⟨h.natAbs, mem_Icc.mpr ⟨h1, hH⟩, ?_⟩
    rw [Int.natCast_natAbs, abs_of_nonpos hm, neg_neg]

/-- Derived from the real actual block_facts, including the tag h sign. -/
theorem actual_block_frequency_support (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) {h : ℤ}
    (hh : h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag) :
    h ∈ poissonNonzeroFrequencyWindow (tagFrequencyBound tag) ∧
      h ∈ poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z D) ∧
      (h : ℝ) = _root_.P3ActualLogAdapterSourceOnly.epsilon tag.2 * |(h : ℝ)| := by
  have hf := _root_.P3ActualLogAdapterSourceOnly.block_facts hh
  have hhi : |(h : ℝ)| ≤ 2 * _root_.P3ActualLogAdapterSourceOnly.Hreal tag.1 :=
    (div_le_iff₀ (_root_.P3ActualLogAdapterSourceOnly.Hreal_pos tag.1)).mp hf.2.2.2
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hcast : (h.natAbs : ℝ) ≤ (tagFrequencyBound tag : ℝ) := by
    rw [habs]
    simpa only [tagFrequencyBound, Nat.cast_mul, Nat.cast_ofNat,
      _root_.P3ActualLogAdapterSourceOnly.Hreal] using hhi
  have hn : h.natAbs ≤ tagFrequencyBound tag := by exact_mod_cast hcast
  have hglobal : h ∈ poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z D) :=
    (mem_filter.mp hh).1
  exact ⟨mem_frequencyWindow_of_natAbs hf.1 hn, hglobal, hf.2.1⟩

/-- A support conclusion about the actual omega, not an embedding premise. -/
theorem actual_omega_zero_outside_tag_window (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l)) {h : ℤ}
    (hh : h ∉ poissonNonzeroFrequencyWindow (tagFrequencyBound tag)) :
    actualModeOmega e D g l Z tag m negative k h = 0 := by
  have hblock : h ∉ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag :=
    fun hb => hh (actual_block_frequency_support e D Z tag hb).1
  simp only [actualModeOmega, if_neg hblock]

def tagPairSupport (e : MediumAtom) (D : ℕ) (Z : ℝ) (tag : ℕ × Bool)
    (s : Source) : Prop :=
  s.2.1.2 ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag ∧
    s.2.2.2 ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag

/-- Either missing actual h block kills the SAME original quadratic weight. -/
theorem actual_weight_zero_outside_tag_pair (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l))
    (lambda : ℕ → ℂ) (s : Source) (hs : ¬ tagPairSupport e D Z tag s) :
    weight lambda (actualModeOmega e D g l Z tag m negative k) s = 0 := by
  by_cases hu : s.2.1.2 ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag
  · have hv : s.2.2.2 ∉ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag :=
      fun hv => hs ⟨hu, hv⟩
    simp [weight, atomCoeff, actualModeOmega, hv]
  · simp [weight, atomCoeff, actualModeOmega, hu]

/-- Same(z,y) fiber, exact weights: zero sources can be deleted on ANY U. -/
theorem actual_beta_eq_tag_pair_filter (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l))
    (lambda : ℕ → ℂ) (U : Finset Source) (zy : Output) :
    beta U lambda (actualModeOmega e D g l Z tag m negative k) zy =
      beta (U.filter (tagPairSupport e D Z tag)) lambda
        (actualModeOmega e D g l Z tag m negative k) zy := by
  simp only [beta, fiber, sum_filter]
  apply sum_congr rfl
  intro s hs
  by_cases hp : tagPairSupport e D Z tag s
  · simp only [if_pos hp]
  · have hz := actual_weight_zero_outside_tag_pair e D g l Z tag m negative k lambda s hp
    simp only [if_neg hp, hz, ite_self]

/-- Nonzero weighted beta supplies a literal original source in the exact h blocks. -/
theorem actual_beta_nonzero_tag_source (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l))
    (lambda : ℕ → ℂ) (U : Finset Source) (zy : Output)
    (hb : beta U lambda (actualModeOmega e D g l Z tag m negative k) zy ≠ 0) :
    ∃ s ∈ U, tagPairSupport e D Z tag s ∧ output s = zy := by
  rw [actual_beta_eq_tag_pair_filter e D g l Z tag m negative k lambda U zy] at hb
  obtain ⟨s, hs, hout⟩ := mem_image.mp (beta_ne_zero_mem_image hb)
  exact ⟨s, (mem_filter.mp hs).1, (mem_filter.mp hs).2, hout⟩

/-- No Htag<=Hglobal assumption: the actual block lies in BOTH windows. -/
private theorem carrier_iff_on_tag_pair (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (A : ℕ) (a : ℤ) (T : Finset ℕ) (F : Finset ℤ)
    (s : Source) (hs : tagPairSupport e D Z tag s) :
    s ∈ carrier A a T (e.sharedSmoothFrequencyBound Z D) F ↔
      s ∈ carrier A a T (tagFrequencyBound tag) F := by
  have hu := actual_block_frequency_support e D Z tag hs.1
  have hv := actual_block_frequency_support e D Z tag hs.2
  simp only [carrier, rawCarrier, finiteInnerCarrier, mem_filter, mem_product,
    hu.1, hu.2.1, hv.1, hv.2.1, and_true]

/-- Arbitrary source masks (including original nu|f*k and f-sign) survive. -/
theorem actual_tag_pair_carrier_filter_eq (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (A : ℕ) (a : ℤ) (T : Finset ℕ) (F : Finset ℤ)
    (P : Source → Prop) :
    ((carrier A a T (e.sharedSmoothFrequencyBound Z D) F).filter P).filter
        (tagPairSupport e D Z tag) =
      ((carrier A a T (tagFrequencyBound tag) F).filter P).filter
        (tagPairSupport e D Z tag) := by
  ext s
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hs, hP⟩, hb⟩
    exact ⟨⟨(carrier_iff_on_tag_pair e D Z tag A a T F s hb).mp hs, hP⟩, hb⟩
  · rintro ⟨⟨hs, hP⟩, hb⟩
    exact ⟨⟨(carrier_iff_on_tag_pair e D Z tag A a T F s hb).mpr hs, hP⟩, hb⟩

/-- The common block filter really is a finite subcarrier with the smaller cap. -/
theorem actual_tag_pair_subcarrier (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (A : ℕ) (a : ℤ) (T : Finset ℕ) (F : Finset ℤ)
    (P : Source → Prop) :
    (((carrier A a T (e.sharedSmoothFrequencyBound Z D) F).filter P).filter
        (tagPairSupport e D Z tag)) ⊆ carrier A a T (tagFrequencyBound tag) F := by
  intro s hs
  obtain ⟨hP, hb⟩ := mem_filter.mp hs
  exact (carrier_iff_on_tag_pair e D Z tag A a T F s hb).mp (mem_filter.mp hP).1

/-- Full exact beta restriction. lambda is unchanged, and P is carried along. -/
theorem actual_beta_global_eq_tag_bound (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l))
    (A : ℕ) (a : ℤ) (T : Finset ℕ) (F : Finset ℤ) (P : Source → Prop)
    (lambda : ℕ → ℂ) (zy : Output) :
    beta ((carrier A a T (e.sharedSmoothFrequencyBound Z D) F).filter P) lambda
        (actualModeOmega e D g l Z tag m negative k) zy =
      beta ((carrier A a T (tagFrequencyBound tag) F).filter P) lambda
        (actualModeOmega e D g l Z tag m negative k) zy := by
  calc
    _ = beta (((carrier A a T (e.sharedSmoothFrequencyBound Z D) F).filter P).filter
        (tagPairSupport e D Z tag)) lambda
        (actualModeOmega e D g l Z tag m negative k) zy :=
      actual_beta_eq_tag_pair_filter e D g l Z tag m negative k lambda _ zy
    _ = beta (((carrier A a T (tagFrequencyBound tag) F).filter P).filter
        (tagPairSupport e D Z tag)) lambda
        (actualModeOmega e D g l Z tag m negative k) zy := by
      rw [actual_tag_pair_carrier_filter_eq]
    _ = _ := (actual_beta_eq_tag_pair_filter e D g l Z tag m negative k lambda _ zy).symm

/-- Actual M2 lambda: original gamma2, root/residue phases and log mode survive. -/
theorem actual_mode_beta_global_eq_tag_bound (e : MediumAtom) (D delta g l : ℕ)
    [NeZero (g*l)] (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (F : Finset ℤ)
    (P : Source → Prop) (zy : Output) :
    beta ((carrier (g*l) (signedResidue negative e.residue) (baseCarrier e (D/delta))
        (e.sharedSmoothFrequencyBound Z D) F).filter P)
      (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) zy =
    beta ((carrier (g*l) (signedResidue negative e.residue) (baseCarrier e (D/delta))
        (tagFrequencyBound tag) F).filter P)
      (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) zy :=
  actual_beta_global_eq_tag_bound e D g l Z tag m negative k (g*l)
    (signedResidue negative e.residue) (baseCarrier e (D/delta)) F P
    (actualModeLambda e D delta g l m negative u k) zy

end
end ImbalancedChen.Part3.ActualLogTagHSupportSourceOnly
