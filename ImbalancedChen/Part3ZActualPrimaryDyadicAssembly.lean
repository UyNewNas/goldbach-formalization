import ImbalancedChen.Part3ZActualPrimaryShortEndpoint
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# P3 exact finite primary/sign/output-dyadic assembly

Source-written, uncompiled. These keys partition the actual joint output y,
not the existing fKey decomposition of the original frequency f.
The sibling short-endpoint module must be staged on the source path.
-/

namespace ImbalancedChen.P3ZActualPrimaryDyadicAssembly

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3 (CommonCompletedVariable)
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly
open ImbalancedChen.P3ZActualPrimaryShortEndpoint

abbrev Key := ℕ × (ℕ × Bool)

/-- The j=0 block has U=1/2 and contains the integer |y|=1. -/
def dyadicScale (j : ℕ) : ℝ := (((2 : ℕ) ^ j : ℕ) : ℝ) / 2

def outputKey (rho : ℤ) (zy : Output) : Key :=
  (rhoPrimaryNu rho zy.2, (Nat.clog 2 zy.2.natAbs, decide (zy.2 < 0)))

def sourceKey (rho : ℤ) (s : Source) : Key := outputKey rho (output s)

def keys (rho : ℤ) (S : Finset Source) : Finset Key :=
  (nonzeroSource S).image (sourceKey rho)

def block (rho : ℤ) (S : Finset Source) (k : Key) : Finset Source :=
  (nonzeroSource S).filter (fun s => sourceKey rho s = k)

theorem dyadicScale_pos (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

theorem power_step {j : ℕ} (hj : 0 < j) :
    (2 : ℕ) ^ j = 2 * 2 ^ (j - 1) := by
  calc
    _ = (2 : ℕ) ^ ((j - 1) + 1) := congrArg (fun k => (2 : ℕ) ^ k) (by omega)
    _ = 2 * 2 ^ (j - 1) := by rw [pow_succ]; ring

theorem clog_dyadic_bounds {m : ℕ} (hm : 0 < m) :
    dyadicScale (Nat.clog 2 m) < (m : ℝ) ∧
      (m : ℝ) ≤ 2 * dyadicScale (Nat.clog 2 m) := by
  have hupperN := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) m
  have hupper : (m : ℝ) ≤ (((2 : ℕ) ^ Nat.clog 2 m : ℕ) : ℝ) := by exact_mod_cast hupperN
  constructor
  · by_cases hm1 : m = 1
    · subst m
      norm_num [dyadicScale, Nat.clog_one_right]
    · have hm2 : 1 < m := by omega
      have hj := Nat.clog_pos (by norm_num : 1 < (2 : ℕ)) hm2
      have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2 : ℕ)) hm2
      have hpred' : (2 : ℕ) ^ (Nat.clog 2 m - 1) < m := by simpa only [Nat.pred_eq_sub_one] using hpred
      have hpredR : (((2 : ℕ) ^ (Nat.clog 2 m - 1) : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hpred'
      have hstepR : (((2 : ℕ) ^ Nat.clog 2 m : ℕ) : ℝ) =
          2 * (((2 : ℕ) ^ (Nat.clog 2 m - 1) : ℕ) : ℝ) := by
        exact_mod_cast power_step hj
      unfold dyadicScale
      nlinarith only [hpredR, hstepR]
  · unfold dyadicScale
    linarith only [hupper]

theorem clog_eq_iff_dyadic {m j : ℕ} (hm : 0 < m) :
    Nat.clog 2 m = j ↔ dyadicScale j < (m : ℝ) ∧ (m : ℝ) ≤ 2 * dyadicScale j := by
  constructor
  · intro h
    simpa only [h] using clog_dyadic_bounds hm
  · intro hs
    have hupperR : (m : ℝ) ≤ (((2 : ℕ) ^ j : ℕ) : ℝ) := by
      calc
        _ ≤ 2 * dyadicScale j := hs.2
        _ = (((2 : ℕ) ^ j : ℕ) : ℝ) := by unfold dyadicScale; ring
    have hupperN : m ≤ (2 : ℕ) ^ j := by exact_mod_cast hupperR
    have hclog : Nat.clog 2 m ≤ j := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hupperN
    by_cases hj : j = 0
    · omega
    · have hstepR : (((2 : ℕ) ^ j : ℕ) : ℝ) = 2 * (((2 : ℕ) ^ (j - 1) : ℕ) : ℝ) := by
        exact_mod_cast power_step (Nat.pos_of_ne_zero hj)
      have hlowerR : (((2 : ℕ) ^ (j - 1) : ℕ) : ℝ) < (m : ℝ) := by
        have hh := hs.1
        unfold dyadicScale at hh
        nlinarith only [hh, hstepR]
      have hlowerN : (2 : ℕ) ^ (j - 1) < m := by exact_mod_cast hlowerR
      have hlower := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < (2 : ℕ))).mpr hlowerN
      omega

theorem sign_key_iff {y : ℤ} (hy : y ≠ 0) (negative : Bool) :
    decide (y < 0) = negative ↔ (if negative then y < 0 else 0 < y) := by
  by_cases hn : y < 0
  · cases negative <;> simp [hn]
  · have hp : 0 < y := by omega
    cases negative <;> simp [hn, hp]

theorem block_subset (rho : ℤ) (S : Finset Source) (k : Key) : block rho S k ⊆ nonzeroSource S := by
  intro s hs
  exact (mem_filter.mp hs).1

theorem source_own_block {rho : ℤ} {S : Finset Source} {s : Source}
    (hs : s ∈ nonzeroSource S) :
    sourceKey rho s ∈ keys rho S ∧ s ∈ block rho S (sourceKey rho s) := by
  exact ⟨mem_image_of_mem _ hs, mem_filter.mpr ⟨hs, rfl⟩⟩

theorem block_key_unique {rho : ℤ} {S : Finset Source} {k q : Key} {s : Source}
    (hk : s ∈ block rho S k) (hq : s ∈ block rho S q) : k = q := by
  exact (mem_filter.mp hk).2.symm.trans (mem_filter.mp hq).2

theorem blocks_disjoint {rho : ℤ} {S : Finset Source} {k q : Key} (hneq : k ≠ q) :
    Disjoint (block rho S k) (block rho S q) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  exact hneq (block_key_unique hs ht)

theorem block_output_nonzero {rho : ℤ} {S : Finset Source} {k : Key} {s : Source}
    (hs : s ∈ block rho S k) : (output s).2 ≠ 0 := by
  exact (mem_filter.mp (block_subset rho S k hs)).2

theorem keys_multiplier_pos {rho : ℤ} {S : Finset Source} {k : Key}
    (hk : k ∈ keys rho S) : 0 < k.1 := by
  obtain ⟨s, _, rfl⟩ := mem_image.mp hk
  exact rhoPrimaryNu_pos rho (output s).2

/-- This identifies the computed-key block with the literal filter used
by the short-endpoint module, including both boundary conventions. -/
theorem block_eq_dyadicSource (rho : ℤ) (S : Finset Source) (nu j : ℕ) (negative : Bool) :
    block rho S (nu, (j, negative)) = dyadicSource rho S nu (dyadicScale j) negative := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsS, hk⟩ := mem_filter.mp hs
    have hy : (output s).2 ≠ 0 := (mem_filter.mp hsS).2
    have hp := congrArg Prod.fst hk
    have hj := congrArg (fun k : Key => k.2.1) hk
    have hn := congrArg (fun k : Key => k.2.2) hk
    change rhoPrimaryNu rho (output s).2 = nu at hp
    change Nat.clog 2 (output s).2.natAbs = j at hj
    change decide ((output s).2 < 0) = negative at hn
    have hb := (clog_eq_iff_dyadic (Int.natAbs_pos.mpr hy)).mp hj
    have habs : (((output s).2.natAbs : ℕ) : ℝ) = |((output s).2 : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [habs] at hb
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hsS, hp⟩, hb.1, hb.2, (sign_key_iff hy negative).mp hn⟩
  · intro hs
    obtain ⟨hprimary, hlo, hhi, hsign⟩ := mem_filter.mp hs
    obtain ⟨hsS, hp⟩ := mem_filter.mp hprimary
    have hy : (output s).2 ≠ 0 := (mem_filter.mp hsS).2
    have habs : (((output s).2.natAbs : ℕ) : ℝ) = |((output s).2 : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    have hj : Nat.clog 2 (output s).2.natAbs = j :=
      (clog_eq_iff_dyadic (Int.natAbs_pos.mpr hy)).mpr (by simpa only [habs] using And.intro hlo hhi)
    have hn := (sign_key_iff hy negative).mpr hsign
    apply mem_filter.mpr
    refine ⟨hsS, ?_⟩
    change (rhoPrimaryNu rho (output s).2, (Nat.clog 2 (output s).2.natAbs, decide ((output s).2 < 0))) = _
    exact Prod.ext hp (Prod.ext hj hn)

theorem finite_source_assembly (rho : ℤ) (S : Finset Source) (F : Source → ℂ) :
    (∑ s ∈ nonzeroSource S, F s) = ∑ k ∈ keys rho S, ∑ s ∈ block rho S k, F s := by
  exact (sum_fiberwise_of_maps_to (s := nonzeroSource S) (t := keys rho S)
    (g := sourceKey rho) (fun s hs => mem_image_of_mem _ hs) F).symm

/-- Each joint-output fibre belongs to a single computed block. -/
theorem beta_block (rho : ℤ) (S : Finset Source) (k : Key)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (zy : Output) :
    beta (block rho S k) lambda omega zy =
      if outputKey rho zy = k then beta (nonzeroSource S) lambda omega zy else 0 := by
  have hf : fiber (block rho S k) zy =
      (fiber (nonzeroSource S) zy).filter (fun _ => outputKey rho zy = k) := by
    ext s
    simp only [fiber, block, sourceKey, mem_filter]
    constructor
    · rintro ⟨⟨hs, hk⟩, hout⟩
      exact ⟨⟨hs, hout⟩, by simpa only [hout] using hk⟩
    · rintro ⟨⟨hs, hout⟩, hk⟩
      exact ⟨⟨hs, by simpa only [hout] using hk⟩, hout⟩
  unfold beta
  rw [hf]
  by_cases hk : outputKey rho zy = k <;> simp [hk]

theorem beta_nonzero_key_mem {rho : ℤ} {S : Finset Source}
    {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {zy : Output}
    (hb : beta (nonzeroSource S) lambda omega zy ≠ 0) : outputKey rho zy ∈ keys rho S := by
  obtain ⟨s, hs, hout⟩ := mem_image.mp (beta_ne_zero_mem_image hb)
  exact mem_image.mpr ⟨s, hs, by simpa only [sourceKey, hout]⟩

theorem finite_beta_assembly (rho : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (zy : Output) :
    beta (nonzeroSource S) lambda omega zy = ∑ k ∈ keys rho S, beta (block rho S k) lambda omega zy := by
  by_cases hb : beta (nonzeroSource S) lambda omega zy = 0
  · simp [beta_block, hb]
  · have hk := beta_nonzero_key_mem (rho := rho) hb
    simp [beta_block, hk]

/-- No Cauchy or cardinality loss: distinct blocks have disjoint JOINT
output fibres, so their finite beta energies add exactly. -/
theorem finite_beta_energy_assembly (rho : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (B : Finset Output) :
    (∑ zy ∈ B, ‖beta (nonzeroSource S) lambda omega zy‖ ^ 2) =
      ∑ k ∈ keys rho S, ∑ zy ∈ B, ‖beta (block rho S k) lambda omega zy‖ ^ 2 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro zy _
  by_cases hb : beta (nonzeroSource S) lambda omega zy = 0
  · simp [beta_block, hb]
  · have hk := beta_nonzero_key_mem (rho := rho) hb
    simp [beta_block, hk]

theorem beta_block_ne_zero_key {rho : ℤ} {S : Finset Source} {k : Key}
    {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {zy : Output}
    (hb : beta (block rho S k) lambda omega zy ≠ 0) :
    k = outputKey rho zy ∧ outputKey rho zy ∈ keys rho S ∧
      beta (nonzeroSource S) lambda omega zy ≠ 0 := by
  by_cases hk : outputKey rho zy = k
  · rw [beta_block, if_pos hk] at hb
    exact ⟨hk.symm, beta_nonzero_key_mem hb, hb⟩
  · rw [beta_block, if_neg hk] at hb
    exact False.elim (hb rfl)

/-- Direct connection to the signed primary beta from the predecessor. -/
theorem signed_beta_block_eq (rho : ℤ) (S : Finset Source) (nu j : ℕ)
    (negative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (n z : ℕ) :
    beta (block rho S (nu, (j, negative))) lambda omega (z, signedY negative (nu * n)) =
      dyadicBeta rho S nu (dyadicScale j) negative lambda omega (nu * n) z := by
  rw [block_eq_dyadicSource]
  rfl

theorem assembled_short_index_eq_one {rho : ℤ} {S : Finset Source} {nu j n z : ℕ}
    {negative : Bool} {lambda : ℕ → ℂ} {omega : ℤ → ℂ}
    (hshort : dyadicScale j / (nu : ℝ) < 1)
    (hb : beta (block rho S (nu, (j, negative))) lambda omega
      (z, signedY negative (nu * n)) ≠ 0) : n = 1 := by
  rw [signed_beta_block_eq] at hb
  exact short_nonzero_index_eq_one (dyadicScale_pos j) hshort hb

theorem assembled_beta_coprime {rho : ℤ} {S : Finset Source} {nu j n z : ℕ}
    {negative : Bool} {lambda : ℕ → ℂ} {omega : ℤ → ℂ}
    (hb : beta (block rho S (nu, (j, negative))) lambda omega
      (z, signedY negative (nu * n)) ≠ 0) : Nat.Coprime n rho.natAbs := by
  rw [signed_beta_block_eq] at hb
  exact dyadicBeta_coprime hb

theorem nonzeroSource_idempotent (S : Finset Source) :
    nonzeroSource (nonzeroSource S) = nonzeroSource S := by
  ext s
  simp only [nonzeroSource, mem_filter]
  tauto

/-- The complete installed actual nonzero-source beta energy, not a
new independent coefficient family or an assumed L2 budget. -/
theorem actual_beta_energy_assembly (e : ImbalancedChen.Part3.MediumAtom)
    (D delta g l : ℕ) (Z : ℝ) (negative : Bool)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (B : Finset Output) :
    let S := ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
      e D delta g l Z negative
    let rho := ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.signedResidue negative e.residue
    (∑ zy ∈ B, ‖beta S lambda omega zy‖ ^ 2) =
      ∑ k ∈ keys rho S, ∑ zy ∈ B, ‖beta (block rho S k) lambda omega zy‖ ^ 2 := by
  dsimp only
  have h := finite_beta_energy_assembly
    (ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.signedResidue negative e.residue)
    (ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
      e D delta g l Z negative) lambda omega B
  have heq : nonzeroSource
      (ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
        e D delta g l Z negative) =
      ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
        e D delta g l Z negative := by
    unfold ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
    exact nonzeroSource_idempotent _
  rw [heq] at h
  exact h

/-- Exact finite common-phase packet assembly on the actual source.
The same I.weight is present in every block, row and completed m. -/
theorem common_phase_source_assembly (rho : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (I : CommonCompletedVariable)
    (M : Finset ℕ) (K : ℕ → Output → ℂ) :
    (∑ m ∈ M, ∑ s ∈ nonzeroSource S, I.weight m * weight lambda omega s * K m (output s)) =
      ∑ k ∈ keys rho S, ∑ m ∈ M, ∑ s ∈ block rho S k,
        I.weight m * weight lambda omega s * K m (output s) := by
  have hs (m : ℕ) := finite_source_assembly rho S
    (fun s => I.weight m * weight lambda omega s * K m (output s))
  simp_rw [hs]
  rw [sum_comm]

theorem common_phase_beta_assembly (rho : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (I : CommonCompletedVariable)
    (M : Finset ℕ) (B : Finset Output) (K : ℕ → Output → ℂ) :
    (∑ m ∈ M, ∑ zy ∈ B, I.weight m * beta (nonzeroSource S) lambda omega zy * K m zy) =
      ∑ k ∈ keys rho S, ∑ m ∈ M, ∑ zy ∈ B,
        I.weight m * beta (block rho S k) lambda omega zy * K m zy := by
  calc
    _ = ∑ m ∈ M, ∑ zy ∈ B, ∑ k ∈ keys rho S,
        I.weight m * beta (block rho S k) lambda omega zy * K m zy := by
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro zy _
      rw [finite_beta_assembly rho S lambda omega zy, mul_sum, sum_mul]
    _ = ∑ m ∈ M, ∑ k ∈ keys rho S, ∑ zy ∈ B,
        I.weight m * beta (block rho S k) lambda omega zy * K m zy := by
      apply sum_congr rfl
      intro m _
      exact sum_comm
    _ = _ := by rw [sum_comm]

end

end ImbalancedChen.P3ZActualPrimaryDyadicAssembly
