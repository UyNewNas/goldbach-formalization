import ImbalancedChen.Part3OriginalReciprocalProductAbel
import ImbalancedChen.Part3ActualReciprocalSquarePoisson

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The K prefix is identified with the existing finite reciprocal row.  The
common h coefficient is the indicator of the ORIGINAL signed rectangle,
and the s carrier is the ORIGINAL commonS with one prefix cutoff.  The
signed f is never replaced by its absolute value.  This is an arithmetic
dictionary, before b-Poisson; it is not a spectral PacketData dictionary.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.OriginalReciprocalMaskSeparation20261102
open ImbalancedChen.Part3.OriginalReciprocalProductAbel20261102
open ImbalancedChen.Part3.OriginalMediumAbelOneCoordinate
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
open CommonSmoothCutoff

namespace ImbalancedChen.Part3.OriginalReciprocalPrefixDictionary20261102

attribute [local instance] Classical.propDecidable

def prefixS (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ)
    (st : ℕ × ℕ) (i : ℕ) : Finset ℕ :=
  (commonS atom z k small st).filter (fun s => s ≤ 2 ^ k.u + i)

theorem mem_prefixS (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ)
    (st : ℕ × ℕ) (i s : ℕ) :
    s ∈ prefixS atom z k small st i ↔
      s ∈ commonS atom z k small st ∧ s ≤ 2 ^ k.u + i := by
  simp only [prefixS, mem_filter]

def originalOmega (B : FixedBlock) (R : Rectangle) (h : ℤ) : ℂ :=
  if h ∈ commonH B R then 1 else 0

theorem originalOmega_norm_le_one (B : FixedBlock) (R : Rectangle) (h : ℤ) :
    ‖originalOmega B R h‖ ≤ 1 := by
  unfold originalOmega
  split_ifs <;> simp

/-- The full signed Poisson window only supplies an ambient carrier.  Its
extra frequencies have coefficient exactly zero, not a discarded mask. -/
theorem commonH_subset_signed_window (B : FixedBlock) (R : Rectangle) :
    commonH B R ⊆ poissonNonzeroFrequencyWindow (Nat.ceil B.H) := by
  intro h hh
  have hb := (mem_inter.mp hh).1
  have hw := (mem_Icc.mp (mem_inter.mp (mem_filter.mp hb).1).1)
  have hlow : 1 ≤ h.natAbs := (mem_filter.mp hb).2.1
  have habs : h.natAbs ≤ Nat.ceil B.H := by
    have he : (h.natAbs : ℤ) ≤ (Nat.ceil B.H : ℤ) := by
      simpa only [Int.natCast_natAbs] using (abs_le.mpr hw)
    exact_mod_cast he
  have hn : h.natAbs ∈ Icc 1 (Nat.ceil B.H) := mem_Icc.mpr ⟨hlow, habs⟩
  by_cases hsign : 0 ≤ h
  · apply mem_union.mpr
    apply Or.inl
    exact mem_image.mpr ⟨h.natAbs, hn, by
      simp only [Int.natCast_natAbs, abs_of_nonneg hsign]⟩
  · apply mem_union.mpr
    apply Or.inr
    exact mem_image.mpr ⟨h.natAbs, hn, by
      simp only [Int.natCast_natAbs, abs_of_nonpos (le_of_not_ge hsign), neg_neg]⟩

theorem originalOmega_sum (B : FixedBlock) (R : Rectangle) (F : ℤ → ℂ) :
    (∑ h ∈ poissonNonzeroFrequencyWindow (Nat.ceil B.H),
      originalOmega B R h * F h) = ∑ h ∈ commonH B R, F h := by
  have he : (poissonNonzeroFrequencyWindow (Nat.ceil B.H)).filter
      (fun h => h ∈ commonH B R) = commonH B R := by
    ext h
    simp only [mem_filter]
    exact ⟨fun hh => hh.2, fun hh => ⟨commonH_subset_signed_window B R hh, hh⟩⟩
  simp only [originalOmega, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, he]

/-- Exact shift/reindex.  Every surviving s has a unique index s-S. -/
theorem original_prefix_eq_carrier (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) (i : ℕ) :
    prefix (shiftedBare B atom z k small R st st' e o) i =
      ∑ s ∈ prefixS atom z k small st i,
        if s.Coprime (B.atom.residue.natAbs * packetC o) then
          lambdaS atom st st' e s * ∑ h ∈ commonH B R,
            phase B.atom.residue o.f (packetB o) (packetC o) (s,h)
        else 0 := by
  let F : ℕ → ℂ := fun s =>
    if s.Coprime (B.atom.residue.natAbs * packetC o) then
      lambdaS atom st st' e s * ∑ h ∈ commonH B R,
        phase B.atom.residue o.f (packetB o) (packetC o) (s,h)
    else 0
  change _ = ∑ s ∈ prefixS atom z k small st i, F s
  unfold prefix
  calc
    _ = ∑ j ∈ (range (i+1)).filter
        (fun j => 2 ^ k.u + j ∈ commonS atom z k small st), F (2 ^ k.u + j) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j hj
      by_cases hs : 2 ^ k.u + j ∈ commonS atom z k small st <;>
        simp only [shiftedBare, bareSAtom, F, hs, true_and, false_and,
          if_true, if_false]
    _ = _ := by
      apply sum_bij (fun j _ => 2 ^ k.u + j)
      · intro j hj
        obtain ⟨hj, hs⟩ := mem_filter.mp hj
        exact mem_filter.mpr ⟨hs, by have := mem_range.mp hj; omega⟩
      · intro j hj j' hj' he
        omega
      · intro s hs
        obtain ⟨hs, hcut⟩ := mem_filter.mp hs
        have hlo := (commonS_window atom z k small st hs).1
        have he : 2 ^ k.u + (s - 2 ^ k.u) = s := by omega
        refine ⟨s - 2 ^ k.u, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, he⟩
        simpa only [he] using hs
      · intro j hj
        rfl

/-- Literal intake into the EXISTING reciprocal-square/Poisson API.  A=1
adds no arithmetic condition: the two written gates reduce to the original
single gcd(s,abs(a)*c)=1.  No packet equality is a premise. -/
theorem original_prefix_eq_finiteReciprocalRow (B : FixedBlock)
    (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle)
    (st st' : ℕ × ℕ) (e : Fin 4) (o : Outer) (i : ℕ) :
    prefix (shiftedBare B atom z k small R st st' e o) i =
      finiteReciprocalRow 1 B.atom.residue (prefixS atom z k small st i)
        (Nat.ceil B.H) (lambdaS atom st st' e) (originalOmega B R)
        ((packetB o, packetC o), o.f) := by
  rw [original_prefix_eq_carrier]
  unfold finiteReciprocalRow
  apply sum_congr rfl
  intro s hs
  have hg : (s.Coprime (1 * packetC o) ∧
      s.Coprime (B.atom.residue.natAbs * packetC o)) ↔
      s.Coprime (B.atom.residue.natAbs * packetC o) := by
    simp only [one_mul, Nat.coprime_mul_iff_right]
    tauto
  rw [hg]
  by_cases hu : s.Coprime (B.atom.residue.natAbs * packetC o)
  · simp only [if_pos hu]
    rw [originalOmega_sum]
    rfl
  · simp only [if_neg hu]

/-- K's maximum is genuinely over prefixes of the actual reciprocal row,
with the signed f and every original coefficient still present. -/
theorem original_rowEnvelope_dictionary (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) :
    rowEnvelope B atom z k small R st st' e o =
      (insert 0 ((range (2 ^ k.u)).image (fun i =>
        ‖finiteReciprocalRow 1 B.atom.residue (prefixS atom z k small st i)
          (Nat.ceil B.H) (lambdaS atom st st' e) (originalOmega B R)
          ((packetB o, packetC o), o.f)‖))).max' ⟨0, by simp⟩ := by
  have hS : 0 < (2 : ℕ) ^ k.u := pow_pos (by omega) _
  have hlen : 2 ^ k.u - 1 + 1 = 2 ^ k.u := by omega
  simp only [rowEnvelope, prefixEnvelope, hlen, original_prefix_eq_finiteReciprocalRow]

end ImbalancedChen.Part3.OriginalReciprocalPrefixDictionary20261102

end
