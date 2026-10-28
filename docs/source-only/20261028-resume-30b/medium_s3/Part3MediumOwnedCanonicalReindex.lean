import ImbalancedChen.Part3MediumGlobalDyadicOwnership
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Connect the actual retained installed row and its sixfold half-open owner
to the complete canonical FactorData choices of the first batch.
The exact d and rough product w are summed INSIDE their common dyadic key.
-/
namespace ImbalancedChen.Part3.MediumOwnedCanonicalReindex20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumActualPostSquareDeletion20261028
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028

/-- A natural half-open dyadic window has the exact closed integer
receiver required by the first batch; its upper endpoint is reduced by 1. -/
theorem dyadicWindow_eq_Icc (k : ℕ) :
    dyadicWindow k = Icc (2 ^ k) (2 ^ (k + 1) - 1) := by
  ext n
  have hpos : 0 < (2 : ℕ) ^ (k + 1) := pow_pos (by norm_num) _
  simp only [dyadicWindow, mem_Ico, mem_Icc]
  omega

/-- Actual fixed windows. Exact d is a fibre variable, not a new
outer dyadic-block index or an independently paid remainder. -/
def fixedBlock (k : Key) (d : ℕ) : Block where
  sLo := 2 ^ k.s
  sHi := 2 ^ (k.s + 1) - 1
  tLo := 2 ^ k.t
  tHi := 2 ^ (k.t + 1) - 1
  uLo := 2 ^ k.u
  uHi := 2 ^ (k.u + 1) - 1
  vLo := 2 ^ k.v
  vHi := 2 ^ (k.v + 1) - 1
  wLo := 2 ^ k.w
  wHi := 2 ^ (k.w + 1) - 1
  d := d

def ownedSlice (atom : MediumAtom) (z y : ℝ) (k : Key) (d w : ℕ) :
    Finset (ℕ × ℕ) :=
  (ownedModuli atom z y k).filter (fun q => actualD z q = d ∧ actualW z q = w)

/-- The physical slice is defined from the original retained carrier,
not through choices. The equality to the first-batch receiver is proved. -/
theorem mem_ownedSlice_iff_selected (atom : MediumAtom) (z y : ℝ)
    (k : Key) (d w : ℕ) (q : ℕ × ℕ) :
    q ∈ ownedSlice atom z y k d w ↔
      q ∈ (fixedBlock k d).selectedModuli atom z w ∧
      d ∈ dyadicWindow k.d ∧
      (smoothPart z q.1 : ℝ) ≤ y ∧ (smoothPart z q.2 : ℝ) ≤ y := by
  constructor
  · intro hq
    obtain ⟨ho, hD, hW⟩ := mem_filter.mp hq
    obtain ⟨hr, hk⟩ := mem_filter.mp ho
    obtain ⟨hpair, hret⟩ := mem_filter.mp hr
    obtain ⟨h2, h3, hsy, hty⟩ := hret
    obtain ⟨hs, ht, hu, hv, hd, hw⟩ := (owner_eq_iff_windows z q k).mp hk
    refine ⟨?_, hD ▸ hd, hsy, hty⟩
    apply mem_filter.mpr
    refine ⟨hpair, h2, h3, ?_, ?_, ?_, ?_, hD, hW, ?_⟩
    · simpa only [dyadicWindow_eq_Icc] using hs
    · simpa only [dyadicWindow_eq_Icc] using ht
    · simpa only [dyadicWindow_eq_Icc] using hu
    · simpa only [dyadicWindow_eq_Icc] using hv
    · simpa only [dyadicWindow_eq_Icc] using hW ▸ hw
  · rintro ⟨hsel, hd, hsy, hty⟩
    obtain ⟨hpair, h2, h3, hs, ht, hu, hv, hD, hW, hw⟩ := mem_filter.mp hsel
    have hs' : smoothPart z q.1 ∈ dyadicWindow k.s := by
      simpa only [dyadicWindow_eq_Icc] using hs
    have ht' : smoothPart z q.2 ∈ dyadicWindow k.t := by
      simpa only [dyadicWindow_eq_Icc] using ht
    have hu' : roughPart z q.1 ∈ dyadicWindow k.u := by
      simpa only [dyadicWindow_eq_Icc] using hu
    have hv' : roughPart z q.2 ∈ dyadicWindow k.v := by
      simpa only [dyadicWindow_eq_Icc] using hv
    have hw' : w ∈ dyadicWindow k.w := by
      simpa only [dyadicWindow_eq_Icc] using hw
    have hk : owner z q = k := (owner_eq_iff_windows z q k).mpr
      ⟨hs', ht', hu', hv', hD.symm ▸ hd, hW.symm ▸ hw'⟩
    exact mem_filter.mpr ⟨mem_filter.mpr
      ⟨mem_filter.mpr ⟨hpair, h2, h3, hsy, hty⟩, hk⟩, hD, hW⟩

def trimmedChoices (atom : MediumAtom) (z y : ℝ) (k : Key) (d w : ℕ) :
    Finset Factor :=
  (((fixedBlock k d).factorData atom z).choices d w).filter
    (fun p => (p.s : ℝ) ≤ y ∧ (p.t : ℝ) ≤ y)

/-- A genuine equality of entire physical fibres and choice images,
including the original smooth trim, rather than a pointwise witness map. -/
theorem ownedSlice_eq_image_trimmedChoices (atom : MediumAtom) (z y : ℝ)
    (k : Key) (d w : ℕ) (hd : d ∈ dyadicWindow k.d) :
    ownedSlice atom z y k d w =
      (trimmedChoices atom z y k d w).image physicalModuli := by
  ext q
  constructor
  · intro hq
    obtain ⟨hsel, _, hsy, hty⟩ :=
      (mem_ownedSlice_iff_selected atom z y k d w q).mp hq
    have hp := canonical_mem_choices (fixedBlock k d) atom z hsel
    obtain ⟨_, h2, h3, _⟩ := mem_filter.mp hsel
    exact mem_image.mpr ⟨canonicalFactor z q.1 q.2,
      mem_filter.mpr ⟨hp, hsy, hty⟩, physical_canonical z h2 h3⟩
  · intro hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    obtain ⟨hp, htrim⟩ := mem_filter.mp hp
    have hsel := choice_mem_selected (fixedBlock k d) atom z hp
    have htrim' :
        (smoothPart z (physicalModuli p).1 : ℝ) ≤ y ∧
        (smoothPart z (physicalModuli p).2 : ℝ) ≤ y := by
      change ((canonicalFactor z (physicalModuli p).1 (physicalModuli p).2).s : ℝ) ≤ y ∧
        ((canonicalFactor z (physicalModuli p).1 (physicalModuli p).2).t : ℝ) ≤ y
      rw [canonical_choice (fixedBlock k d) atom z hp]
      exact htrim
    exact (mem_ownedSlice_iff_selected atom z y k d w _).mpr
      ⟨hsel, hd, htrim'⟩

theorem sum_ownedSlice_eq_trimmedChoices (atom : MediumAtom) (z y : ℝ)
    (k : Key) (d w : ℕ) (hd : d ∈ dyadicWindow k.d)
    (f : (ℕ × ℕ) → ℂ) :
    (∑ q ∈ ownedSlice atom z y k d w, f q) =
      ∑ p ∈ trimmedChoices atom z y k d w, f (physicalModuli p) := by
  rw [ownedSlice_eq_image_trimmedChoices atom z y k d w hd]
  apply sum_image
  intro p hp p' hp' heq
  exact physicalModuli_injOn_choices (fixedBlock k d) atom z w
    (mem_filter.mp hp).1 (mem_filter.mp hp').1 heq

private theorem sum_two_fibres {α : Type*} [DecidableEq α]
    (S : Finset α) (D W : Finset ℕ) (dOf wOf : α → ℕ)
    (hD : ∀ q ∈ S, dOf q ∈ D) (hW : ∀ q ∈ S, wOf q ∈ W)
    (f : α → ℂ) :
    (∑ d ∈ D, ∑ w ∈ W, ∑ q ∈ S.filter (fun q => dOf q = d ∧ wOf q = w), f q) =
      ∑ q ∈ S, f q := by
  simp only [sum_filter]
  calc
    _ = ∑ d ∈ D, ∑ q ∈ S, ∑ w ∈ W,
        if dOf q = d ∧ wOf q = w then f q else 0 := by
      apply sum_congr rfl
      intro d hd
      exact sum_comm
    _ = ∑ q ∈ S, ∑ d ∈ D, ∑ w ∈ W,
        if dOf q = d ∧ wOf q = w then f q else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro q hq
      rw [sum_eq_single (dOf q)]
      · rw [sum_eq_single (wOf q)]
        · simp
        · intro w hw hne
          simp [Ne.symm hne]
        · exact fun h => False.elim (h (hW q hq))
      · intro d hd hne
        simp [Ne.symm hne]
      · exact fun h => False.elim (h (hD q hq))

/-- ALL exact d and w inside ONE half-open dyadic key are retained.
No summation of D separately supplied distribution remainders occurs. -/
theorem sum_ownedModuli_eq_all_trimmedChoices (atom : MediumAtom) (z y : ℝ)
    (k : Key) (f : (ℕ × ℕ) → ℂ) :
    (∑ q ∈ ownedModuli atom z y k, f q) =
      ∑ d ∈ dyadicWindow k.d, ∑ w ∈ dyadicWindow k.w,
        ∑ p ∈ trimmedChoices atom z y k d w, f (physicalModuli p) := by
  have hD : ∀ q ∈ ownedModuli atom z y k, actualD z q ∈ dyadicWindow k.d := by
    intro q hq
    exact ((owner_eq_iff_windows z q k).mp (mem_filter.mp hq).2).2.2.2.2.1
  have hW : ∀ q ∈ ownedModuli atom z y k, actualW z q ∈ dyadicWindow k.w := by
    intro q hq
    exact ((owner_eq_iff_windows z q k).mp (mem_filter.mp hq).2).2.2.2.2.2
  calc
    _ = ∑ d ∈ dyadicWindow k.d, ∑ w ∈ dyadicWindow k.w,
        ∑ q ∈ ownedSlice atom z y k d w, f q :=
      (sum_two_fibres (ownedModuli atom z y k) _ _ (actualD z) (actualW z) hD hW f).symm
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro w hw
      exact sum_ownedSlice_eq_trimmedChoices atom z y k d w hd f

/-- Entire actual retained installed row, with its original q1, beta n
and signed/complex kernel, now has a finite global canonical reindexing.
The statement assumes no block cover, licence witness or target equality. -/
theorem sum_retainedRows_eq_global_canonical (atom : MediumAtom) (z y : ℝ)
    (f : RowLabel → ℂ) :
    (∑ l ∈ retainedRows atom z y, f l) =
      ∑ q1 ∈ factorCarrier atom.Q1, ∑ k ∈ keyBank atom z y,
        ∑ d ∈ dyadicWindow k.d, ∑ w ∈ dyadicWindow k.w,
          ∑ p ∈ trimmedChoices atom z y k d w, ∑ n ∈ atom.betaCarrier,
            f ((q1, p.u * p.s, p.v * p.t), n) := by
  rw [sum_retainedRows_eq_physical_pairs]
  apply sum_congr rfl
  intro q1 hq1
  rw [← sum_ownedModuli atom z y (fun q =>
    ∑ n ∈ atom.betaCarrier, f ((q1, q.1, q.2), n))]
  apply sum_congr rfl
  intro k hk
  exact sum_ownedModuli_eq_all_trimmedChoices atom z y k
    (fun q => ∑ n ∈ atom.betaCarrier, f ((q1, q.1, q.2), n))

/-- Specialization to the original deleted progression row: original
physical gamma, beta, residue, q1*q2*q3 and m are unchanged. -/
theorem retainedDeletedRow_eq_global_canonical (atom : MediumAtom)
    (z y : ℝ) (m : ℕ) :
    retainedDeletedRow atom z y m =
      ∑ q1 ∈ factorCarrier atom.Q1, ∑ k ∈ keyBank atom z y,
        ∑ d ∈ dyadicWindow k.d, ∑ w ∈ dyadicWindow k.w,
          ∑ p ∈ trimmedChoices atom z y k d w, ∑ n ∈ atom.betaCarrier,
            atom.complexFactorGamma (q1, p.u * p.s, p.v * p.t) * atom.beta n *
              deletedCongruence atom m ((q1, p.u * p.s, p.v * p.t), n) :=
  sum_retainedRows_eq_global_canonical atom z y _

end
end ImbalancedChen.Part3.MediumOwnedCanonicalReindex20261028
