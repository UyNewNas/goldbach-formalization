import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional

/- Independent consumer-side literal specification. No mathematical premise. -/
open Filter Finset
open scoped Classical BigOperators

namespace IndependentBV

def primeCount (x q a : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ p ≡ a [MOD q])).card

noncomputable def li (x : ℝ) : ℝ :=
  2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t

noncomputable def residueMax (x q : ℕ) : ℝ :=
  let S := (Finset.range q).filter (fun a => Nat.Coprime a q)
  if h : S.Nonempty then
    (S.image (fun a => |(primeCount x q a : ℝ) - li x / Nat.totient q|)).max'
      (Finset.image_nonempty.mpr h)
  else 0

noncomputable def prefixMax (N q : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image (fun y => residueMax y q)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

noncomputable def cutoff (N : ℕ) (B : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B)

/- The consumer definitions above remain literal and independent. These
bridges compare their mathematical values with the producer's definitions,
rather than asking deep simplification to identify dependent maxima. -/

theorem primeCount_eq_producer (x q a : ℕ) :
    primeCount x q a = MathlibNt.SieveTheory.BombieriVinogradov.primesInAP x q a := by
  unfold primeCount MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  constructor
  · intro hp
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp hp)
  · intro hp
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp hp)

theorem li_eq_producer (x : ℝ) :
    li x = MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral x := by
  unfold li MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral
  rfl

theorem cutoff_eq_producer (N : ℕ) (B : ℝ) :
    cutoff N B = MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
  unfold cutoff MathlibNt.SieveTheory.LiuWeight.panModulusCutoff
  rfl

theorem residues_eq_producer (q : ℕ) :
    (Finset.range q).filter (fun a => Nat.Coprime a q) =
      AnalyticNumberTheory.Sieve.unitResidues q := by
  unfold AnalyticNumberTheory.Sieve.unitResidues
  apply Finset.ext
  intro a
  constructor
  · intro ha
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp ha)
  · intro ha
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp ha)

theorem abs_error_eq_producer (x q a : ℕ) :
    |(primeCount x q a : ℝ) - li x / Nat.totient q| =
      |MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError x q a| := by
  unfold MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError
  rw [primeCount_eq_producer, li_eq_producer]

/-- Equal membership determines the maximum, regardless of the chosen
nonemptiness witnesses. The proof compares actual maximum members. -/
private theorem maximum_eq_of_same_members {S T : Finset ℝ}
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hmem : ∀ r : ℝ, r ∈ S ↔ r ∈ T) : S.max' hS = T.max' hT := by
  apply le_antisymm
  · exact Finset.le_max' T (S.max' hS) ((hmem _).mp (Finset.max'_mem S hS))
  · exact Finset.le_max' S (T.max' hT) ((hmem _).mpr (Finset.max'_mem T hT))

theorem residueMax_eq_producer (x q : ℕ) :
    residueMax x q =
      MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPMaxError x q := by
  let S := (Finset.range q).filter (fun a => Nat.Coprime a q)
  let T := AnalyticNumberTheory.Sieve.unitResidues q
  let f := fun a => |(primeCount x q a : ℝ) - li x / Nat.totient q|
  let g := fun a =>
    |MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError x q a|
  have hST : S = T := residues_eq_producer q
  have hfg : ∀ a, f a = g a := abs_error_eq_producer x q
  have hvalues : ∀ r : ℝ, r ∈ S.image f ↔ r ∈ T.image g := by
    intro r
    constructor
    · intro hr
      obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hr
      exact Finset.mem_image.mpr ⟨a, hST ▸ ha, (hfg a).symm.trans har⟩
    · intro hr
      obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hr
      exact Finset.mem_image.mpr ⟨a, hST.symm ▸ ha, (hfg a).trans har⟩
  by_cases hS : S.Nonempty
  · have hT : T.Nonempty := hST ▸ hS
    calc
      residueMax x q = (S.image f).max' (Finset.image_nonempty.mpr hS) := by
        unfold residueMax
        exact dif_pos hS
      _ = (T.image g).max' (Finset.image_nonempty.mpr hT) :=
        maximum_eq_of_same_members _ _ hvalues
      _ = MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPMaxError x q := by
        symm
        unfold MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPMaxError
        exact dif_pos hT
  · have hT : ¬T.Nonempty := fun h => hS (hST.symm ▸ h)
    calc
      residueMax x q = 0 := by
        unfold residueMax
        exact dif_neg hS
      _ = MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPMaxError x q := by
        symm
        unfold MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPMaxError
        exact dif_neg hT

theorem prefixMax_eq_producer (N q : ℕ) :
    prefixMax N q =
      MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q := by
  unfold prefixMax MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError
  apply maximum_eq_of_same_members
  intro r
  constructor
  · intro hr
    obtain ⟨y, hy, hyr⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image.mpr
      ⟨y, hy, (residueMax_eq_producer y q).symm.trans hyr⟩
  · intro hr
    obtain ⟨y, hy, hyr⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image.mpr
      ⟨y, hy, (residueMax_eq_producer y q).trans hyr⟩

theorem standard_bv :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
        ∀ᶠ N : ℕ in atTop, 2 ≤ N →
          ∑ q ∈ Finset.Icc 1 (cutoff N B), prefixMax N q ≤
            C * (N : ℝ) / Real.log N ^ A := by
  intro A hA
  obtain ⟨B, hB, C, hC, hbound⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov A hA
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [hbound] with N hN
  intro hN2
  have hsum :
      (∑ q ∈ Finset.Icc 1 (cutoff N B), prefixMax N q) =
        ∑ q ∈ Finset.Icc 1 (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
          MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q := by
    rw [cutoff_eq_producer]
    apply Finset.sum_congr rfl
    intro q hq
    exact prefixMax_eq_producer N q
  rw [hsum]
  exact hN hN2

end IndependentBV

set_option pp.all true in
#check @IndependentBV.standard_bv
#print axioms AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
#print axioms IndependentBV.standard_bv
