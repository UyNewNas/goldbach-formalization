import ImbalancedChen.Certificates.PairedV2Geometry

/-!+Uniform geometric ownership of the adopted paired-v2 grid.  This applies
to both E0 and E1: the mesh coordinates, rather than a residual inequality,
separate their actual open four-dimensional fibres.  No claimed numerical
integral value occurs in this ownership proof.
-/

namespace ImbalancedChen.Certificates.PairedV2

theorem tUpper_le_tLower {i k : ℕ} (hik : i < k) :
    tUpper i ≤ tLower k := by
  have hk : (i : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hik
  norm_num [tUpper, tLower, mu, d] at *
  linarith

theorem uUpper_le_uLower {j l : ℕ} (hjl : j < l) :
    uUpper j ≤ uLower l := by
  have hl : (j : ℚ) + 1 ≤ (l : ℚ) := by exact_mod_cast hjl
  norm_num [uUpper, uLower, a, h] at *
  linarith

/-- A point cannot belong to two different decoded grid pairs, even when
their cutoffs or their E0/E1 labels differ. -/
theorem openFibreSupport_unique_indices {i j k l : ℕ} {Z W : ℚ}
    {t u z w : ℝ}
    (hs : openFibreSupport i j Z t u z w)
    (ht : openFibreSupport k l W t u z w) : i = k ∧ j = l := by
  have hti : (tLower i : ℝ) < t := hs.1
  have htk : (tLower k : ℝ) < t := ht.1
  have hit : t < (tUpper i : ℝ) := hs.2.1
  have hkt : t < (tUpper k : ℝ) := ht.2.1
  have hui : (uLower j : ℝ) < u := hs.2.2.1
  have huk : (uLower l : ℝ) < u := ht.2.2.1
  have hiu : u < (uUpper j : ℝ) := hs.2.2.2.1
  have hku : u < (uUpper l : ℝ) := ht.2.2.2.1
  constructor
  · rcases lt_trichotomy i k with h | h | h
    · have hb : (tUpper i : ℝ) ≤ (tLower k : ℝ) :=
        Rat.cast_le.mpr (tUpper_le_tLower h)
      exact False.elim ((lt_irrefl t) ((hit.trans_le hb).trans htk))
    · exact h
    · have hb : (tUpper k : ℝ) ≤ (tLower i : ℝ) :=
        Rat.cast_le.mpr (tUpper_le_tLower h)
      exact False.elim ((lt_irrefl t) ((hkt.trans_le hb).trans hti))
  · rcases lt_trichotomy j l with h | h | h
    · have hb : (uUpper j : ℝ) ≤ (uLower l : ℝ) :=
        Rat.cast_le.mpr (uUpper_le_uLower h)
      exact False.elim ((lt_irrefl u) ((hiu.trans_le hb).trans huk))
    · exact h
    · have hb : (uUpper l : ℝ) ≤ (uLower j : ℝ) :=
        Rat.cast_le.mpr (uUpper_le_uLower h)
      exact False.elim ((lt_irrefl u) ((hku.trans_le hb).trans hui))

/-- The genuine subset of four-dimensional exponent space. -/
def openFibreSet (i j : ℕ) (Z : ℚ) : Set (Fin 4 → ℝ) :=
  {x | openFibreSupport i j Z (x 0) (x 1) (x 2) (x 3)}

theorem openFibreSet_disjoint {i j k l : ℕ} {Z W : ℚ}
    (hne : (i, j) ≠ (k, l)) :
    Disjoint (openFibreSet i j Z) (openFibreSet k l W) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hi, hj⟩ := openFibreSupport_unique_indices hx hy
  exact hne (Prod.ext hi hj)

/-- Injectivity of the actual grid pairs suffices for pairwise disjointness;
injectivity of source ordinals alone would not suffice. -/
theorem openFibreSet_pairwiseDisjoint {ι : Type*}
    (indices : ι → ℕ × ℕ) (cutoff : ι → ℚ)
    (hinj : Function.Injective indices) :
    Pairwise (fun i j => Disjoint
      (openFibreSet (indices i).1 (indices i).2 (cutoff i))
      (openFibreSet (indices j).1 (indices j).2 (cutoff j))) := by
  intro i j hij
  exact openFibreSet_disjoint (fun h => hij (hinj h))

/-- The union has exactly one owner at each point of its support.  This
is geometric coverage; it makes no assertion about the value of an
integral or the arithmetic licensing of that owner. -/
theorem mem_adopted_fibre_union_iff_existsUnique {ι : Type*}
    (indices : ι → ℕ × ℕ) (cutoff : ι → ℚ)
    (hinj : Function.Injective indices) (x : Fin 4 → ℝ) :
    x ∈ ⋃ i, openFibreSet (indices i).1 (indices i).2 (cutoff i) ↔
      ∃! i, x ∈ openFibreSet (indices i).1 (indices i).2 (cutoff i) := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    refine ⟨i, hi, ?_⟩
    intro j hj
    apply hinj
    obtain ⟨ht, hu⟩ := openFibreSupport_unique_indices hj hi
    exact Prod.ext ht hu
  · rintro ⟨i, hi, _⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

end ImbalancedChen.Certificates.PairedV2
