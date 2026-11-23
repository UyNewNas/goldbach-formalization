import ImbalancedChen.P5ZU11OriginalLastPair
import Mathlib.Data.Finset.Max

/-!
Finite adaptive selection on the literal original U11 source.  Tag 0 is
the switched bound; tag j+1 is ordinary policy j, allowed only where its
complete eligibility predicate holds.  Ties are assigned to the least tag.
Thus alternatives never add on overlapping domains.  Every local bound
below concerns one actual quotient-source cardinality, not the full mean.

CP: this proves selection and finite accounting only.  Proving the local
Rosser/density inequalities for these cardinalities, their common analytic
approximation, and the full four-dimensional integral remains necessary.
Status: source_written / uncompiled.
-/

namespace ImbalancedChen.P5Z.U11Adaptive

open scoped BigOperators
open Classical

noncomputable section

abbrev Four := (ℕ × ℕ) × (ℕ × ℕ)

def source (N : ℕ) (E : ℕ × ℕ → Prop) : Finset Four :=
  (chenY11FullPrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
      (fun t => ¬ E t.2)

def weight (N : ℕ) (t : Four) : ℝ :=
  ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
    (t.1.2 : ℝ)).card : ℝ)

theorem current_eq_sum_weight (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon11 N E = ∑ t ∈ source N E, weight N t := by
  exact currentChenUpsilon11_eq_siftedQuotientPrimeSource N E

/-- The manuscript coordinates decrease from the fourth prime to the first. -/
def logCoordinate (N p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log (N : ℝ)

def switchedKernel (N : ℕ) (K : ℝ) (omega : ℝ → ℝ) (t : Four) : ℝ :=
  K * omega ((1 - (logCoordinate N t.2.2 + logCoordinate N t.2.1 +
    logCoordinate N t.1.2 + logCoordinate N t.1.1)) /
      logCoordinate N t.1.2) / logCoordinate N t.1.2

def ordinaryKernel (N : ℕ) (H : ℝ → ℝ) (L : ℕ → Four → ℝ)
    (j : ℕ) (t : Four) : ℝ :=
  4 * (1 - H (max 2 (L j t / logCoordinate N t.1.1))) / L j t

/-- The global tag bank contains each labelled policy only once. -/
def tags (bank : Finset ℕ) : Finset ℕ := insert 0 (bank.image Nat.succ)

/-- Eligibility includes all full/selected square and physical ceiling
gates required by policy j at this complete four-prime label. -/
def candidates (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (t : Four) : Finset ℕ :=
  insert 0 ((bank.filter (fun j => eligible j t)).image Nat.succ)

theorem candidates_nonempty (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (t : Four) : (candidates bank eligible t).Nonempty :=
  ⟨0, Finset.mem_insert_self _ _⟩

theorem candidates_subset_tags (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (t : Four) : candidates bank eligible t ⊆ tags bank := by
  intro c hc
  rcases Finset.mem_insert.mp hc with h0 | hc
  · exact Finset.mem_insert.mpr (Or.inl h0)
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_insert.mpr (Or.inr
      (Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, rfl⟩))

def kernel (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ)
    (c : ℕ) (t : Four) : ℝ :=
  if c = 0 then switched t else ordinary c.pred t

/-- An actual finite minimum, with the switched option always present. -/
def envelope (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (t : Four) : ℝ :=
  ((candidates bank eligible t).image (fun c => kernel switched ordinary c t)).min'
    ((candidates_nonempty bank eligible t).image _)

theorem envelope_le_candidate (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (t : Four)
    (c : ℕ) (hc : c ∈ candidates bank eligible t) :
    envelope bank eligible switched ordinary t ≤ kernel switched ordinary c t := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)

def minimizers (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (t : Four) : Finset ℕ :=
  (candidates bank eligible t).filter (fun c =>
    kernel switched ordinary c t = envelope bank eligible switched ordinary t)

theorem minimizers_nonempty (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (t : Four) :
    (minimizers bank eligible switched ordinary t).Nonempty := by
  have hm := Finset.min'_mem
    ((candidates bank eligible t).image (fun c => kernel switched ordinary c t))
    ((candidates_nonempty bank eligible t).image _)
  obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hm
  exact ⟨c, Finset.mem_filter.mpr ⟨hc, heq⟩⟩

/-- Deterministic tie breaking: take the smallest tag attaining the finite
minimum. This is finite search; no independent choice of overlapping cells. -/
def chosen (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (t : Four) : ℕ :=
  (minimizers bank eligible switched ordinary t).min'
    (minimizers_nonempty bank eligible switched ordinary t)

theorem chosen_spec (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (t : Four) :
    chosen bank eligible switched ordinary t ∈ candidates bank eligible t ∧
      kernel switched ordinary (chosen bank eligible switched ordinary t) t =
        envelope bank eligible switched ordinary t := by
  exact Finset.mem_filter.mp (Finset.min'_mem
    (minimizers bank eligible switched ordinary t)
    (minimizers_nonempty bank eligible switched ordinary t))

theorem chosen_mem_tags (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (t : Four) :
    chosen bank eligible switched ordinary t ∈ tags bank :=
  candidates_subset_tags bank eligible t (chosen_spec bank eligible switched ordinary t).1

theorem chosen_ordinary_eligible (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (t : Four) (j : ℕ)
    (hj : chosen bank eligible switched ordinary t = j.succ) :
    j ∈ bank ∧ eligible j t := by
  have hc := (chosen_spec bank eligible switched ordinary t).1
  rw [hj] at hc
  rcases Finset.mem_insert.mp hc with hzero | hc
  · exact (Nat.succ_ne_zero j hzero).elim
  · obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hc
    have hkj' : k = j := Nat.succ.inj hkj
    subst k
    exact Finset.mem_filter.mp hk

/-- A common nonnegative atom mass commutes with choosing the minimum.
This records the scale needed when kernels are densities rather than
literal cardinal upper bounds. -/
theorem scaled_envelope_le_candidate (bank : Finset ℕ)
    (eligible : ℕ → Four → Prop) (switched : Four → ℝ)
    (ordinary : ℕ → Four → ℝ) (t : Four) (m : ℝ) (hm : 0 ≤ m)
    (c : ℕ) (hc : c ∈ candidates bank eligible t) :
    m * envelope bank eligible switched ordinary t ≤
      m * kernel switched ordinary c t := by
  exact mul_le_mul_of_nonneg_left
    (envelope_le_candidate bank eligible switched ordinary t c hc) hm

/-- Local majorants suffice for the minimum. The ordinary hypothesis is
requested only when j belongs to the bank and is eligible at this tuple. -/
theorem weight_le_envelope (N : ℕ) (bank : Finset ℕ)
    (eligible : ℕ → Four → Prop) (switched : Four → ℝ)
    (ordinary : ℕ → Four → ℝ) (t : Four)
    (hs : weight N t ≤ switched t)
    (ho : ∀ j ∈ bank, eligible j t → weight N t ≤ ordinary j t) :
    weight N t ≤ envelope bank eligible switched ordinary t := by
  apply Finset.le_min'
  intro v hv
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
  rcases Finset.mem_insert.mp hc with h0 | hc
  · simpa only [h0, kernel, if_pos rfl] using hs
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hjbank, hjeligible⟩ := Finset.mem_filter.mp hj
    simpa [kernel] using ho j hjbank hjeligible

def cell (T : Finset Four) (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (c : ℕ) : Finset Four :=
  T.filter (fun t => chosen bank eligible switched ordinary t = c)

theorem cells_disjoint (T : Finset Four) (bank : Finset ℕ)
    (eligible : ℕ → Four → Prop) (switched : Four → ℝ)
    (ordinary : ℕ → Four → ℝ) {c d : ℕ} (hcd : c ≠ d) :
    Disjoint (cell T bank eligible switched ordinary c)
      (cell T bank eligible switched ordinary d) := by
  apply Finset.disjoint_left.mpr
  intro t hc hd
  exact hcd ((Finset.mem_filter.mp hc).2.symm.trans (Finset.mem_filter.mp hd).2)

theorem mem_some_cell_iff (T : Finset Four) (bank : Finset ℕ)
    (eligible : ℕ → Four → Prop) (switched : Four → ℝ)
    (ordinary : ℕ → Four → ℝ) (t : Four) :
    (∃ c ∈ tags bank, t ∈ cell T bank eligible switched ordinary c) ↔ t ∈ T := by
  constructor
  · rintro ⟨c, hc, ht⟩
    exact (Finset.mem_filter.mp ht).1
  · intro ht
    exact ⟨chosen bank eligible switched ordinary t,
      chosen_mem_tags bank eligible switched ordinary t,
      Finset.mem_filter.mpr ⟨ht, rfl⟩⟩

/-- Exact regrouping for every signed weight on the common source. -/
theorem sum_cells (T : Finset Four) (bank : Finset ℕ)
    (eligible : ℕ → Four → Prop) (switched : Four → ℝ)
    (ordinary : ℕ → Four → ℝ) (f : Four → ℝ) :
    (∑ c ∈ tags bank, ∑ t ∈ cell T bank eligible switched ordinary c, f t) =
      ∑ t ∈ T, f t := by
  simp only [cell, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    _ = (if chosen bank eligible switched ordinary t =
        chosen bank eligible switched ordinary t then f t else 0) := by
      apply Finset.sum_eq_single (chosen bank eligible switched ordinary t)
      · intro c hc hne
        exact if_neg (Ne.symm hne)
      · intro hn
        exact (hn (chosen_mem_tags bank eligible switched ordinary t)).elim
    _ = f t := if_pos rfl

/-- Each cell uses its own chosen candidate, but the cells partition one
common domain. Signed kernels are permitted in this identity. -/
theorem sum_envelope_eq_cells (T : Finset Four) (bank : Finset ℕ)
    (eligible : ℕ → Four → Prop) (switched : Four → ℝ)
    (ordinary : ℕ → Four → ℝ) :
    (∑ t ∈ T, envelope bank eligible switched ordinary t) =
      ∑ c ∈ tags bank, ∑ t ∈ cell T bank eligible switched ordinary c,
        kernel switched ordinary c t := by
  rw [← sum_cells T bank eligible switched ordinary
    (envelope bank eligible switched ordinary)]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro t ht
  have hchosen := (Finset.mem_filter.mp ht).2
  exact (chosen_spec bank eligible switched ordinary t).2.symm.trans
    (congrArg (fun j => kernel switched ordinary j t) hchosen)

/-- Original U11 application. Every local analytic estimate is on the
literal four-label quotient source. No whole-U11 mean is assumed. -/
theorem current_le_adaptive_cells (N : ℕ) (E : ℕ × ℕ → Prop)
    (bank : Finset ℕ) (eligible : ℕ → Four → Prop) (switched : Four → ℝ)
    (ordinary : ℕ → Four → ℝ)
    (hs : ∀ t ∈ source N E, weight N t ≤ switched t)
    (ho : ∀ t ∈ source N E, ∀ j ∈ bank,
      eligible j t → weight N t ≤ ordinary j t) :
    currentChenUpsilon11 N E ≤
      ∑ c ∈ tags bank, ∑ t ∈ cell (source N E) bank eligible switched ordinary c,
        kernel switched ordinary c t := by
  rw [current_eq_sum_weight, ← sum_envelope_eq_cells]
  apply Finset.sum_le_sum
  intro t ht
  exact weight_le_envelope N bank eligible switched ordinary t (hs t ht) (ho t ht)

/-- Specialization to the manuscript's two actual kernel formulas. The
H table, residual exponents, and eligibility gates are supplied as local
policy data; the finite minimum itself is the concrete `envelope` above. -/
theorem current_le_original_kernel_cells (N : ℕ) (E : ℕ × ℕ → Prop)
    (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (K : ℝ) (omega H : ℝ → ℝ) (L : ℕ → Four → ℝ)
    (hs : ∀ t ∈ source N E, weight N t ≤ switchedKernel N K omega t)
    (ho : ∀ t ∈ source N E, ∀ j ∈ bank,
      eligible j t → weight N t ≤ ordinaryKernel N H L j t) :
    currentChenUpsilon11 N E ≤
      ∑ c ∈ tags bank,
        ∑ t ∈ cell (source N E) bank eligible (switchedKernel N K omega)
            (ordinaryKernel N H L) c,
          kernel (switchedKernel N K omega) (ordinaryKernel N H L) c t := by
  exact current_le_adaptive_cells N E bank eligible (switchedKernel N K omega)
    (ordinaryKernel N H L) hs ho

/-- Averaged local analytic estimates may instead be supplied separately
on the disjoint winner cells.  The atom masses carry the density/counting
normalization; no pointwise cardinal estimate is needed by this version. -/
theorem current_le_cells_of_local_averages (N : ℕ) (E : ℕ × ℕ → Prop)
    (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (mass : Four → ℝ)
    (hlocal : ∀ c ∈ tags bank,
      (∑ t ∈ cell (source N E) bank eligible switched ordinary c, weight N t) ≤
        ∑ t ∈ cell (source N E) bank eligible switched ordinary c,
          mass t * kernel switched ordinary c t) :
    currentChenUpsilon11 N E ≤
      ∑ c ∈ tags bank, ∑ t ∈ cell (source N E) bank eligible switched ordinary c,
        mass t * kernel switched ordinary c t := by
  rw [current_eq_sum_weight,
    ← sum_cells (source N E) bank eligible switched ordinary (weight N)]
  exact Finset.sum_le_sum hlocal

/-- The actual switched/ordinary formulas can be selected with their
common positive atom masses and with local averaged analytic premises. -/
theorem current_le_scaled_original_cells (N : ℕ) (E : ℕ × ℕ → Prop)
    (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (K : ℝ) (omega H : ℝ → ℝ) (L : ℕ → Four → ℝ) (mass : Four → ℝ)
    (hlocal : ∀ c ∈ tags bank,
      (∑ t ∈ cell (source N E) bank eligible (switchedKernel N K omega)
          (ordinaryKernel N H L) c, weight N t) ≤
        ∑ t ∈ cell (source N E) bank eligible (switchedKernel N K omega)
            (ordinaryKernel N H L) c,
          mass t * kernel (switchedKernel N K omega) (ordinaryKernel N H L) c t) :
    currentChenUpsilon11 N E ≤
      ∑ c ∈ tags bank,
        ∑ t ∈ cell (source N E) bank eligible (switchedKernel N K omega)
            (ordinaryKernel N H L) c,
          mass t * kernel (switchedKernel N K omega) (ordinaryKernel N H L) c t := by
  exact current_le_cells_of_local_averages N E bank eligible
    (switchedKernel N K omega) (ordinaryKernel N H L) mass hlocal

/-- The winner partition commutes with conditioning on the literal last
pair. Thus exactly the same E is retained in every selected fiber. -/
theorem cell_lastPair_comm (T : Finset Four) (bank : Finset ℕ)
    (eligible : ℕ → Four → Prop) (switched : Four → ℝ)
    (ordinary : ℕ → Four → ℝ) (c : ℕ) (q : ℕ × ℕ) :
    cell (T.filter (fun t => t.2 = q)) bank eligible switched ordinary c =
      (cell T bank eligible switched ordinary c).filter (fun t => t.2 = q) := by
  ext t
  simp only [cell, Finset.mem_filter]
  tauto

/-- Exact original last-pair disintegration of every winner cell.  The
mask is evaluated once on q; all four labels remain in the winner test. -/
theorem sum_original_cell_eq_lastPair (N : ℕ) (E : ℕ × ℕ → Prop)
    (bank : Finset ℕ) (eligible : ℕ → Four → Prop) (switched : Four → ℝ)
    (ordinary : ℕ → Four → ℝ) (c : ℕ) (f : Four → ℝ) :
    (∑ t ∈ cell (source N E) bank eligible switched ordinary c, f t) =
      ∑ q ∈ U11Original.lastPairs N ((N : ℝ) ^ (19 / 125 : ℝ))
          ((N : ℝ) ^ (59 / 250 : ℝ)) E,
        ∑ p ∈ U11Original.firstPairs N ((N : ℝ) ^ (417 / 5000 : ℝ)) q,
          if chosen bank eligible switched ordinary (p, q) = c then f (p, q) else 0 := by
  rw [cell, Finset.sum_filter]
  exact U11Original.sum_fullSelector N _ _ _ E _

end

end ImbalancedChen.P5Z.U11Adaptive
