import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral
import ImbalancedChen.SelectedPrefixBoxCap
import ImbalancedChen.VariableEnvelope

/-!
# The original descending129 eighth-prefix real semantics

SOURCE ONLY / UNCOMPILED.  Frozen publication sources read as text:

* `eighth-prefix-descending-independent-20261009.py`, SHA256
  ebbb4830d6e73294715f064f2eb59555a28d502081e7f2fd82b14566bc3e608e;
* its `.tex`, SHA256
  bc17db4fb4bca90011581357b10e4d55b7e8a27d491df85a80135fd5ed4f574b;
* `eighth-family-independent-engine-20261009.py`, SHA256
  13817621f2bec228d53a2c0d4b55d0eb027c0e585aeba811e9128519dd2a2e0e.

They specify rank eight, selected mask129={1,8}, old winner mask6={2,3},
R=D(t2+t3), and M=D(t1+t8)-10^-6.  Their final numerical rule is
gap-weighted Jensen on physical eight-simplices with Jacobian one and ten
affine denominator factors.  It is not a final logarithmic quadrature or
a radial change of variables.  This file proves the exact log-coordinate,
branch/minimum and actual residual-profile dictionary, without claiming
the missing simplex integral certificate or the reported fifteen-cell sum.

The actual sixth cap stays distinct from its raw upper envelope.  The
third-cap approximation hypothesis uses one supplied error margin; no
third cap is defined using a future seventh or eighth coordinate.
-/

namespace ImbalancedChen.P2OriginalDescendingEighthLogSemantics

noncomputable section

open scoped BigOperators
open Classical
open VariableEnvelope
open MathlibNt.SieveTheory

abbrev Point := Fin 8 → ℝ

def eta : ℝ := 1 / 1000000
def firstSix : Finset (Fin 8) := {0, 1, 2, 3, 4, 5}
def firstThree : Finset (Fin 8) := {0, 1, 2}
def winningMask6 : Finset (Fin 8) := {1, 2}
def selectedMask129 : Finset (Fin 8) := {0, 7}

def d (t : Point) : ℝ := t 1 + t 2
def selectedSum (t : Point) : ℝ := t 0 + t 7
def oldRaw (t : Point) : ℝ := C (d t)
def newCap (t : Point) : ℝ := C (selectedSum t) - eta
def total (t : Point) : ℝ := ∑ i, t i

def history3 (t : Point) : ℝ := t 0 + t 1 + 3 * t 2
def history5 (t : Point) : ℝ := t 0 + t 1 + t 2 + t 3 + 3 * t 4
def history7 (t : Point) : ℝ := t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + 3 * t 6

theorem selectedMask129_sum (t : Point) :
    (∑ i ∈ selectedMask129, t i) = selectedSum t := by
  simp [selectedMask129, selectedSum]

theorem winningMask6_sum (t : Point) : (∑ i ∈ winningMask6, t i) = d t := by
  simp [winningMask6, d]

theorem total_explicit (t : Point) :
    total t = t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + t 6 + t 7 := by
  simp [total, Fin.sum_univ_succ] <;> ring

theorem history7_residual (t : Point) : history7 t - total t = 2 * t 6 - t 7 := by
  rw [total_explicit]
  unfold history7
  ring

/-- Every other tent needs only a chosen upper plane.  That plane need
not be the active minimum, exactly as in the frozen branch reconstruction. -/
def chosenPlane (left : Finset (Finset (Fin 8))) (I : Finset (Fin 8))
    (t : Point) : ℝ :=
  if I ∈ left then A (∑ i ∈ I, t i) else C (∑ i ∈ I, t i)

theorem tent_le_chosenPlane (left : Finset (Finset (Fin 8)))
    (I : Finset (Fin 8)) (t : Point) :
    v (∑ i ∈ I, t i) ≤ chosenPlane left I t := by
  rw [v_eq_min]
  unfold chosenPlane
  split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _

def branchValues (slots : Finset (Fin 8)) (t : Point) : Finset ℝ :=
  insert (B (t 2)) ((slots.powerset.filter Finset.Nonempty).image
    (fun I => v (∑ i ∈ I, t i)))

theorem branchValues_nonempty (slots : Finset (Fin 8)) (t : Point) :
    (branchValues slots t).Nonempty := ⟨B (t 2), by simp [branchValues]⟩

def rawCap (slots : Finset (Fin 8)) (t : Point) : ℝ :=
  (branchValues slots t).max' (branchValues_nonempty slots t)

def BranchGuards (left : Finset (Finset (Fin 8))) (t : Point) : Prop :=
  mu < d t ∧ B (t 2) ≤ oldRaw t ∧
    ∀ I ⊆ firstSix, I.Nonempty → chosenPlane left I t ≤ oldRaw t

theorem tent_le_oldRaw {left : Finset (Finset (Fin 8))} {t : Point}
    (h : BranchGuards left t) (I : Finset (Fin 8))
    (hI : I ⊆ firstSix) (hne : I.Nonempty) : v (∑ i ∈ I, t i) ≤ oldRaw t :=
  (tent_le_chosenPlane left I t).trans (h.2.2 I hI hne)

/-- All-subset old envelopes are identified from the literal physical
plane inequalities, rather than asserted to equal the desired winner. -/
theorem rawCap_eq_oldRaw {left : Finset (Finset (Fin 8))} {t : Point}
    (h : BranchGuards left t) (slots : Finset (Fin 8))
    (hslots : slots ⊆ firstSix) (hwin : winningMask6 ⊆ slots) :
    rawCap slots t = oldRaw t := by
  have hupper : rawCap slots t ≤ oldRaw t := by
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_insert.mp hy with hy | hy
    · simpa only [hy] using h.2.1
    · obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hy
      have hi := Finset.mem_filter.mp hI
      exact tent_le_oldRaw h I ((Finset.mem_powerset.mp hi.1).trans hslots) hi.2
  have hvalue : v (∑ i ∈ winningMask6, t i) = oldRaw t := by
    rw [winningMask6_sum, v_eq_C h.1.le]
    rfl
  have hmember : oldRaw t ∈ branchValues slots t := by
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨winningMask6, ?_, hvalue⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hwin, by simp [winningMask6]⟩
  exact le_antisymm hupper (Finset.le_max' _ _ hmember)

theorem original_raw_third_and_sixth {left : Finset (Finset (Fin 8))} {t : Point}
    (h : BranchGuards left t) :
    rawCap firstThree t = oldRaw t ∧ rawCap firstSix t = oldRaw t := by
  constructor
  · exact rawCap_eq_oldRaw h firstThree (by decide) (by decide)
  · exact rawCap_eq_oldRaw h firstSix (fun _ hx => hx) (by decide)

/-- The same winner is the existing six-branch third envelope. -/
theorem six_eq_oldRaw {left : Finset (Finset (Fin 8))} {t : Point}
    (h : BranchGuards left t) : six (t 0) (t 1) (t 2) = oldRaw t := by
  have h0 : v (t 0) ≤ oldRaw t := by
    simpa using tent_le_oldRaw h {0} (by decide) (by simp)
  have h01 : v (t 0 + t 1) ≤ oldRaw t := by
    simpa using tent_le_oldRaw h {0, 1} (by decide) (by simp)
  have h012 : v (t 0 + t 1 + t 2) ≤ oldRaw t := by
    simpa [add_assoc] using tent_le_oldRaw h {0, 1, 2} (by decide) (by simp)
  have h02 : v (t 0 + t 2) ≤ oldRaw t := by
    simpa using tent_le_oldRaw h {0, 2} (by decide) (by simp)
  have h12 : v (t 1 + t 2) = oldRaw t := v_eq_C h.1.le
  apply le_antisymm
  · exact max_le h0 (max_le h01 (max_le h012 (max_le h.2.1 (max_le h02 h12.le))))
  · rw [← h12]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))))

theorem literal_third_envelope_eq {left : Finset (Finset (Fin 8))} {t : Point}
    (h : BranchGuards left t) (hord : Ordered (t 0) (t 1) (t 2)) :
    original (t 0) (t 1) (t 2) = oldRaw t := by
  rw [original_eq_six hord, six_eq_oldRaw h]

/-- The forbidden gap separates distinct left/right branch patterns. -/
theorem branch_forbidden_gap (t : Point) :
    d t - (25 / 32 - 3 * d t) = 4 * (d t - mu) := by
  dsimp [mu]
  ring

theorem chosen_planes_incompatible {t : Point} (hd : mu < d t) (s : ℝ) :
    ¬ (A s ≤ oldRaw t ∧ C s ≤ oldRaw t) := by
  dsimp [A, C, oldRaw, mu] at *
  rintro ⟨ha, hc⟩
  linarith

/-- The positive ascending-license row is precisely the descending half
selector; the active descending license retains its fixed eta buffer. -/
theorem descending_selector (t : Point) :
    0 < A (selectedSum t) - eta - newCap t ↔ mu < selectedSum t := by
  dsimp [A, C, eta, newCap, mu]
  constructor <;> linarith

theorem selected129_license {t : Point} (ht : mu < selectedSum t) :
    v (∑ i ∈ selectedMask129, t i) - newCap t = eta ∧
      newCap t < v (∑ i ∈ selectedMask129, t i) := by
  rw [selectedMask129_sum, v_eq_C ht.le]
  dsimp [newCap, eta]
  constructor <;> linarith

/-- A supplied third-prefix approximation is enough for all retained
history tests.  Its definition is not allowed to depend on these margins. -/
theorem histories_pass_of_third_approximation (t : Point) (eps lambda3 lambda6 : ℝ)
    (happrox : oldRaw t - eps < lambda3) (hparent : lambda3 ≤ lambda6)
    (h3 : history3 t + eps ≤ oldRaw t)
    (h5 : history5 t + eps ≤ oldRaw t)
    (h7 : history7 t + eps ≤ oldRaw t) :
    history3 t < lambda6 ∧ history5 t < lambda6 ∧ history7 t < lambda6 := by
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The frozen compact eighth cutoff follows from the actual retained
odd histories and the raw first-subset branch; it is not an assumed
numerical lower bound on an unexamined tail. -/
theorem eighth_compact_cutoff (t : Point)
    (hfirst : t 0 < mu) (h10 : t 1 ≤ t 0) (h32 : t 3 ≤ t 2)
    (h54 : t 5 ≤ t 4) (hA : A (t 0) ≤ oldRaw t)
    (h3 : history3 t < oldRaw t) (h5 : history5 t < oldRaw t)
    (h7 : history7 t < oldRaw t) (hraise : oldRaw t < newCap t)
    (hterminal : newCap t < total t + 3 * t 7) :
    (53 / 13824 : ℝ) < t 7 := by
  have hRQ : oldRaw t < total t + 3 * t 7 := hraise.trans hterminal
  have h7Q := h7.trans hRQ
  have h5Q := h5.trans hRQ
  have h3Q := h3.trans hRQ
  rw [total_explicit] at h7Q h5Q h3Q
  dsimp only [history7] at h7Q
  dsimp only [history5] at h5Q
  dsimp only [history3] at h3Q
  have h6 : t 6 < 2 * t 7 := by linarith only [h7Q]
  have h4 : t 4 < 6 * t 7 := by linarith only [h5Q, h54, h6]
  have h2 : t 2 < 18 * t 7 := by linarith only [h3Q, h32, h54, h4, h6]
  have hQ : total t + 3 * t 7 < 2 * t 0 + 54 * t 7 := by
    rw [total_explicit]
    linarith only [h10, h32, h54, h2, h4, h6]
  have hAQ : A (t 0) < 2 * t 0 + 54 * t 7 := hA.trans_lt (hRQ.trans hQ)
  dsimp only [A, mu] at hAQ hfirst
  linarith only [hAQ, hfirst]

/-- The true parent passes rank seven before the rank-eight residual is
formed.  Its residual, the raw comparison residual and the new residual
all belong to the actual initial upper-density range. -/
theorem residual_interval_chain (t : Point) (lambda6 : ℝ)
    (hr : 0 < t 7) (horder : t 7 < t 6) (h7 : history7 t < lambda6)
    (hparent : lambda6 ≤ oldRaw t) (hraise : oldRaw t < newCap t)
    (hterminal : newCap t - total t < 3 * t 7) :
    t 7 < lambda6 - total t ∧
      lambda6 - total t ≤ oldRaw t - total t ∧
      oldRaw t - total t < newCap t - total t ∧
      newCap t - total t < 3 * t 7 := by
  have hh := history7_residual t
  exact ⟨by linarith, by linarith, by linarith, hterminal⟩

def actualResidualProfile (lambda : ℝ) (t : Point) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / t 7) *
    suzukiContinuousUpperFactor ((lambda - total t) / t 7)

def physicalKernel (t : Point) : ℝ :=
  primeBoxInitialSavingProfile (oldRaw t) (newCap t) t * ∏ i, 1 / t i

theorem primeBoxInitialSavingProfile_eq_difference (old new : ℝ) (t : Point)
    (ho : old - total t ≠ 0) (hn : new - total t ≠ 0) :
    primeBoxInitialSavingProfile old new t =
      4 / (old - total t) - 4 / (new - total t) := by
  unfold primeBoxInitialSavingProfile
  change 4 * (new - old) / ((old - total t) * (new - total t)) = _
  field_simp [ho, hn]
  ring

/-- Identification uses the already proved actual Rosser limit, rather
than an assumed raw profile equality. -/
theorem actualResidualProfile_eq_initial (lambda : ℝ) (t : Point)
    (hr : 0 < t 7) (hlo : t 7 < lambda - total t)
    (hhi : lambda - total t ≤ 3 * t 7) :
    actualResidualProfile lambda t = 4 / (lambda - total t) := by
  exact normalized_suzukiUpperFactor_initial (lambda - total t) (t 7) hr hlo hhi

/-- Conservative comparison against the actual sixth parent.  The raw
envelope is used only as an upper bound on that parent; it is never
substituted as the actual finite old cap. -/
theorem physicalKernel_le_actual_parent_saving (t : Point) (lambda6 : ℝ)
    (hpos : ∀ i, 0 < t i) (horder : t 7 < t 6)
    (h7 : history7 t < lambda6) (hparent : lambda6 ≤ oldRaw t)
    (hraise : oldRaw t < newCap t) (hterminal : newCap t - total t < 3 * t 7) :
    physicalKernel t ≤
      (actualResidualProfile lambda6 t - actualResidualProfile (newCap t) t) *
        ∏ i, 1 / t i := by
  obtain ⟨hlo, hpar, hnew, hhi⟩ := residual_interval_chain t lambda6 (hpos 7)
    horder h7 hparent hraise hterminal
  have hol : 0 < lambda6 - total t := (hpos 7).trans hlo
  have hor : 0 < oldRaw t - total t := hol.trans_le hpar
  have hnr : 0 < newCap t - total t := hor.trans hnew
  rw [actualResidualProfile_eq_initial lambda6 t (hpos 7) hlo (by linarith),
    actualResidualProfile_eq_initial (newCap t) t (hpos 7) (by linarith) hhi.le]
  unfold physicalKernel
  rw [primeBoxInitialSavingProfile_eq_difference (oldRaw t) (newCap t) t hor.ne' hnr.ne']
  apply mul_le_mul_of_nonneg_right
  · apply sub_le_sub_right
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) hol hpar
  · exact Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hpos i)).le)

/-- Literal ten-factor physical kernel: no factorial and no Chen quarter
appear in the ordered eight-dimensional density. -/
theorem physicalKernel_eq_literal (t : Point) :
    physicalKernel t =
      4 * (newCap t - oldRaw t) /
        ((oldRaw t - total t) * (newCap t - total t) * ∏ i, t i) := by
  simp only [physicalKernel, primeBoxInitialSavingProfile, total, one_div,
    Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exactly the ten affine factors in the frozen simplex engine. -/
def denominatorFactors (t : Point) : Fin 10 → ℝ :=
  ![oldRaw t - total t, newCap t - total t,
    t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7]

theorem denominatorFactors_product (t : Point) :
    (∏ j, denominatorFactors t j) =
      (oldRaw t - total t) * (newCap t - total t) * ∏ i, t i := by
  simp [denominatorFactors, Fin.prod_univ_succ] <;> ring

theorem denominatorFactors_pos (t : Point) (lambda6 : ℝ)
    (hpos : ∀ i, 0 < t i) (horder : t 7 < t 6)
    (h7 : history7 t < lambda6) (hparent : lambda6 ≤ oldRaw t)
    (hraise : oldRaw t < newCap t) (hterminal : newCap t - total t < 3 * t 7) :
    ∀ j, 0 < denominatorFactors t j := by
  obtain ⟨hlo, hpar, hnew, _⟩ := residual_interval_chain t lambda6 (hpos 7)
    horder h7 hparent hraise hterminal
  have ho : 0 < oldRaw t - total t := ((hpos 7).trans hlo).trans_le hpar
  have hn : 0 < newCap t - total t := ho.trans hnew
  intro j
  fin_cases j
  all_goals simp only [denominatorFactors, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ]
  · exact ho
  · exact hn
  all_goals exact hpos _

theorem physicalKernel_positive (t : Point) (lambda6 : ℝ)
    (hpos : ∀ i, 0 < t i) (horder : t 7 < t 6)
    (h7 : history7 t < lambda6) (hparent : lambda6 ≤ oldRaw t)
    (hraise : oldRaw t < newCap t) (hterminal : newCap t - total t < 3 * t 7) :
    0 < physicalKernel t := by
  rw [physicalKernel_eq_literal, ← denominatorFactors_product]
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hraise))
    (Finset.prod_pos (fun j _ => denominatorFactors_pos t lambda6 hpos horder
      h7 hparent hraise hterminal j))

/-- The real proof chain from reconstructed branch rows and a supplied
causal third-prefix approximation to the conservative actual-parent
saving.  Its premises contain no saving inequality or reported total. -/
theorem original_descending_profile_sound
    (left : Finset (Finset (Fin 8))) (t : Point) (eps lambda3 lambda6 : ℝ)
    (hbranches : BranchGuards left t) (hpos : ∀ i, 0 < t i)
    (horder : t 7 < t 6) (happrox : oldRaw t - eps < lambda3)
    (hparentLower : lambda3 ≤ lambda6) (hparentUpper : lambda6 ≤ rawCap firstSix t)
    (h3 : history3 t + eps ≤ oldRaw t) (h5 : history5 t + eps ≤ oldRaw t)
    (h7 : history7 t + eps ≤ oldRaw t) (hraise : oldRaw t < newCap t)
    (hterminal : newCap t - total t < 3 * t 7) :
    physicalKernel t ≤
      (actualResidualProfile lambda6 t - actualResidualProfile (newCap t) t) *
        ∏ i, 1 / t i := by
  have hpasses := histories_pass_of_third_approximation t eps lambda3 lambda6
    happrox hparentLower h3 h5 h7
  have hraw := (original_raw_third_and_sixth hbranches).2
  rw [hraw] at hparentUpper
  exact physicalKernel_le_actual_parent_saving t lambda6 hpos horder hpasses.2.2
    hparentUpper hraise hterminal

/-- Exact log_N coordinate dictionary for the actual eight-prime product. -/
theorem actual_history_profile_dictionary (N : ℕ) (p : Fin 8 → ℕ)
    (hp : ∀ i, 0 < p i) :
    primeBoxInitialSavingProfile (oldRaw (actualPrimeTupleLog N p))
        (newCap (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p) =
      4 * (newCap (actualPrimeTupleLog N p) - oldRaw (actualPrimeTupleLog N p)) /
        ((oldRaw (actualPrimeTupleLog N p) - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ)) *
          (newCap (actualPrimeTupleLog N p) - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ))) := by
  simp only [primeBoxInitialSavingProfile, actualPrimeTupleLog_sum_prod p hp]

end

end ImbalancedChen.P2OriginalDescendingEighthLogSemantics
