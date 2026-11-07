import ImbalancedChen.Part3OriginalSamePsiS1Remainder
import ImbalancedChen.Part3MediumActualPreliminaryCauchy
import ImbalancedChen.Part3ActualFixedFeatureCountGeometry
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The six-coordinate dyadic atlas and its physical ownership are reused
from MediumGlobalDyadicOwnership / MediumOwnedCanonicalReindex. This
file supplies their missing S1 FixedBlock instances, with lambdaTrim,
the original atom and the actual common paperPsi. No new block cover
or unrelated Lambda-equality premise is requested.

The smooth q support is longer than a single FixedBlock q interval.
It is split into three disjoint physical intervals at Q and 2Q.
The frequency-only fields required by FixedBlock are set to the inert
positive singleton; S1 is pre-Poisson and never reads those fields.
No E3 frequency-carrier equality is claimed.
-/

namespace ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
noncomputable section
open Classical Finset
open scoped BigOperators FourierTransform
open OriginalSamePsiS1Remainder OriginalPaperPsiCoprimeCount
open OriginalMediumPhysicalE3Block OriginalMediumS1CommonMCount
open OriginalMediumS1WeightedRemainder OriginalMediumS1SeparatedDivisorMean
open OriginalMediumS1ActualCoefficientBinding
open MediumGlobalDyadicOwnership20261028 MediumOwnedCanonicalReindex20261028
open MediumCanonicalFixedBlock20261028 MediumActualPreliminaryCauchy20261028
open MediumInstalledFactorChoiceMap20261028 MediumInstalledSplitConverse20261028
open OriginalMediumDoubleLambdaColorWindows20261028 OriginalGevreyFinalPsi20261028
open OriginalGevreyPoissonPacket20261028

def keyD (k : Key) : ℝ := ((2 : ℕ) ^ k.d : ℕ)
def keyR (k : Key) : ℝ := ((2 : ℕ) ^ k.w : ℕ)
def keyY (atom : MediumAtom) (k : Key) : ℝ := atom.Q1 * keyD k

def activeD (atom : MediumAtom) (k : Key) : Finset ℕ :=
  (dyadicWindow k.d).filter (fun d => d.Coprime atom.residue.natAbs)

/-- Actual trimmed coefficients are weighted physical ownership fibres. -/
theorem lambdaTrim_eq_owned_physical_slice (atom : MediumAtom) (z y : ℝ)
    (k : Key) (d w : ℕ) (hd : d ∈ dyadicWindow k.d) :
    lambdaTrim atom z y k d w =
      ∑ q ∈ ownedSlice atom z y k d w, atom.gamma2 q.1 * atom.gamma3 q.2 := by
  rw [sum_ownedSlice_eq_trimmedChoices atom z y k d w hd]
  rfl

theorem lambdaTrim_norm_le_tau {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (d w : ℕ)
    (hA : MediumAdmissible b σ κ c0 atom) :
    ‖lambdaTrim atom z y k d w‖ ≤ tauR (d * w) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hγ2, hγ3⟩ := hA
  unfold lambdaTrim
  calc
    _ ≤ ∑ p ∈ trimmedChoices atom z y k d w,
        ‖((fixedBlock k d).factorData atom z).term p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ trimmedChoices atom z y k d w, (1 : ℝ) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨_, _, ha⟩ := choice_products (mem_filter.mp hp).1
      change p.u * p.s ∈ factorCarrier atom.Q2 ∧
        p.v * p.t ∈ factorCarrier atom.Q3 ∧ _ at ha
      change ‖atom.gamma2 (p.u * p.s) * atom.gamma3 (p.v * p.t)‖ ≤ 1
      rw [norm_mul]
      simpa using mul_le_mul (hγ2 _ ha.1).1 (hγ3 _ ha.2.1).1
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = ((trimmedChoices atom z y k d w).card : ℝ) := by simp
    _ ≤ ((((fixedBlock k d).factorData atom z).choices d w).card : ℝ) := by
      exact_mod_cast card_le_card (filter_subset _ _)
    _ ≤ _ := by exact_mod_cast choices_card_le_divisors (fixedBlock k d) atom z w

theorem lambdaTrim_support_coprime (atom : MediumAtom) (z y : ℝ)
    (k : Key) (d w : ℕ) (hn : lambdaTrim atom z y k d w ≠ 0) : d.Coprime w := by
  by_contra hc
  apply hn
  unfold lambdaTrim
  apply sum_eq_zero
  intro p hp
  exact False.elim (hc (choice_smooth_product_coprime_rough_product
    (fixedBlock k d) atom z (mem_filter.mp hp).1))

/-- Primitive gamma support makes every nonprimitive d fibre zero.
It is therefore removed by an equality, rather than by a new licence. -/
theorem lambdaTrim_zero_of_nonprimitive {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (d w : ℕ)
    (hA : MediumAdmissible b σ κ c0 atom)
    (hc : ¬ d.Coprime atom.residue.natAbs) : lambdaTrim atom z y k d w = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hγ2, hγ3⟩ := hA
  unfold lambdaTrim
  apply sum_eq_zero
  intro p hp
  obtain ⟨hd, _, ha⟩ := choice_products (mem_filter.mp hp).1
  change p.u * p.s ∈ factorCarrier atom.Q2 ∧
    p.v * p.t ∈ factorCarrier atom.Q3 ∧ _ at ha
  change atom.gamma2 (p.u * p.s) * atom.gamma3 (p.v * p.t) = 0
  by_contra hn
  obtain ⟨h2, h3⟩ := mul_ne_zero_iff.mp hn
  have hs : p.s.Coprime atom.residue.natAbs :=
    Nat.Coprime.of_dvd_left (show p.s ∣ p.u * p.s from ⟨p.u, by ring⟩)
      ((hγ2 _ ha.1).2 h2)
  have ht : p.t.Coprime atom.residue.natAbs :=
    Nat.Coprime.of_dvd_left (show p.t ∣ p.v * p.t from ⟨p.v, by ring⟩)
      ((hγ3 _ ha.2.1).2 h3)
  exact hc (hd ▸ Nat.coprime_mul_iff_left.mpr ⟨hs, ht⟩)

theorem lambdaTrim_zero_outside_rough_window (atom : MediumAtom) (z y : ℝ)
    (k : Key) (d w : ℕ) (hw : w ∉ dyadicWindow k.w) :
    lambdaTrim atom z y k d w = 0 := by
  unfold lambdaTrim
  apply sum_eq_zero
  intro p hp
  obtain ⟨_, hpw, ha⟩ := choice_products (mem_filter.mp hp).1
  have hwin : p.u * p.v ∈ dyadicWindow k.w := by
    simpa only [dyadicWindow_eq_Icc] using ha.2.2
  exact False.elim (hw (hpw ▸ hwin))

/-- The exact d summation from the preliminary row loses no nonzero term. -/
theorem sum_d_lambda_pair_eq_active {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (r s : ℕ) (f : ℕ → ℂ)
    (hA : MediumAdmissible b σ κ c0 atom) :
    (∑ d ∈ dyadicWindow k.d,
      lambdaTrim atom z y k d r * star (lambdaTrim atom z y k d s) * f d) =
    ∑ d ∈ activeD atom k,
      lambdaTrim atom z y k d r * star (lambdaTrim atom z y k d s) * f d := by
  unfold activeD
  rw [sum_filter]
  apply sum_congr rfl
  intro d hd
  by_cases hc : d.Coprime atom.residue.natAbs
  · simp [hc]
  · simp [hc, lambdaTrim_zero_of_nonprimitive atom z y k d r hA hc]

def qLo (Q : ℝ) : Fin 3 → ℕ := ![Nat.ceil (Q / 2), Nat.floor Q + 1, Nat.floor (2 * Q) + 1]
def qHi (Q : ℝ) : Fin 3 → ℕ := ![Nat.floor Q, Nat.floor (2 * Q), Nat.floor (5 * Q / 2)]
def qScale (Q : ℝ) : Fin 3 → ℝ := ![Q / 2, Q, 2 * Q]
def qPiece (Q : ℝ) (j : Fin 3) : Finset ℕ := Icc (qLo Q j) (qHi Q j)

theorem qPiece_geometry {Q : ℝ} (hQ : 1 ≤ Q) (j : Fin 3) :
    0 < qScale Q j ∧ Q / 2 ≤ qScale Q j ∧ qScale Q j ≤ 2 * Q ∧
      qScale Q j ≤ (qLo Q j : ℝ) ∧ (qHi Q j : ℝ) ≤ 2 * qScale Q j := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hceil := Nat.le_ceil (Q / 2)
  have hfloorQ := Nat.floor_le hQ0.le
  have hfloor2Q := Nat.floor_le (show 0 ≤ 2 * Q by positivity)
  have hfloor5Q := Nat.floor_le (show 0 ≤ 5 * Q / 2 by positivity)
  have hnextQ := Nat.lt_floor_add_one Q
  have hnext2Q := Nat.lt_floor_add_one (2 * Q)
  fin_cases j
  · change 0 < Q / 2 ∧ Q / 2 ≤ Q / 2 ∧ Q / 2 ≤ 2 * Q ∧
      Q / 2 ≤ (Nat.ceil (Q / 2) : ℝ) ∧ (Nat.floor Q : ℝ) ≤ 2 * (Q / 2)
    repeat' constructor <;> linarith
  · change 0 < Q ∧ Q / 2 ≤ Q ∧ Q ≤ 2 * Q ∧
      Q ≤ (Nat.floor Q + 1 : ℕ) ∧ (Nat.floor (2 * Q) : ℝ) ≤ 2 * Q
    push_cast
    repeat' constructor <;> linarith
  · change 0 < 2 * Q ∧ Q / 2 ≤ 2 * Q ∧ 2 * Q ≤ 2 * Q ∧
      2 * Q ≤ (Nat.floor (2 * Q) + 1 : ℕ) ∧
        (Nat.floor (5 * Q / 2) : ℝ) ≤ 2 * (2 * Q)
    push_cast
    repeat' constructor <;> linarith

/-- Endpoints Q and 2Q belong to the lower piece only. Every natural
point of the actual paper profile carrier is counted exactly once. -/
theorem qPiece_unique_cover {Q : ℝ} (hQ : 1 ≤ Q) (q : ℕ) :
    (q ∈ paperPsiNaturalCarrier Q) ↔ ∃! j : Fin 3, q ∈ qPiece Q j := by
  have hceil : Nat.ceil (Q / 2) ≤ Nat.floor Q + 1 := by
    apply Nat.ceil_le.mpr
    have hnext := Nat.lt_floor_add_one Q
    push_cast
    linarith
  have hfloor : Nat.floor Q ≤ Nat.floor (2 * Q) := Nat.floor_mono (by linarith)
  have hfloor' : Nat.floor (2 * Q) ≤ Nat.floor (5 * Q / 2) := Nat.floor_mono (by linarith)
  constructor
  · intro hq
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hq
    by_cases h0 : q ≤ Nat.floor Q
    · refine ⟨0, ?_, ?_⟩
      · simpa [qPiece, qLo, qHi] using mem_Icc.mpr ⟨hlo, h0⟩
      · intro j hj
        fin_cases j <;> simp [qPiece, qLo, qHi, mem_Icc] at hj ⊢ <;> omega
    · by_cases h1 : q ≤ Nat.floor (2 * Q)
      · refine ⟨1, ?_, ?_⟩
        · simpa [qPiece, qLo, qHi] using mem_Icc.mpr ⟨by omega, h1⟩
        · intro j hj
          fin_cases j <;> simp [qPiece, qLo, qHi, mem_Icc] at hj ⊢ <;> omega
      · refine ⟨2, ?_, ?_⟩
        · simpa [qPiece, qLo, qHi] using mem_Icc.mpr ⟨by omega, hhi⟩
        · intro j hj
          fin_cases j <;> simp [qPiece, qLo, qHi, mem_Icc] at hj ⊢ <;> omega
  · rintro ⟨j, hj, _⟩
    fin_cases j <;> simp [qPiece, qLo, qHi, mem_Icc] at hj <;>
      apply mem_Icc.mpr <;> omega

theorem sum_qPieces {Q : ℝ} (hQ : 1 ≤ Q) (f : ℕ → ℂ) :
    (∑ j : Fin 3, ∑ q ∈ qPiece Q j, f q) =
      ∑ q ∈ paperPsiNaturalCarrier Q, f q := by
  have hsub (j : Fin 3) : qPiece Q j ⊆ paperPsiNaturalCarrier Q := by
    intro q hq
    exact (qPiece_unique_cover hQ q).mpr ⟨j, hq, fun j' hj' => by
      fin_cases j <;> fin_cases j' <;> simp [qPiece, qLo, qHi, mem_Icc] at * <;> omega⟩
  calc
    _ = ∑ j : Fin 3, ∑ q ∈ paperPsiNaturalCarrier Q,
        if q ∈ qPiece Q j then f q else 0 := by
      apply sum_congr rfl
      intro j _
      rw [← sum_filter]
      congr 1
      ext q
      simp only [mem_filter]
      exact ⟨fun h => ⟨hsub j h, h⟩, fun h => h.2⟩
    _ = ∑ q ∈ paperPsiNaturalCarrier Q, ∑ j : Fin 3,
        if q ∈ qPiece Q j then f q else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro q hq
      obtain ⟨j, hj, hu⟩ := (qPiece_unique_cover hQ q).mp hq
      rw [sum_eq_single j]
      · simp [hj]
      · intro j' _ hne
        exact if_neg (fun hmem => hne (hu j' hmem))
      · simp

def atlasBlock {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ)
    (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) : FixedBlock := by
  obtain ⟨hdwin, hdc⟩ := mem_filter.mp hd
  obtain ⟨hdlo, hdhi⟩ := mem_Ico.mp hdwin
  have hD : 0 < (2 : ℕ) ^ k.d := pow_pos (by norm_num) _
  have hR : 0 < (2 : ℕ) ^ k.w := pow_pos (by norm_num) _
  have hq := qPiece_geometry hA.2.2.1 j
  refine { atom := atom, d := d, D := keyD k, roughLength := keyR k,
    q0 := qScale atom.Q1 j, qLo := qLo atom.Q1 j, qHi := qHi atom.Q1 j,
    hLo := 1, hHi := 1, separationOrder := 0,
    lambdaD := lambdaTrim atom z y k d,
    lambdaD_support_coprime := lambdaTrim_support_coprime atom z y k d,
    psi0 := fun x => (paperPsi x : ℂ), psi0_support := paperPsi_complex_support,
    psiHat0 := fun ξ => 𝓕 (fun x : ℝ => (paperPsi x : ℂ)) ξ,
    U_pos := lt_of_lt_of_le zero_lt_one hA.1,
    V_pos := lt_of_lt_of_le zero_lt_one hA.2.1,
    Q_pos := lt_of_lt_of_le zero_lt_one hA.2.2.1,
    D_pos := by exact_mod_cast hD,
    rough_pos := by exact_mod_cast hR,
    d_pos := lt_of_lt_of_le hD hdlo,
    d_coprime_residue := hdc,
    d_window_lo := by exact_mod_cast hdlo,
    d_window_hi := ?_, q0_pos := hq.1, q0_from_Q_lo := hq.2.1,
    q0_from_Q_hi := hq.2.2.1, qLo_block := hq.2.2.2.1,
    qHi_block := hq.2.2.2.2, h_one_sign := Or.inr (by norm_num) }
  have hcast : (d : ℝ) < ((2 : ℕ) ^ (k.d + 1) : ℕ) := by exact_mod_cast hdhi
  simpa only [keyD, pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hcast.le

@[simp] theorem atlasBlock_lambda {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) (w : ℕ) :
    (atlasBlock atom z y k hA j d hd).lambdaD w = lambdaTrim atom z y k d w := rfl

@[simp] theorem atlasBlock_qCarrier {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) :
    (atlasBlock atom z y k hA j d hd).qCarrier = qPiece atom.Q1 j := rfl

theorem atlasBlock_samePsi_kernel_bound {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) :
    let B := atlasBlock atom z y k hA j d hd
    S1DivisorKernel B ≤
      4 * (2 * atom.U) ^ 2 * P5Z.RoughSquareWeightedBudget.logBudget
        (OriginalMediumS1ActualCoefficientBinding.physicalCap B) ^ 2 *
        (tauR d ^ 3 / (d : ℝ) ^ 2) *
        ((1 + Real.log (qCap B : ℝ)) ^ 4 / qScale atom.Q1 j) *
        (1 + Real.log (roughCap B : ℝ)) ^ 16 := by
  let B := atlasBlock atom z y k hA j d hd
  apply S1DivisorKernel_le_log B
    (OriginalMediumS1ActualCoefficientBinding.physicalCap B) (2 * atom.U)
    (qCap B : ℝ) (roughCap B : ℝ)
  · exact mul_nonneg (by norm_num) (zero_le_one.trans hA.1)
  · exact_mod_cast le_max_left 1 B.qHi
  · exact_mod_cast le_max_left 1 (Nat.floor (2 * B.roughLength))
  · exact actual_qCarrier_cap B
  · exact actual_wCarrier_cap B
  · intro q _
    exact paperPsi_complex_norm_le_one _
  · intro r _
    exact lambdaTrim_norm_le_tau atom z y k d r hA
  · intro q _ r _
    exact actual_alpha_mean_bound B hA q r
  · intro q hq r hr
    exact actual_physical_modulus_cap B hq hr

end
end ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
