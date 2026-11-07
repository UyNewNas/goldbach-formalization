import ImbalancedChen.P5ActualLowerNormalizedBlockGeometry
import ImbalancedChen.Part3PrimeMellinProfileVariation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual remaining HB occurrences have a derived L1 mass. Repeated
positions, real Mobius cutoffs, numerator logs and Mellin phases are kept.
No short-sequence mass estimate is a premise. The independent long-role
selection and full-row-to-two-long reindex remain separate obligations.
-/
namespace ImbalancedChen.Part3.TwoLongActualHBShortMass
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.HBRightClosedDyadicRoles
open ImbalancedChen.P5Z.ActualHBDyadicProductWindow
open ImbalancedChen.P5Z.ActualLowerNormalizedBlockGeometry (blockIntegers)
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b (phase phase_norm)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shortRectangle (bs : ι → Block) : Finset (ι → ℕ) :=
  Fintype.piFinset (fun a => blockIntegers (bs a))

def shortScale (bs : ι → Block) : ℕ := ∏ a, lower (bs a)

def shortProduct (n : ι → ℕ) : ℕ := ∏ a, n a

def shortWeight (bs : ι → Block) (Z : ℝ) (y xi : ι → ℝ)
    (rs : ι → Role) (n : ι → ℕ) : ℂ :=
  ∏ a, actual Z (y a) (rs a) (n a) *
    phase (xi a) ((n a : ℝ) / lower (bs a))

def shortSupport (bs : ι → Block) : Finset ℕ :=
  (shortRectangle bs).image shortProduct

def shortSequence (bs : ι → Block) (Z : ℝ) (y xi : ι → ℝ)
    (rs : ι → Role) (m : ℕ) : ℂ :=
  ∑ n ∈ (shortRectangle bs).filter (fun n => shortProduct n = m),
    shortWeight bs Z y xi rs n

theorem blockIntegers_card (b : Block) : (blockIntegers b).card = lower b := by
  cases b with
  | unit => simp [blockIntegers, lower]
  | dyadic k =>
      simp only [blockIntegers, lower, Nat.card_Ioc, pow_succ]
      omega

theorem shortRectangle_card (bs : ι → Block) :
    (shortRectangle bs).card = shortScale bs := by
  simp [shortRectangle, shortScale, blockIntegers_card]

theorem shortRectangle_bounds (bs : ι → Block) {n : ι → ℕ}
    (hn : n ∈ shortRectangle bs) (a : ι) :
    0 < n a ∧ lower (bs a) ≤ n a ∧ n a ≤ 2 * lower (bs a) := by
  have ho := (ImbalancedChen.P5Z.ActualLowerNormalizedBlockGeometry.mem_blockIntegers
    (bs a) (n a)).mp (Fintype.mem_piFinset.mp hn a)
  have hb := owns_bounds ho
  exact ⟨(lower_pos _).trans_le hb.1, hb⟩

theorem shortProduct_window (bs : ι → Block) {n : ι → ℕ}
    (hn : n ∈ shortRectangle bs) :
    shortScale bs ≤ shortProduct n ∧
      shortProduct n ≤ 2 ^ Fintype.card ι * shortScale bs := by
  constructor
  · exact Finset.prod_le_prod' (fun a _ => (shortRectangle_bounds bs hn a).2.1)
  · calc
      _ ≤ ∏ a, 2 * lower (bs a) :=
        Finset.prod_le_prod' (fun a _ => (shortRectangle_bounds bs hn a).2.2)
      _ = _ := by simp [shortScale, Finset.prod_mul_distrib]

theorem actual_role_norm_le {X : ℝ} (hX : 1 ≤ X) (Z y : ℝ)
    (role : Role) {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ≤ X) :
    ‖actual Z y role n‖ ≤ 1 + Real.log X := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  cases role with
  | mobius => exact (roughMuTrunc_norm_le Z y n).trans (by linarith)
  | one => exact (roughOneSlot_norm_le Z n).trans (by linarith)
  | logarithm =>
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hln := Real.log_nonneg hn1
      have hlnX := Real.log_le_log hnR hnX
      change ‖roughLog Z n‖ ≤ _
      calc
        _ = Real.log (n : ℝ) * ‖roughOneSlot Z n‖ := by
          simp [roughLog, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hln]
        _ ≤ Real.log (n : ℝ) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (roughOneSlot_norm_le Z n) hln
        _ ≤ _ := by linarith

theorem shortWeight_norm_le (bs : ι → Block) (Z : ℝ)
    (y xi : ι → ℝ) (rs : ι → Role) {X : ℝ} (hX : 1 ≤ X)
    (hcap : ∀ a, 2 * (lower (bs a) : ℝ) ≤ X)
    {n : ι → ℕ} (hn : n ∈ shortRectangle bs) :
    ‖shortWeight bs Z y xi rs n‖ ≤ (1 + Real.log X) ^ Fintype.card ι := by
  simp only [shortWeight, norm_prod, norm_mul, phase_norm, mul_one]
  calc
    _ ≤ ∏ _a : ι, (1 + Real.log X) := by
      apply Finset.prod_le_prod (fun a _ => norm_nonneg _)
      intro a ha
      obtain ⟨hpos, hlo, hhi⟩ := shortRectangle_bounds bs hn a
      apply actual_role_norm_le hX Z (y a) (rs a) hpos
      have hhiR : (n a : ℝ) ≤ 2 * (lower (bs a) : ℝ) := by exact_mod_cast hhi
      exact hhiR.trans (hcap a)
    _ = _ := by simp

/-- Exact pushforward retains signed collisions between ordered short
tuples; no absolute values occur in this identity. -/
theorem shortSequence_pushforward (bs : ι → Block) (Z : ℝ)
    (y xi : ι → ℝ) (rs : ι → Role) (f : ℕ → ℂ) :
    (∑ m ∈ shortSupport bs, shortSequence bs Z y xi rs m * f m) =
      ∑ n ∈ shortRectangle bs, shortWeight bs Z y xi rs n * f (shortProduct n) := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := shortRectangle bs) (t := shortSupport bs) (g := shortProduct)
    (fun n hn => Finset.mem_image.mpr ⟨n, hn, rfl⟩)
    (fun n => shortWeight bs Z y xi rs n * f (shortProduct n))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m hm
  rw [shortSequence, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(Finset.mem_filter.mp hn).2]

/-- The short L1 bound is derived from literal role values and exact
right-closed block cardinalities. It is uniform in all real frequencies,
all original rough cutoffs and every real Mobius truncation parameter. -/
theorem shortSequence_mass (bs : ι → Block) (Z : ℝ)
    (y xi : ι → ℝ) (rs : ι → Role) {X : ℝ} (hX : 1 ≤ X)
    (hcap : ∀ a, 2 * (lower (bs a) : ℝ) ≤ X) :
    (∑ m ∈ shortSupport bs, ‖shortSequence bs Z y xi rs m‖) ≤
      (shortScale bs : ℝ) * (1 + Real.log X) ^ Fintype.card ι := by
  calc
    _ ≤ ∑ m ∈ shortSupport bs,
        ∑ n ∈ (shortRectangle bs).filter (fun n => shortProduct n = m),
          ‖shortWeight bs Z y xi rs n‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_sum_le _ _
    _ = ∑ n ∈ shortRectangle bs, ‖shortWeight bs Z y xi rs n‖ :=
      Finset.sum_fiberwise_of_maps_to
        (fun n hn => Finset.mem_image.mpr ⟨n, hn, rfl⟩) _
    _ ≤ ∑ _n ∈ shortRectangle bs, (1 + Real.log X) ^ Fintype.card ι :=
      Finset.sum_le_sum (fun n hn => shortWeight_norm_le bs Z y xi rs hX hcap hn)
    _ = _ := by simp [shortRectangle_card]

/-- Original positions other than the two selected long occurrences.
The subtype preserves repeated numerical values as distinct positions. -/
abbrev ShortPositions {r : ℕ} (i j : Fin r) := {a : Fin r // a ≠ i ∧ a ≠ j}

theorem product_two_positions {r : ℕ} {M : Type*} [CommMonoid M]
    (i j : Fin r) (hij : i ≠ j) (f : Fin r → M) :
    (∏ a, f a) = (f i * f j) * ∏ a : ShortPositions i j, f a.val := by
  have hlong : (Finset.univ.filter (fun a : Fin r => a = i ∨ a = j)) = {i, j} := by
    ext a
    simp
  have hshort := Finset.prod_subtype
    (Finset.univ.filter (fun a : Fin r => ¬(a = i ∨ a = j)))
    (p := fun a : Fin r => a ≠ i ∧ a ≠ j)
    (by intro a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or]) f
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun a : Fin r => a = i ∨ a = j) f, hlong, hshort]
  simp [hij]

/-- The independently existing retained-mode tensor has exactly these
role/log/Mellin factors; the phase conventions agree by commutativity in
the exponential exponent. Whole-group reciprocal logs remain outside. -/
theorem retained_tensor_eq_shortWeight {r : ℕ} (bs : Fin r → Block) (Z : ℝ)
    (y xi : Fin r → ℝ) (rs : Fin r → Role) (n : Fin r → ℕ) :
    ImbalancedChen.P5Z.ActualHBPostModulusLogCutoff.hbSlots Z y rs n *
      ImbalancedChen.P5Z.ActualAllRankOccurrenceFourierBridge.occurrenceMode
        (ImbalancedChen.P5Z.ActualLowerNormalizedBlockGeometry.scales bs) n xi =
      shortWeight bs Z y xi rs n := by
  unfold ImbalancedChen.P5Z.ActualHBPostModulusLogCutoff.hbSlots
    ImbalancedChen.P5Z.ActualAllRankOccurrenceFourierBridge.occurrenceMode shortWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a ha
  congr 1
  unfold phase ImbalancedChen.P5Z.ActualAllRankOccurrenceFourierBridge.logOccurrence
    ImbalancedChen.P5Z.ActualLowerNormalizedBlockGeometry.scales
  congr 1
  push_cast
  ring

/-- Exact selected-occurrence tensor factorization, prior to any norm.
No unordered value set replaces the original ordered positions. -/
theorem shortWeight_split {r : ℕ} (bs : Fin r → Block) (Z : ℝ)
    (y xi : Fin r → ℝ) (rs : Fin r → Role) (n : Fin r → ℕ)
    (i j : Fin r) (hij : i ≠ j) :
    shortWeight bs Z y xi rs n =
      (actual Z (y i) (rs i) (n i) * phase (xi i) ((n i : ℝ)/lower (bs i))) *
      (actual Z (y j) (rs j) (n j) * phase (xi j) ((n j : ℝ)/lower (bs j))) *
      shortWeight (fun a : ShortPositions i j => bs a.val) Z
        (fun a => y a.val) (fun a => xi a.val) (fun a => rs a.val) (fun a => n a.val) :=
  product_two_positions i j hij _

theorem restricted_mem_shortRectangle {r : ℕ} (bs : Fin r → Block)
    {n : Fin r → ℕ}
    (hn : n ∈ ImbalancedChen.P5Z.ActualLowerNormalizedBlockGeometry.rectangle bs)
    (i j : Fin r) :
    (fun a : ShortPositions i j => n a.val) ∈
      shortRectangle (fun a : ShortPositions i j => bs a.val) := by
  apply Fintype.mem_piFinset.mpr
  intro a
  exact Fintype.mem_piFinset.mp hn a.val

end
end ImbalancedChen.Part3.TwoLongActualHBShortMass
