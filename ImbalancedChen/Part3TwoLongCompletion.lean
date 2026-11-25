import ImbalancedChen.Part3CompletedReciprocalWeil

/-!
# The two-long discrepancy on primitive residue classes

The center is the exact product of the two primitive masses. Adding a
constant to either residue profile leaves the discrepancy invariant, so
both zero Fourier axes cancel before taking absolute values.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators

/-- The representative of the product target is a unit modulo `q`. -/
def twoLongResidueError {q : ℕ} [NeZero q] (b : (ZMod q)ˣ)
    (f g : ZMod q → ℂ) : ℂ :=
  (∑ u : (ZMod q)ˣ, f (u : ZMod q) * g (↑(b * u⁻¹) : ZMod q)) -
    (∑ u : (ZMod q)ˣ, f (u : ZMod q)) * (∑ u : (ZMod q)ˣ, g (u : ZMod q)) /
      (q.totient : ℂ)

private theorem sum_product_target {q : ℕ} [NeZero q] (b : (ZMod q)ˣ)
    (g : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, g (↑(b * u⁻¹) : ZMod q)) = ∑ u : (ZMod q)ˣ, g (u : ZMod q) :=
  Equiv.sum_comp ((Equiv.inv ((ZMod q)ˣ)).trans (Equiv.mulLeft b)) (fun u => g u)

/-- The first Fourier axis cancels against the precise primitive center. -/
theorem twoLongResidueError_add_const_left {q : ℕ} [NeZero q] (b : (ZMod q)ˣ)
    (f g : ZMod q → ℂ) (c : ℂ) :
    twoLongResidueError b (fun u => f u + c) g = twoLongResidueError b f g := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp only [twoLongResidueError, add_mul, sum_add_distrib,
    sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  rw [← mul_sum, sum_product_target]
  field_simp
  ring

/-- The second Fourier axis cancels against the same center. -/
theorem twoLongResidueError_add_const_right {q : ℕ} [NeZero q] (b : (ZMod q)ˣ)
    (f g : ZMod q → ℂ) (c : ℂ) :
    twoLongResidueError b f (fun u => g u + c) = twoLongResidueError b f g := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp only [twoLongResidueError, mul_add, sum_add_distrib, ← sum_mul _ _ c,
    sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
  field_simp
  ring

private def longMode {q : ℕ} [NeZero q] (j : ℤ) (u : ZMod q) : ℂ :=
  ZMod.stdAddChar ((j : ZMod q) * u)

private theorem longMode_norm {q : ℕ} [NeZero q] (j : ℤ) (u : ZMod q) :
    ‖longMode j u‖ = 1 := stdAddChar_norm _

private theorem longMode_sum_units {q : ℕ} [NeZero q] (j : ℤ) :
    (∑ u : (ZMod q)ˣ, longMode j (u : ZMod q)) = completeKloosterman q 0 j := by
  rw [completeKloosterman_eq_sum_units]
  simp only [zero_mul, zero_add, longMode]
  exact (Equiv.sum_comp (Equiv.inv ((ZMod q)ˣ))
    (fun u => ZMod.stdAddChar ((j : ZMod q) * (u : ZMod q)))).symm

private theorem longMode_product_sum_units {q : ℕ} [NeZero q] (b : (ZMod q)ˣ) (j k : ℤ) :
    (∑ u : (ZMod q)ˣ, longMode j (u : ZMod q) * longMode k (↑(b * u⁻¹) : ZMod q)) =
      completeKloosterman q (j : ZMod q) (((b : ZMod q).val : ℤ) * k) := by
  rw [completeKloosterman_eq_sum_units]
  apply sum_congr rfl
  intro u _
  simp only [longMode, ← AddChar.map_add_eq_mul, Units.val_mul, Int.cast_mul,
    Int.cast_natCast, ZMod.natCast_zmod_val, mul_assoc]
  congr 1
  ring

/-- The completed residue kernel at one pair of Fourier frequencies. -/
theorem twoLongResidueError_modes {q : ℕ} [NeZero q] (b : (ZMod q)ˣ) (j k : ℤ) :
    twoLongResidueError b (fun u => ZMod.stdAddChar ((j : ZMod q) * u))
      (fun u => ZMod.stdAddChar ((k : ZMod q) * u)) =
      completeKloosterman q (j : ZMod q) (((b : ZMod q).val : ℤ) * k) -
        completeKloosterman q 0 j * completeKloosterman q 0 k / (q.totient : ℂ) := by
  change twoLongResidueError b (longMode j) (longMode k) = _
  rw [twoLongResidueError, longMode_product_sum_units, longMode_sum_units, longMode_sum_units]

private theorem sum_mul_tsum_longMode {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ZMod q) (w : (ZMod q)ˣ → ℂ) (c : ℤ → ℂ)
    (hc : Summable (fun j => ‖c j‖)) :
    (∑ u : (ZMod q)ˣ, w u * ∑' j : ℤ, c j * longMode j (v u)) =
      ∑' j : ℤ, c j * ∑ u : (ZMod q)ˣ, w u * longMode j (v u) := by
  have hs (u : (ZMod q)ˣ) : Summable (fun j : ℤ => w u * (c j * longMode j (v u))) := by
    have hu : Summable (fun j : ℤ => c j * longMode j (v u)) := Summable.of_norm (by
      simpa only [norm_mul, longMode_norm, mul_one] using hc)
    exact hu.mul_left (w u)
  simp only [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun u _ => hs u)]
  apply tsum_congr
  intro j
  rw [mul_sum]
  exact sum_congr rfl fun _ _ => by ring

private def nonzeroLongCoefficient (t : ℝ) (F : ℝ → ℂ) (j : ℤ) : ℂ :=
  if j = 0 then 0 else t • F (t * (j : ℝ))

private theorem nonzeroLongCoefficient_norm_summable_le (t : ℝ) (ht : 0 < t)
    (F : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ x : ℝ, ‖F x‖ ≤ C / (1 + |x|) ^ 2) :
    Summable (fun j : ℤ => ‖nonzeroLongCoefficient t F j‖) ∧
      (∑' j : ℤ, ‖nonzeroLongCoefficient t F j‖) ≤ 2 * C := by
  obtain ⟨hS, hsum⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hpoint (j : ℤ) : ‖nonzeroLongCoefficient t F j‖ ≤ C * poissonNonzeroDecay t j := by
    by_cases hj : j = 0
    · simp [hj, nonzeroLongCoefficient, poissonNonzeroDecay]
    · simp only [nonzeroLongCoefficient, poissonNonzeroDecay, hj, if_false, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht]
      exact (mul_le_mul_of_nonneg_left (hdecay _) ht.le).trans_eq (by ring)
  have hc := (hS.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  refine ⟨hc, (hc.tsum_le_tsum hpoint (hS.mul_left _)).trans ?_⟩
  rw [tsum_mul_left, mul_comm (2 : ℝ) C]
  exact mul_le_mul_of_nonneg_left hsum hC

private theorem norm_tsum_weighted_le (c f : ℤ → ℂ) (hc : Summable (fun j => ‖c j‖))
    (B : ℝ) (hB : ∀ j, ‖f j‖ ≤ B) :
    ‖∑' j : ℤ, c j * f j‖ ≤ (∑' j : ℤ, ‖c j‖) * B := by
  have hpoint (j : ℤ) : ‖c j * f j‖ ≤ ‖c j‖ * B := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB j) (norm_nonneg _)
  have hs := (hc.mul_right B).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have hsum := (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hpoint (hc.mul_right B))
  rwa [tsum_mul_right] at hsum

private def centeredLongProfile {q : ℕ} [NeZero q] (t : ℝ) (F : ℝ → ℂ) (u : ZMod q) : ℂ :=
  ∑' j : ℤ, nonzeroLongCoefficient t F j * longMode j u

private theorem centeredLongProfile_sum_units {q : ℕ} [NeZero q] (t : ℝ) (F : ℝ → ℂ)
    (hc : Summable (fun j => ‖nonzeroLongCoefficient t F j‖)) :
    (∑ u : (ZMod q)ˣ, centeredLongProfile t F (u : ZMod q)) =
      ∑' j : ℤ, nonzeroLongCoefficient t F j * completeKloosterman q 0 j := by
  simpa only [one_mul, longMode_sum_units, centeredLongProfile] using
    (sum_mul_tsum_longMode (fun u : (ZMod q)ˣ => (u : ZMod q)) (fun _ => 1)
      (nonzeroLongCoefficient t F) hc)

private theorem centeredLongProfile_product_sum_units {q : ℕ} [NeZero q] (b : (ZMod q)ˣ)
    (t s : ℝ) (F G : ℝ → ℂ)
    (hc : Summable (fun j => ‖nonzeroLongCoefficient t F j‖))
    (hd : Summable (fun k => ‖nonzeroLongCoefficient s G k‖)) :
    (∑ u : (ZMod q)ˣ, centeredLongProfile t F (u : ZMod q) *
      centeredLongProfile s G (↑(b * u⁻¹) : ZMod q)) =
      ∑' k : ℤ, nonzeroLongCoefficient s G k * ∑' j : ℤ, nonzeroLongCoefficient t F j *
        completeKloosterman q (j : ZMod q) (((b : ZMod q).val : ℤ) * k) := by
  change (∑ u : (ZMod q)ˣ, centeredLongProfile t F (u : ZMod q) *
    ∑' k : ℤ, nonzeroLongCoefficient s G k * longMode k (↑(b * u⁻¹) : ZMod q)) = _
  rw [sum_mul_tsum_longMode _ _ _ hd]
  apply tsum_congr
  intro k
  congr 1
  simp_rw [mul_comm (centeredLongProfile t F _), centeredLongProfile]
  rw [sum_mul_tsum_longMode _ _ _ hc]
  apply tsum_congr
  intro j
  congr 1
  simp_rw [mul_comm (longMode k _)]
  exact longMode_product_sum_units b j k

private theorem centeredLongError_norm_le {q : ℕ} [NeZero q] (b : (ZMod q)ˣ)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (F G : ℝ → ℂ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖F x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖G x‖ ≤ D / (1 + |x|) ^ 2) :
    ‖twoLongResidueError b (centeredLongProfile t F) (centeredLongProfile s G)‖ ≤
      4 * C * D * (q.divisors.card : ℝ) ^ 2 * (Real.sqrt q + 1 / q.totient) := by
  obtain ⟨hc, _⟩ := nonzeroLongCoefficient_norm_summable_le t ht F C hC hF
  obtain ⟨hd, hmass⟩ := nonzeroLongCoefficient_norm_summable_le s hs G D hD hG
  let τ := (q.divisors.card : ℝ)
  let wf := centeredLongProfile (q := q) t F
  let wg := centeredLongProfile (q := q) s G
  have hcount : ‖∑ u : (ZMod q)ˣ, wf (u : ZMod q) * wg (↑(b * u⁻¹) : ZMod q)‖ ≤
      4 * C * D * τ ^ 2 * Real.sqrt q := by
    change ‖∑ u : (ZMod q)ˣ, centeredLongProfile t F (u : ZMod q) *
      centeredLongProfile s G (↑(b * u⁻¹) : ZMod q)‖ ≤ _
    rw [centeredLongProfile_product_sum_units b t s F G hc hd]
    have hinner (k : ℤ) : ‖∑' j : ℤ, nonzeroLongCoefficient t F j *
        completeKloosterman q (j : ZMod q) (((b : ZMod q).val : ℤ) * k)‖ ≤
        2 * C * τ ^ 2 * Real.sqrt q := by
      simp only [nonzeroLongCoefficient, ite_mul, zero_mul]
      exact (completedReciprocal_nonzero_norm_le q _ t ht F C hC hF).2
    refine (norm_tsum_weighted_le _ _ hd _ hinner).trans ?_
    calc
      _ ≤ (2 * D) * (2 * C * τ ^ 2 * Real.sqrt q) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = _ := by ring
  have hmean (s : ℝ) (hs : 0 < s) (H : ℝ → ℂ) (A : ℝ) (hA : 0 ≤ A)
      (hH : ∀ x : ℝ, ‖H x‖ ≤ A / (1 + |x|) ^ 2)
      (hc : Summable (fun j => ‖nonzeroLongCoefficient s H j‖)) :
      ‖∑ u : (ZMod q)ˣ, centeredLongProfile s H (u : ZMod q)‖ ≤ 2 * A * τ := by
    rw [centeredLongProfile_sum_units s H hc]
    simp only [nonzeroLongCoefficient, ite_mul, zero_mul]
    exact completedRamanujan_nonzero_norm_le q s hs H A hA hH
  have hmeanProduct : ‖(∑ u : (ZMod q)ˣ, wf u) * (∑ u : (ZMod q)ˣ, wg u) / (q.totient : ℂ)‖ ≤
      4 * C * D * τ ^ 2 / q.totient := by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (2 * C * τ) * (2 * D * τ) / (q.totient : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul (hmean t ht F C hC hF hc) (hmean s hs G D hD hG hd)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  change ‖twoLongResidueError b wf wg‖ ≤ 4 * C * D * τ ^ 2 * (Real.sqrt q + 1 / q.totient)
  rw [twoLongResidueError]
  exact (norm_sub_le _ _).trans ((add_le_add hcount hmeanProduct).trans_eq (by ring))

/-- One residue's periodized profile in terms of the exact Fourier coefficients. -/
def twoLongFourierProfile {q : ℕ} [NeZero q] (t : ℝ) (F : ℝ → ℂ) (u : ZMod q) : ℂ :=
  ∑' j : ℤ, (t • F (t * (j : ℝ))) * ZMod.stdAddChar ((j : ZMod q) * u)

private theorem twoLongFourierProfile_eq_add_const {q : ℕ} [NeZero q] (t : ℝ)
    (F : ℝ → ℂ) (hc : Summable (fun j => ‖nonzeroLongCoefficient t F j‖)) (u : ZMod q) :
    twoLongFourierProfile t F u = centeredLongProfile t F u + t • F 0 := by
  let c (j : ℤ) := nonzeroLongCoefficient t F j * longMode j u
  let z (j : ℤ) := if j = 0 then t • F 0 else (0 : ℂ)
  have hc' : Summable c := Summable.of_norm (by simpa only [c, norm_mul, longMode_norm, mul_one] using hc)
  have hz : Summable z := summable_of_hasFiniteSupport ((Set.finite_singleton 0).subset (by
    intro j hj
    by_contra h
    have hne : j ≠ 0 := by simpa only [Set.mem_singleton_iff] using h
    exact hj (by simp [z, hne])))
  have hj (j : ℤ) : (t • F (t * (j : ℝ))) * longMode j u = c j + z j := by
    by_cases hj : j = 0 <;> simp [c, z, nonzeroLongCoefficient, longMode, hj]
  change (∑' j : ℤ, (t • F (t * (j : ℝ))) * longMode j u) = _
  simp only [hj, hc'.tsum_add hz]
  have hzsum : (∑' j : ℤ, z j) = t • F 0 := by
    rw [tsum_eq_single 0 (fun j hj => by simp [z, hj])]
    simp [z]
  exact congrArg (fun a => centeredLongProfile t F u + a) hzsum

/-- The primitive residue mass has the exact zero Fourier mode and a
Ramanujan error uniform in the positive mesh. -/
theorem twoLongFourierProfile_primitiveMean_norm_le {q : ℕ} [NeZero q]
    {t : ℝ} (ht : 0 < t) (F : ℝ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x : ℝ, ‖F x‖ ≤ C / (1 + |x|) ^ 2) :
    ‖(∑ u : (ZMod q)ˣ, twoLongFourierProfile t F (u : ZMod q)) -
      (q.totient : ℂ) * (t • F 0)‖ ≤ 2 * C * (q.divisors.card : ℝ) := by
  obtain ⟨hc, _⟩ := nonzeroLongCoefficient_norm_summable_le t ht F C hC hF
  simp only [twoLongFourierProfile_eq_add_const t F hc, sum_add_distrib, sum_const, card_univ,
    ZMod.card_units_eq_totient, nsmul_eq_mul, add_sub_cancel_right]
  rw [centeredLongProfile_sum_units t F hc]
  simp only [nonzeroLongCoefficient, ite_mul, zero_mul]
  exact completedRamanujan_nonzero_norm_le q t ht F C hC hF

/-- The uncentered product profiles satisfy the two-long estimate. Their
zero modes cancel identically, and the primitive main term stays exact. -/
theorem twoLongResidueError_fourierProfiles_norm_le {q : ℕ} [NeZero q] (b : (ZMod q)ˣ)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (F G : ℝ → ℂ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ x : ℝ, ‖F x‖ ≤ C / (1 + |x|) ^ 2)
    (hG : ∀ x : ℝ, ‖G x‖ ≤ D / (1 + |x|) ^ 2) :
    ‖twoLongResidueError b (twoLongFourierProfile t F) (twoLongFourierProfile s G)‖ ≤
      4 * C * D * (q.divisors.card : ℝ) ^ 2 * (Real.sqrt q + 1 / q.totient) := by
  obtain ⟨hc, _⟩ := nonzeroLongCoefficient_norm_summable_le t ht F C hC hF
  obtain ⟨hd, _⟩ := nonzeroLongCoefficient_norm_summable_le s hs G D hD hG
  rw [funext (twoLongFourierProfile_eq_add_const t F hc),
    funext (twoLongFourierProfile_eq_add_const s G hd),
    twoLongResidueError_add_const_left, twoLongResidueError_add_const_right]
  exact centeredLongError_norm_le b ht hs F G hC hD hF hG

end

end ImbalancedChen.Part3
