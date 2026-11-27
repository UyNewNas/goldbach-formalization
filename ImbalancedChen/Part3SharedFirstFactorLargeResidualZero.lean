import ImbalancedChen.Part3SharedFirstFactorCharacterDictionary

/-!
# The large residual gcd in the actual shared first-factor zero mode

The residual divisor here is gcd of the two remaining physical factor
products. It is not the gcd of the paired original-alpha variables.
The high-conductor restriction is retained, so this object can accompany
the low-conductor estimate on all residual divisors without overlap.

The finite character argument keeps the auxiliary coprimality sieve.
Exact complex factor grouping and gcd grouping precede every norm.
The resulting coefficients cost tau_2, rather than an assumed unit bound.
The finite reciprocal-square tail retains its literal inverse cutoff.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators Pointwise
open SharedFirstFactorCharacterDictionary
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace SharedFirstFactorLargeResidualZero

private def characterTransform (N : Finset ℕ) (a : ℕ → ℂ) (delta : ℕ)
    (chi : DirichletCharacter ℂ delta) : ℂ :=
  ∑ n ∈ N, a n * star (chi (n : ZMod delta))

private theorem character_star_inverse {delta : ℕ} [NeZero delta]
    (chi : DirichletCharacter ℂ delta) {a : ZMod delta} (ha : IsUnit a) :
    star (chi a) = chi a⁻¹ := by
  obtain ⟨u, rfl⟩ := ha
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

private theorem character_orthogonality {delta : ℕ} (hdelta : 0 < delta)
    (n m : ℕ) :
    (∑ chi : DirichletCharacter ℂ delta,
      star (chi (n : ZMod delta)) * chi (m : ZMod delta)) =
      if n.Coprime delta ∧ m.Coprime delta ∧ Nat.ModEq delta n m then
        (delta.totient : ℂ) else 0 := by
  let : NeZero delta := ⟨hdelta.ne'⟩
  have hexp : Monoid.exponent (ZMod delta)ˣ ≠ 0 := Monoid.exponent_ne_zero.mpr
    (Monoid.ExponentExists.of_finite (G := (ZMod delta)ˣ))
  let : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod delta)ˣ) := by
    let : NeZero (Monoid.exponent (ZMod delta)ˣ) := ⟨hexp⟩
    refine { prim := ?_, cyc := ?_ }
    · exact ⟨Complex.exp (2 * Real.pi * Complex.I /
        (Monoid.exponent (ZMod delta)ˣ : ℂ)),
        Complex.isPrimitiveRoot_exp (Monoid.exponent (ZMod delta)ˣ) hexp⟩
    · infer_instance
  have hz (a b : ZMod delta) :
      (∑ chi : DirichletCharacter ℂ delta, star (chi a) * chi b) =
        if IsUnit a ∧ IsUnit b ∧ a = b then (delta.totient : ℂ) else 0 := by
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · calc
          _ = ∑ chi : DirichletCharacter ℂ delta, chi a⁻¹ * chi b := by
            apply Finset.sum_congr rfl
            intro chi _
            rw [character_star_inverse chi ha]
          _ = if a = b then (delta.totient : ℂ) else 0 :=
            DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b
          _ = _ := by simp only [ha, hb, true_and]
      · rw [if_neg (fun h ↦ hb h.2.1)]
        apply Finset.sum_eq_zero
        intro chi _
        rw [chi.map_nonunit hb, mul_zero]
    · rw [if_neg (fun h ↦ ha h.1)]
      apply Finset.sum_eq_zero
      intro chi _
      rw [chi.map_nonunit ha, star_zero, zero_mul]
  simpa only [ZMod.isUnit_iff_coprime, ZMod.natCast_eq_natCast_iff] using
    hz (n : ZMod delta) (m : ZMod delta)

private theorem transform_parseval (N : Finset ℕ) (a : ℕ → ℂ)
    {delta : ℕ} (hdelta : 0 < delta) :
    (∑ chi : DirichletCharacter ℂ delta,
      characterTransform N a delta chi * star (characterTransform N a delta chi)) =
      (delta.totient : ℂ) *
        ∑ n ∈ N, ∑ m ∈ N,
          if n.Coprime delta ∧ m.Coprime delta ∧ Nat.ModEq delta n m then
            a n * star (a m) else 0 := by
  unfold characterTransform
  simp only [star_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  calc
    _ = a n * star (a m) *
        ∑ chi : DirichletCharacter ℂ delta,
          star (chi (n : ZMod delta)) * chi (m : ZMod delta) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      simp only [star_mul', star_star]
      ring
    _ = _ := by
      rw [character_orthogonality hdelta]
      split_ifs <;> ring

private theorem progression_card_le (N : Finset ℕ) (H delta b : ℕ)
    (hN : N ⊆ Finset.Ioc 0 H) :
    ((N.filter (fun n ↦ Nat.ModEq delta n b)).card : ℝ) ≤
      (H : ℝ) / delta + 1 := by
  have hc : (N.filter (fun n ↦ Nat.ModEq delta n b)).card ≤ H / delta + 1 := by
    calc
      _ ≤ (Finset.range (H / delta + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun n : ℕ ↦ n / delta)
        · intro n hn
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le
            (Nat.div_le_div_right (Finset.mem_Ioc.mp (hN (Finset.mem_filter.mp hn).1)).2))
        · intro n hn m hm he
          apply Nat.ext_div_modEq he
          exact (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
      _ = _ := Finset.card_range _
  calc
    _ ≤ ((H / delta : ℕ) : ℝ) + 1 := by exact_mod_cast hc
    _ ≤ _ := add_le_add Nat.cast_div_le le_rfl

private theorem unit_pair_mass_norm_le (N : Finset ℕ) (a : ℕ → ℂ)
    (H delta : ℕ) (hN : N ⊆ Finset.Ioc 0 H)
    (ha : ∀ n ∈ N, ‖a n‖ ≤ 1) :
    ‖∑ n ∈ N, ∑ m ∈ N,
      if n.Coprime delta ∧ m.Coprime delta ∧ Nat.ModEq delta n m then
        a n * star (a m) else 0‖ ≤
      (H : ℝ) * ((H : ℝ) / delta + 1) := by
  have hcard : (N.card : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (Finset.card_le_card hN).trans_eq (by simp)
  calc
    _ ≤ ∑ n ∈ N, ∑ m ∈ N,
        if Nat.ModEq delta n m then (1 : ℝ) else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m hm
      by_cases h : n.Coprime delta ∧ m.Coprime delta ∧ Nat.ModEq delta n m
      · simp only [if_pos h, if_pos h.2.2, norm_mul, norm_star]
        simpa only [one_mul] using mul_le_mul (ha n hn) (ha m hm)
          (norm_nonneg _) zero_le_one
      · simp only [if_neg h, norm_zero]
        split_ifs <;> norm_num
    _ = ∑ n ∈ N, ((N.filter (fun m ↦ Nat.ModEq delta m n)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [Nat.ModEq.comm (a := n), ← Finset.sum_filter]
      simp
    _ ≤ ∑ _n ∈ N, ((H : ℝ) / delta + 1) :=
      Finset.sum_le_sum (fun n _ ↦ progression_card_le N H delta n hN)
    _ = (N.card : ℝ) * ((H : ℝ) / delta + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

private theorem transform_square_sum_le (N : Finset ℕ) (a : ℕ → ℂ)
    (H : ℕ) {delta : ℕ} (hdelta : 0 < delta)
    (hN : N ⊆ Finset.Ioc 0 H) (ha : ∀ n ∈ N, ‖a n‖ ≤ 1) :
    (∑ chi : DirichletCharacter ℂ delta,
      ‖characterTransform N a delta chi‖ ^ 2) ≤
      (delta.totient : ℝ) * ((H : ℝ) * ((H : ℝ) / delta + 1)) := by
  have hcast :
      (((∑ chi : DirichletCharacter ℂ delta,
        ‖characterTransform N a delta chi‖ ^ 2) : ℝ) : ℂ) =
        ∑ chi : DirichletCharacter ℂ delta,
          characterTransform N a delta chi * star (characterTransform N a delta chi) := by
    push_cast
    apply Finset.sum_congr rfl
    intro chi _
    exact (Complex.mul_conj' _).symm
  calc
    _ = ‖(((∑ chi : DirichletCharacter ℂ delta,
        ‖characterTransform N a delta chi‖ ^ 2) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
    _ = ‖(delta.totient : ℂ) *
        ∑ n ∈ N, ∑ m ∈ N,
          if n.Coprime delta ∧ m.Coprime delta ∧ Nat.ModEq delta n m then
            a n * star (a m) else 0‖ := by rw [hcast, transform_parseval N a hdelta]
    _ = (delta.totient : ℝ) * ‖∑ n ∈ N, ∑ m ∈ N,
          if n.Coprime delta ∧ m.Coprime delta ∧ Nat.ModEq delta n m then
            a n * star (a m) else 0‖ := by rw [norm_mul, Complex.norm_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (unit_pair_mass_norm_le N a H delta hN ha)
      (Nat.cast_nonneg _)

private theorem auxiliary_eq_transform (N : Finset ℕ) (a : ℕ → ℂ)
    (k delta : ℕ) (chi : DirichletCharacter ℂ delta) :
    auxiliaryCharacterSum N a k delta chi =
      characterTransform N (fun n ↦ if n.Coprime k then a n else 0) delta chi := by
  unfold auxiliaryCharacterSum characterTransform
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Coprime k
  · simp only [if_pos hn]
  · simp only [if_neg hn, zero_mul]

private theorem alpha_subset_prefix {d : MediumAtom} (hU : 1 ≤ d.U) :
    d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U)) := by
  intro n hn
  obtain ⟨hn, _⟩ := Finset.mem_filter.mp hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hc : 1 ≤ Nat.ceil d.U := by exact_mod_cast hU.trans (Nat.le_ceil d.U)
  exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩

private theorem actual_auxiliary_square_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k : ℕ)
    {delta : ℕ} (hdelta : 0 < delta) :
    (∑ chi : DirichletCharacter ℂ delta,
      ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ ^ 2) ≤
      (delta.totient : ℝ) * (2 * d.U * (2 * d.U / delta + 1)) := by
  have ha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ha, _⟩ := hd
    exact ha
  simp only [auxiliary_eq_transform]
  have hb : ∀ n ∈ d.alphaCarrier, ‖if n.Coprime k then d.alpha n else 0‖ ≤ 1 := by
    intro n hn
    split_ifs
    · exact ha n hn
    · simp
  refine (transform_square_sum_le d.alphaCarrier
    (fun n ↦ if n.Coprime k then d.alpha n else 0)
    (Nat.floor (2 * d.U)) hdelta (alpha_subset_prefix hd.1) hb).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hf : (Nat.floor (2 * d.U) : ℝ) ≤ 2 * d.U := Nat.floor_le (by linarith [hd.1])
  have hdelta0 : (0 : ℝ) ≤ delta := Nat.cast_nonneg _
  exact mul_le_mul hf (add_le_add (div_le_div_of_nonneg_right hf hdelta0) le_rfl)
    (by positivity) (by linarith [hd.1])

/-- The same arbitrary character subset occurs in both coefficient sums.
Only nonnegative square sums are enlarged to the full character carrier. -/
private theorem auxiliary_cross_div_totient_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k l : ℕ)
    {delta : ℕ} (hdelta : 0 < delta)
    (C : Finset (DirichletCharacter ℂ delta)) :
    ‖(∑ chi ∈ C,
      auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi *
        star (auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi)) /
          (delta.totient : ℂ)‖ ≤ 2 * d.U * (2 * d.U / delta + 1) := by
  let E : ℝ := (delta.totient : ℝ) * (2 * d.U * (2 * d.U / delta + 1))
  have hsq (j : ℕ) :
      (∑ chi ∈ C, ‖auxiliaryCharacterSum d.alphaCarrier d.alpha j delta chi‖ ^ 2) ≤ E := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ C) (fun _ _ _ ↦ sq_nonneg _)).trans ?_
    exact actual_auxiliary_square_sum_le hd j hdelta
  have hcross : ‖∑ chi ∈ C,
      auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi *
        star (auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi)‖ ≤ E := by
    calc
      _ ≤ ∑ chi ∈ C,
          ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ *
            ‖auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi‖ := by
        simpa only [norm_mul, norm_star] using norm_sum_le C
          (fun chi ↦ auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi *
            star (auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi))
      _ ≤ ∑ chi ∈ C,
          (‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ ^ 2 +
            ‖auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi‖ ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro chi _
        nlinarith [sq_nonneg
          (‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ -
            ‖auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi‖)]
      _ = ((∑ chi ∈ C,
          ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ ^ 2) +
          (∑ chi ∈ C,
            ‖auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi‖ ^ 2)) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ E := by linarith [hsq k, hsq l]
  have hphi : (0 : ℝ) < delta.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hdelta)
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hphi).mpr
  dsimp only [E] at hcross
  nlinarith only [hcross]

private def tailLabels (d : MediumAtom) : Finset (ℕ × ℕ) :=
  factorCarrier d.Q2 ×ˢ factorCarrier d.Q3

private def tailProducts (d : MediumAtom) : Finset ℕ :=
  (tailLabels d).image (fun u ↦ u.1 * u.2)

private def tailGamma (d : MediumAtom) (v : ℕ) : ℂ :=
  ∑ u ∈ (tailLabels d).filter (fun u ↦ u.1 * u.2 = v), d.gamma2 u.1 * d.gamma3 u.2

private def tailCap (d : MediumAtom) : ℝ := 4 * d.Q2 * d.Q3

private def tau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

private theorem factor_bounds {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : 0 < n ∧ Q ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hlower : Q ≤ (n : ℝ) :=
    (Nat.le_ceil Q).trans (by exact_mod_cast hlo)
  have hpos : (0 : ℝ) < n := (zero_lt_one.trans_le hQ).trans_le hlower
  refine ⟨by exact_mod_cast hpos, hlower, ?_⟩
  exact (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
    (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

private theorem one_le_tailCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ tailCap d := by
  have h2 := hd.2.2.2.1
  have h3 := hd.2.2.2.2.1
  unfold tailCap
  nlinarith [mul_le_mul h2 h3 zero_le_one (by linarith : 0 ≤ d.Q2)]

private theorem tail_product_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {u : ℕ × ℕ}
    (hu : u ∈ tailLabels d) : 0 < u.1 * u.2 ∧ (u.1 * u.2 : ℕ) ≤ Nat.floor (tailCap d) := by
  obtain ⟨h2, h3⟩ := Finset.mem_product.mp hu
  have hb2 := factor_bounds hd.2.2.2.1 h2
  have hb3 := factor_bounds hd.2.2.2.2.1 h3
  refine ⟨Nat.mul_pos hb2.1 hb3.1, Nat.le_floor ?_⟩
  push_cast
  calc
    (u.1 : ℝ) * u.2 ≤ (2 * d.Q2) * (2 * d.Q3) :=
      mul_le_mul hb2.2.2 hb3.2.2 (Nat.cast_nonneg _) (by linarith [hd.2.2.2.1])
    _ = tailCap d := by unfold tailCap; ring

private theorem tailProducts_subset_prefix
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    tailProducts d ⊆ Finset.Ioc 0 (Nat.floor (tailCap d)) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_Ioc.mpr (tail_product_bounds hd hu)

private theorem tailGamma_zero_off_products (d : MediumAtom) {v : ℕ}
    (hv : v ∉ tailProducts d) : tailGamma d v = 0 := by
  unfold tailGamma
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hu, he⟩ := Finset.mem_filter.mp hu
  exact (hv (Finset.mem_image.mpr ⟨u, hu, he⟩)).elim

private theorem tailGamma_norm_le_tau
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (v : ℕ) :
    ‖tailGamma d v‖ ≤ tau v := by
  let S := (tailLabels d).filter (fun u ↦ u.1 * u.2 = v)
  have hsub : S ⊆ v.divisorsAntidiagonal := by
    intro u hu
    obtain ⟨hu, he⟩ := Finset.mem_filter.mp hu
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨he, by rw [← he]; exact (tail_product_bounds hd hu).1.ne'⟩
  have hcard : v.divisorsAntidiagonal.card = v.divisors.card := by
    rw [← Nat.map_div_right_divisors]
    exact Finset.card_map _
  have hg : ∀ u ∈ S, ‖d.gamma2 u.1 * d.gamma3 u.2‖ ≤ 1 := by
    intro u hu
    obtain ⟨hu, _⟩ := Finset.mem_filter.mp hu
    obtain ⟨h2, h3⟩ := Finset.mem_product.mp hu
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hg2, hg3⟩ := hd
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hg2 _ h2).1 (hg3 _ h3).1
      (norm_nonneg _) zero_le_one
  calc
    ‖tailGamma d v‖ ≤ ∑ u ∈ S, ‖d.gamma2 u.1 * d.gamma3 u.2‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ S, (1 : ℝ) := Finset.sum_le_sum hg
    _ = (S.card : ℝ) := by simp
    _ ≤ tau v := by
      unfold tau
      exact_mod_cast (Finset.card_le_card hsub).trans_eq hcard

/-- Group every original complex tail label before taking its norm. -/
private theorem tail_sum_eq_grouped (d : MediumAtom) (F : ℕ → ℂ) :
    (∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) * F (u.1 * u.2)) =
      ∑ v ∈ tailProducts d, tailGamma d v * F v := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := tailLabels d) (t := tailProducts d) (g := fun u ↦ u.1 * u.2)
    (fun u hu ↦ Finset.mem_image_of_mem _ hu)
    (fun u ↦ (d.gamma2 u.1 * d.gamma3 u.2) * F (u.1 * u.2))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro v _
  rw [tailGamma, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [(Finset.mem_filter.mp hu).2]

private theorem tail_star_sum_eq_grouped (d : MediumAtom) (F : ℕ → ℂ) :
    (∑ u ∈ tailLabels d, star (d.gamma2 u.1 * d.gamma3 u.2) * F (u.1 * u.2)) =
      ∑ v ∈ tailProducts d, star (tailGamma d v) * F v := by
  calc
    _ = star (∑ u ∈ tailLabels d,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (F (u.1 * u.2))) := by
      simp only [star_sum, star_mul', star_star]
    _ = star (∑ v ∈ tailProducts d, tailGamma d v * star (F v)) :=
      congrArg star (tail_sum_eq_grouped d (fun v ↦ star (F v)))
    _ = _ := by simp only [star_sum, star_mul', star_star]

private theorem tail_pair_sum_eq_grouped (d : MediumAtom) (F : ℕ → ℕ → ℂ) :
    (∑ u ∈ tailLabels d, ∑ v ∈ tailLabels d,
      (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
        F (u.1 * u.2) (v.1 * v.2)) =
      ∑ a ∈ tailProducts d, ∑ b ∈ tailProducts d,
        tailGamma d a * star (tailGamma d b) * F a b := by
  calc
    _ = ∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) *
        ∑ v ∈ tailLabels d,
          star (d.gamma2 v.1 * d.gamma3 v.2) * F (u.1 * u.2) (v.1 * v.2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ a ∈ tailProducts d, tailGamma d a *
        ∑ v ∈ tailLabels d,
          star (d.gamma2 v.1 * d.gamma3 v.2) * F a (v.1 * v.2) :=
      tail_sum_eq_grouped d (fun a ↦ ∑ v ∈ tailLabels d,
        star (d.gamma2 v.1 * d.gamma3 v.2) * F a (v.1 * v.2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [tail_star_sum_eq_grouped d (F a), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

private theorem tail_sum_eq_prefix
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (F : ℕ → ℂ) :
    (∑ v ∈ tailProducts d, tailGamma d v * F v) =
      ∑ v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)), tailGamma d v * F v := by
  apply Finset.sum_subset (tailProducts_subset_prefix hd)
  intro v _ hv
  rw [tailGamma_zero_off_products d hv, zero_mul]

private theorem tail_pair_sum_eq_prefix
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (F : ℕ → ℕ → ℂ) :
    (∑ u ∈ tailLabels d, ∑ v ∈ tailLabels d,
      (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
        F (u.1 * u.2) (v.1 * v.2)) =
      ∑ a ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
        ∑ b ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
          tailGamma d a * star (tailGamma d b) * F a b := by
  rw [tail_pair_sum_eq_grouped]
  calc
    _ = ∑ a ∈ tailProducts d, tailGamma d a *
        ∑ b ∈ tailProducts d, star (tailGamma d b) * F a b := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ a ∈ Finset.Ioc 0 (Nat.floor (tailCap d)), tailGamma d a *
        ∑ b ∈ tailProducts d, star (tailGamma d b) * F a b :=
      tail_sum_eq_prefix hd (fun a ↦ ∑ b ∈ tailProducts d,
        star (tailGamma d b) * F a b)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have hb : (∑ b ∈ tailProducts d, star (tailGamma d b) * F a b) =
          ∑ b ∈ Finset.Ioc 0 (Nat.floor (tailCap d)), star (tailGamma d b) * F a b := by
        apply Finset.sum_subset (tailProducts_subset_prefix hd)
        intro b _ hb
        rw [tailGamma_zero_off_products d hb, star_zero, zero_mul]
      rw [hb, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Exact gcd disintegration, still for the original complex sum. -/
private theorem pair_sum_by_gcd (N : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ a ∈ Finset.Ioc 0 N, ∑ b ∈ Finset.Ioc 0 N, F a b) =
      ∑ D ∈ Finset.Ioc 0 N, ∑ a ∈ Finset.Ioc 0 N, ∑ b ∈ Finset.Ioc 0 N,
        if a.gcd b = D then F a b else 0 := by
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hag : a.gcd b ∈ Finset.Ioc 0 N := Finset.mem_Ioc.mpr
    ⟨Nat.gcd_pos_of_pos_left b (Finset.mem_Ioc.mp ha).1,
      (Nat.le_of_dvd (Finset.mem_Ioc.mp ha).1 (Nat.gcd_dvd_left a b)).trans
        (Finset.mem_Ioc.mp ha).2⟩
  rw [Finset.sum_eq_single (a.gcd b)]
  · rw [if_pos rfl]
  · intro D _ hD
    exact if_neg (fun h ↦ hD h.symm)
  · exact fun h ↦ (h hag).elim

private def characterKernel (d : MediumAtom) (p v w : ℕ) (R : ℝ) : ℂ :=
  (((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
    ((p * v.lcm w : ℕ) : ℂ)) *
      ((∑ chi ∈ ((Finset.univ : Finset
          (DirichletCharacter ℂ (p * v.gcd w))).erase 1).filter
            (fun chi ↦ R < (chi.conductor : ℝ)),
        auxiliaryCharacterSum d.alphaCarrier d.alpha (v / v.gcd w) (p * v.gcd w) chi *
          star (auxiliaryCharacterSum d.alphaCarrier d.alpha
            (w / v.gcd w) (p * v.gcd w) chi)) / ((p * v.gcd w).totient : ℂ))

private def gcdSlice (d : MediumAtom) (p D : ℕ) (R : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
    ∑ w ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
      if v.gcd w = D then
        tailGamma d v * star (tailGamma d w) * characterKernel d p v w R
      else 0

private def largeDivisors (d : MediumAtom) (Y : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 (Nat.floor (tailCap d))).filter (fun D ↦ Y < (D : ℝ))

end SharedFirstFactorLargeResidualZero

open SharedFirstFactorLargeResidualZero

/-- The literal zero-mode dictionary restricted to high conductor and
large gcd of the two remaining physical factor products. -/
def MediumAtom.sharedFirstFactorLargeResidualHighConductorZero
    (d : MediumAtom) (Y R : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    ∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
      ∑ v ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
        if Y < ((u.1 * u.2).gcd (v.1 * v.2) : ℝ) then
          (((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
            (((p * (u.1 * u.2).lcm (v.1 * v.2) : ℕ) : ℂ) *
              ((p * (u.1 * u.2).gcd (v.1 * v.2)).totient : ℂ))) *
            (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
            (∑ chi ∈ ((Finset.univ : Finset
                (DirichletCharacter ℂ (p * (u.1 * u.2).gcd (v.1 * v.2)))).erase 1).filter
                  (fun chi ↦ R < (chi.conductor : ℝ)),
              auxiliaryCharacterSum d.alphaCarrier d.alpha
                ((u.1 * u.2) / (u.1 * u.2).gcd (v.1 * v.2))
                (p * (u.1 * u.2).gcd (v.1 * v.2)) chi *
              star (auxiliaryCharacterSum d.alphaCarrier d.alpha
                ((v.1 * v.2) / (u.1 * u.2).gcd (v.1 * v.2))
                (p * (u.1 * u.2).gcd (v.1 * v.2)) chi))
        else 0

namespace SharedFirstFactorLargeResidualZero

/-- The actual signed expression is grouped twice before any norm:
first by each full tail product, then by their exact gcd. -/
private theorem actual_eq_gcd_slices
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y R : ℝ) :
    d.sharedFirstFactorLargeResidualHighConductorZero Y R =
      ∑ p ∈ d.primitiveFirstFactorCarrier,
        ∑ D ∈ largeDivisors d Y, gcdSlice d p D R := by
  unfold MediumAtom.sharedFirstFactorLargeResidualHighConductorZero
  apply Finset.sum_congr rfl
  intro p _
  calc
    _ = ∑ u ∈ tailLabels d, ∑ v ∈ tailLabels d,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
          (if Y < ((u.1 * u.2).gcd (v.1 * v.2) : ℝ) then
            characterKernel d p (u.1 * u.2) (v.1 * v.2) R else 0) := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      unfold characterKernel
      split_ifs <;> ring
    _ = ∑ v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
        ∑ w ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
          tailGamma d v * star (tailGamma d w) *
            (if Y < (v.gcd w : ℝ) then characterKernel d p v w R else 0) :=
      tail_pair_sum_eq_prefix hd (fun v w ↦
        if Y < (v.gcd w : ℝ) then characterKernel d p v w R else 0)
    _ = ∑ D ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
        ∑ v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
          ∑ w ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
            if v.gcd w = D then tailGamma d v * star (tailGamma d w) *
              (if Y < (v.gcd w : ℝ) then characterKernel d p v w R else 0) else 0 :=
      pair_sum_by_gcd _ _
    _ = _ := by
      rw [largeDivisors, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro D _
      by_cases hY : Y < (D : ℝ)
      · rw [if_pos hY]
        unfold gcdSlice
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro w _
        by_cases hD : v.gcd w = D
        · simp only [hD, if_pos hY, ite_true]
        · simp only [if_neg hD]
      · rw [if_neg hY]
        apply Finset.sum_eq_zero
        intro v _
        apply Finset.sum_eq_zero
        intro w _
        by_cases hD : v.gcd w = D
        · simp only [hD, if_neg hY, mul_zero, ite_true]
        · simp only [if_neg hD]

private theorem characterKernel_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {p v w : ℕ} (hp : 0 < p) (hv : 0 < v) (hw : 0 < w) (R : ℝ) :
    ‖characterKernel d p v w R‖ ≤
      |CommonSmoothCutoff.cutoffMass| * d.V *
        (4 * d.U ^ 2 / ((p : ℝ) ^ 2 * v * w) +
          2 * d.U * (v.gcd w : ℝ) / ((p : ℝ) * v * w)) := by
  have hD : 0 < v.gcd w := Nat.gcd_pos_of_pos_left w hv
  have hL : 0 < v.lcm w := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hv.ne' hw.ne')
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hDR : (0 : ℝ) < v.gcd w := by exact_mod_cast hD
  have hLR : (0 : ℝ) < v.lcm w := by exact_mod_cast hL
  have hprod : (v.gcd w : ℝ) * (v.lcm w : ℝ) = (v : ℝ) * w := by
    exact_mod_cast Nat.gcd_mul_lcm v w
  have he : (v.lcm w : ℝ) = (v : ℝ) * w / (v.gcd w : ℝ) := by
    apply (eq_div_iff hDR.ne').mpr
    nlinarith only [hprod]
  have hV0 : 0 ≤ d.V := by linarith [hd.2.1]
  unfold characterKernel
  rw [norm_mul]
  have hfirst :
      ‖(((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) /
        ((p * v.lcm w : ℕ) : ℂ))‖ =
        d.V * |CommonSmoothCutoff.cutoffMass| / ((p : ℝ) * (v.lcm w : ℝ)) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by linarith [hd.2.1]), Complex.norm_natCast, Nat.cast_mul]
  rw [hfirst]
  refine (mul_le_mul_of_nonneg_left
    (auxiliary_cross_div_totient_norm_le hd (v / v.gcd w) (w / v.gcd w)
      (Nat.mul_pos hp hD) _) (by positivity)).trans_eq ?_
  rw [Nat.cast_mul, he]
  field_simp [hpR.ne', hvR.ne', hwR.ne', hDR.ne']; ring

private theorem divisors_mul_eq (a b : ℕ) :
    (a * b).divisors = a.divisors * b.divisors := by
  ext n
  simp_rw [Finset.mem_mul, Nat.mem_divisors, Nat.dvd_mul, mul_ne_zero_iff,
    ← exists_and_left, ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

private theorem tau_nonneg (n : ℕ) : 0 ≤ tau n := Nat.cast_nonneg _

private theorem tau_mul_le (a b : ℕ) : tau (a * b) ≤ tau a * tau b := by
  unfold tau
  rw [divisors_mul_eq]
  exact_mod_cast (Finset.card_mul_le (s := a.divisors) (t := b.divisors))

private def multipleWeight (D n : ℕ) : ℝ := if D ∣ n then tau n / (n : ℝ) else 0

private theorem multipleWeight_nonneg (D n : ℕ) : 0 ≤ multipleWeight D n := by
  unfold multipleWeight
  split_ifs
  · exact div_nonneg (tau_nonneg n) (Nat.cast_nonneg _)
  · exact le_rfl

private theorem sum_multiples_real (N D : ℕ) (hD : 0 < D) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc 0 N, if D ∣ n then f n else 0) =
      ∑ k ∈ Finset.Ioc 0 (N / D), f (D * k) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun k _ ↦ D * k) ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hk0, hkN⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨Nat.mul_pos hD hk0, (Nat.mul_le_mul_left D hkN).trans (Nat.mul_div_le N D)⟩,
      dvd_mul_right D k⟩
  · intro k₁ _ k₂ _ he
    exact Nat.eq_of_mul_eq_mul_left hD he
  · intro n hn
    obtain ⟨hn, hDn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    refine ⟨n / D, Finset.mem_Ioc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hn0 hDn) hD, Nat.div_le_div_right hnN⟩,
      Nat.mul_div_cancel' hDn⟩
  · intro k _
    rfl

/-- The exact multiples reindexing keeps the full divisor cost of D. -/
private theorem multiple_harmonic_le {T : ℝ} (hT : 1 ≤ T)
    {D : ℕ} (hD : 0 < D) :
    (∑ n ∈ Finset.Ioc 0 (Nat.floor T), multipleWeight D n) ≤
      tau D / (D : ℝ) * (1 + Real.log T) ^ 2 := by
  unfold multipleWeight
  rw [sum_multiples_real _ _ hD]
  calc
    _ ≤ ∑ k ∈ Finset.Ioc 0 (Nat.floor T / D),
        (tau D / (D : ℝ)) * (tau k / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
      have hDR : (0 : ℝ) < D := by exact_mod_cast hD
      calc
        _ ≤ (tau D * tau k) / ((D * k : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (tau_mul_le D k) (Nat.cast_nonneg _)
        _ = _ := by
          rw [Nat.cast_mul]
          field_simp [hDR.ne', hkR.ne']
    _ = (tau D / (D : ℝ)) *
        ∑ k ∈ Finset.Ioc 0 (Nat.floor T / D), tau k / (k : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (tau D / (D : ℝ)) *
        ∑ k ∈ Finset.Ioc 0 (Nat.floor T), tau k / (k : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (tau_nonneg D) (Nat.cast_nonneg _))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hk).1,
          (Finset.mem_Ioc.mp hk).2.trans (Nat.div_le_self _ _)⟩
      · intro k _ _
        exact div_nonneg (tau_nonneg k) (Nat.cast_nonneg _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (tau_nonneg D) (Nat.cast_nonneg _))
      simpa only [fouvryTau_two, tau] using sum_fouvryTau_div_le_real 2 hT

private theorem gcdSlice_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {p D : ℕ} (hp : 0 < p) (hD : 0 < D) (R : ℝ) :
    ‖gcdSlice d p D R‖ ≤
      |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 4 *
        (4 * d.U ^ 2 / (p : ℝ) ^ 2 * (tau D ^ 2 / (D : ℝ) ^ 2) +
          2 * d.U / (p : ℝ) * (tau D ^ 2 / (D : ℝ))) := by
  let K : ℝ := |CommonSmoothCutoff.cutoffMass| * d.V *
    (4 * d.U ^ 2 / (p : ℝ) ^ 2 + 2 * d.U * (D : ℝ) / (p : ℝ))
  have hV0 : 0 ≤ d.V := by linarith [hd.2.1]
  have hU0 : 0 ≤ d.U := by linarith [hd.1]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint {v w : ℕ}
      (hv : v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)))
      (hw : w ∈ Finset.Ioc 0 (Nat.floor (tailCap d))) :
      ‖if v.gcd w = D then
        tailGamma d v * star (tailGamma d w) * characterKernel d p v w R else 0‖ ≤
        K * multipleWeight D v * multipleWeight D w := by
    by_cases hg : v.gcd w = D
    · have hv0 := (Finset.mem_Ioc.mp hv).1
      have hw0 := (Finset.mem_Ioc.mp hw).1
      have hDv : D ∣ v := hg ▸ Nat.gcd_dvd_left v w
      have hDw : D ∣ w := hg ▸ Nat.gcd_dvd_right v w
      rw [if_pos hg, norm_mul, norm_mul, norm_star,
        multipleWeight, if_pos hDv, multipleWeight, if_pos hDw]
      refine (mul_le_mul
        (mul_le_mul (tailGamma_norm_le_tau hd v) (tailGamma_norm_le_tau hd w)
          (norm_nonneg _) (tau_nonneg v))
        (characterKernel_norm_le hd hp hv0 hw0 R) (norm_nonneg _)
        (mul_nonneg (tau_nonneg v) (tau_nonneg w))).trans_eq ?_
      rw [hg]
      dsimp only [K]
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv0.ne'
      have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw0.ne'
      field_simp [hpR, hvR, hwR]
    · rw [if_neg hg, norm_zero]
      exact mul_nonneg (mul_nonneg hK (multipleWeight_nonneg D v))
        (multipleWeight_nonneg D w)
  have hbase : ‖gcdSlice d p D R‖ ≤
      K * (∑ n ∈ Finset.Ioc 0 (Nat.floor (tailCap d)), multipleWeight D n) ^ 2 := by
    unfold gcdSlice
    calc
      _ ≤ ∑ v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
          ∑ w ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
            K * multipleWeight D v * multipleWeight D w := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro v hv
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro w hw
        exact hpoint hv hw
      _ = _ := by
        rw [pow_two, Finset.sum_mul_sum]
        simp only [Finset.mul_sum, mul_assoc]
  refine hbase.trans ?_
  have hsum0 : 0 ≤ ∑ n ∈ Finset.Ioc 0 (Nat.floor (tailCap d)), multipleWeight D n :=
    Finset.sum_nonneg (fun n _ ↦ multipleWeight_nonneg D n)
  refine (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hsum0 (multiple_harmonic_le (one_le_tailCap hd) hD) 2) hK).trans_eq ?_
  dsimp only [K]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp [hpR, hDR]

private theorem tau_square_harmonic_le {T : ℝ} (hT : 1 ≤ T) :
    (∑ D ∈ Finset.Ioc 0 (Nat.floor T), tau D ^ 2 / (D : ℝ)) ≤
      (1 + Real.log T) ^ 4 := by
  have hfour : (2 : ℕ) ^ 2 = 4 := by norm_num
  simpa only [fouvryTau_two, tau, hfour] using sum_fouvryTau_sq_div_le_real 2 hT

/-- This is a finite endpoint estimate. The inverse Y is retained before
the remaining divisor harmonic sum is enlarged. -/
private theorem reciprocal_square_tail_le
    {T Y : ℝ} (hT : 1 ≤ T) (hY : 1 ≤ Y) :
    (∑ D ∈ (Finset.Ioc 0 (Nat.floor T)).filter (fun D : ℕ ↦ Y < (D : ℝ)),
      tau D ^ 2 / (D : ℝ) ^ 2) ≤ (1 + Real.log T) ^ 4 / Y := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  calc
    _ ≤ ∑ D ∈ (Finset.Ioc 0 (Nat.floor T)).filter (fun D : ℕ ↦ Y < (D : ℝ)),
        (tau D ^ 2 / (D : ℝ)) / Y := by
      apply Finset.sum_le_sum
      intro D hD
      have hyD : Y < (D : ℝ) := (Finset.mem_filter.mp hD).2
      have hDR : 0 < (D : ℝ) := hY0.trans hyD
      calc
        _ = (tau D ^ 2 / (D : ℝ)) * (1 / (D : ℝ)) := by
          field_simp [hDR.ne']
        _ ≤ (tau D ^ 2 / (D : ℝ)) * (1 / Y) :=
          mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le hY0 hyD.le) (by positivity)
        _ = _ := by ring
    _ = (∑ D ∈ (Finset.Ioc 0 (Nat.floor T)).filter (fun D : ℕ ↦ Y < (D : ℝ)),
        tau D ^ 2 / (D : ℝ)) / Y := by rw [Finset.sum_div]
    _ ≤ (∑ D ∈ Finset.Ioc 0 (Nat.floor T), tau D ^ 2 / (D : ℝ)) / Y := by
      apply div_le_div_of_nonneg_right _ hY0.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun D _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ ≤ _ := div_le_div_of_nonneg_right (tau_square_harmonic_le hT) hY0.le

private theorem large_divisor_harmonic_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    (∑ D ∈ largeDivisors d Y, tau D ^ 2 / (D : ℝ)) ≤
      (1 + Real.log (tailCap d)) ^ 4 := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun D _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))).trans ?_
  exact tau_square_harmonic_le (one_le_tailCap hd)

private theorem one_p_large_divisor_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {p : ℕ} (hp : 0 < p) {Y : ℝ} (hY : 1 ≤ Y) (R : ℝ) :
    ‖∑ D ∈ largeDivisors d Y, gcdSlice d p D R‖ ≤
      |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 8 *
        (4 * d.U ^ 2 / ((p : ℝ) ^ 2 * Y) + 2 * d.U / (p : ℝ)) := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hV0 : 0 ≤ d.V := by linarith [hd.2.1]
  have hU0 : 0 ≤ d.U := by linarith [hd.1]
  have hlog0 : 0 ≤ 1 + Real.log (tailCap d) := by
    have := Real.log_nonneg (one_le_tailCap hd)
    linarith
  have hD2 : (∑ D ∈ largeDivisors d Y, tau D ^ 2 / (D : ℝ) ^ 2) ≤
      (1 + Real.log (tailCap d)) ^ 4 / Y :=
    reciprocal_square_tail_le (one_le_tailCap hd) hY
  have hD1 := large_divisor_harmonic_le hd Y
  calc
    _ ≤ ∑ D ∈ largeDivisors d Y,
        |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 4 *
          (4 * d.U ^ 2 / (p : ℝ) ^ 2 * (tau D ^ 2 / (D : ℝ) ^ 2) +
            2 * d.U / (p : ℝ) * (tau D ^ 2 / (D : ℝ))) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro D hD
      exact gcdSlice_norm_le hd hp
        (Finset.mem_Ioc.mp (Finset.mem_filter.mp hD).1).1 R
    _ = |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 4 *
        (4 * d.U ^ 2 / (p : ℝ) ^ 2 *
            (∑ D ∈ largeDivisors d Y, tau D ^ 2 / (D : ℝ) ^ 2) +
          2 * d.U / (p : ℝ) *
            (∑ D ∈ largeDivisors d Y, tau D ^ 2 / (D : ℝ))) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_assoc]
    _ ≤ |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 4 *
        (4 * d.U ^ 2 / (p : ℝ) ^ 2 * ((1 + Real.log (tailCap d)) ^ 4 / Y) +
          2 * d.U / (p : ℝ) * (1 + Real.log (tailCap d)) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hD2 (by positivity)
      · exact mul_le_mul_of_nonneg_left hD1 (by positivity)
    _ = _ := by
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      field_simp [hpR, hY0.ne']

private theorem primitive_factor_card_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.primitiveFirstFactorCarrier.card : ℝ) ≤ 2 * d.Q1 := by
  have hsub : d.primitiveFirstFactorCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.Q1)) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).1
    exact Finset.mem_Ioc.mpr ⟨(factor_bounds hd.2.2.1 hp').1,
      (Finset.mem_Icc.mp hp').2⟩
  have hc : (d.primitiveFirstFactorCarrier.card : ℝ) ≤
      (Nat.floor (2 * d.Q1) : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (by simp)
  exact hc.trans (Nat.floor_le (by linarith [hd.2.2.1]))

private theorem primitive_reciprocal_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ p ∈ d.primitiveFirstFactorCarrier, 1 / (p : ℝ)) ≤ 2 := by
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  calc
    _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier, 1 / d.Q1 := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hQ
        (factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1).2.1
    _ = (d.primitiveFirstFactorCarrier.card : ℝ) * (1 / d.Q1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d.Q1) * (1 / d.Q1) :=
      mul_le_mul_of_nonneg_right (primitive_factor_card_le hd) (by positivity)
    _ = 2 := by field_simp [hQ.ne']

private theorem primitive_reciprocal_square_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ p ∈ d.primitiveFirstFactorCarrier, 1 / (p : ℝ) ^ 2) ≤ 2 / d.Q1 := by
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  calc
    _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier, 1 / d.Q1 ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hlo := (factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1).2.1
      exact one_div_le_one_div_of_le (sq_pos_of_pos hQ)
        (pow_le_pow_left₀ hQ.le hlo 2)
    _ = (d.primitiveFirstFactorCarrier.card : ℝ) * (1 / d.Q1 ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d.Q1) * (1 / d.Q1 ^ 2) :=
      mul_le_mul_of_nonneg_right (primitive_factor_card_le hd) (by positivity)
    _ = 2 / d.Q1 := by field_simp [hQ.ne']

private theorem actual_finite_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {Y : ℝ} (hY : 1 ≤ Y) (R : ℝ) :
    ‖d.sharedFirstFactorLargeResidualHighConductorZero Y R‖ ≤
      |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 8 *
        (8 * d.U ^ 2 / (d.Q1 * Y) + 4 * d.U) := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ0 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hU0 : 0 ≤ d.U := by linarith [hd.1]
  have hV0 : 0 ≤ d.V := by linarith [hd.2.1]
  have hL0 : 0 ≤ 1 + Real.log (tailCap d) := by
    have := Real.log_nonneg (one_le_tailCap hd)
    linarith
  rw [actual_eq_gcd_slices hd]
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 8 *
          (4 * d.U ^ 2 / ((p : ℝ) ^ 2 * Y) + 2 * d.U / (p : ℝ)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      exact one_p_large_divisor_norm_le hd
        (factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1).1 hY R
    _ = |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 8 *
        ((4 * d.U ^ 2 / Y) *
            (∑ p ∈ d.primitiveFirstFactorCarrier, 1 / (p : ℝ) ^ 2) +
          (2 * d.U) * (∑ p ∈ d.primitiveFirstFactorCarrier, 1 / (p : ℝ))) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 8 *
        ((4 * d.U ^ 2 / Y) * (2 / d.Q1) + (2 * d.U) * 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (primitive_reciprocal_square_le hd) (by positivity))
        (mul_le_mul_of_nonneg_left (primitive_reciprocal_le hd) (by positivity))
    _ = _ := by
      field_simp [hY0.ne', hQ0.ne']; ring

end SharedFirstFactorLargeResidualZero

/-- A universal finite bound on the literal original high-conductor,
large-residual zero covariance. There is no SW or large-sieve supplier. -/
theorem actual_largeResidualHighConductorZero_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        MediumAdmissible B sigma kappa c0 d → ∀ Y R : ℝ, 1 ≤ Y →
          ‖d.sharedFirstFactorLargeResidualHighConductorZero Y R‖ ≤
            C * d.V * (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 8 *
              (d.U ^ 2 / (d.Q1 * Y) + d.U) := by
  refine ⟨8 * (1 + |CommonSmoothCutoff.cutoffMass|), by positivity,
    fun B sigma kappa c0 d hd Y R hY ↦ ?_⟩
  refine (SharedFirstFactorLargeResidualZero.actual_finite_bound hd hY R).trans ?_
  have hU : 0 ≤ d.U := by linarith [hd.1]
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hL : 0 ≤ 1 + Real.log (4 * d.Q2 * d.Q3) := by
    have := Real.log_nonneg (SharedFirstFactorLargeResidualZero.one_le_tailCap hd)
    change 0 ≤ 1 + Real.log (SharedFirstFactorLargeResidualZero.tailCap d)
    linarith
  change |CommonSmoothCutoff.cutoffMass| * d.V *
    (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 8 *
      (8 * d.U ^ 2 / (d.Q1 * Y) + 4 * d.U) ≤ _
  have ht : 0 ≤ d.U ^ 2 / (d.Q1 * Y) := by positivity
  have hbracket : 8 * d.U ^ 2 / (d.Q1 * Y) + 4 * d.U ≤
      8 * (d.U ^ 2 / (d.Q1 * Y) + d.U) := by
    rw [mul_div_assoc]
    nlinarith
  calc
    _ ≤ |CommonSmoothCutoff.cutoffMass| * d.V *
        (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 8 *
          (8 * (d.U ^ 2 / (d.Q1 * Y) + d.U)) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ (1 + |CommonSmoothCutoff.cutoffMass|) * d.V *
        (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 8 *
          (8 * (d.U ^ 2 / (d.Q1 * Y) + d.U)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hV
      linarith
    _ = _ := by ring

/-- The original outside beta and gamma1 factors are paid without an
epsilon power loss; both geometric savings remain explicit. -/
theorem actual_outside_mul_largeResidualHighConductorZero_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        MediumAdmissible B sigma kappa c0 d → ∀ Y R : ℝ, 1 ≤ Y →
          ((∑ m ∈ d.betaCarrier, ‖d.beta m‖ ^ 2) *
              (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)) *
            ‖d.sharedFirstFactorLargeResidualHighConductorZero Y R‖ ≤
              C * d.scale ^ 2 *
                (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
                (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 8 *
                (1 / Y + d.Q1 / d.U) := by
  obtain ⟨C, hC, hbound⟩ := actual_largeResidualHighConductorZero_bound
  refine ⟨4 * C, by positivity, fun B sigma kappa c0 d hd Y R hY ↦ ?_⟩
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hLV : 0 ≤ 1 + Real.log (2 * d.V) := by
    have := Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])
    linarith
  have hLT : 0 ≤ 1 + Real.log (4 * d.Q2 * d.Q3) := by
    have := Real.log_nonneg (SharedFirstFactorLargeResidualZero.one_le_tailCap hd)
    change 0 ≤ 1 + Real.log (SharedFirstFactorLargeResidualZero.tailCap d)
    linarith
  refine (mul_le_mul (d.sharedFirstFactor_outside_le hd)
    (hbound B sigma kappa c0 d hd Y R hY) (norm_nonneg _) (by positivity)).trans_eq ?_
  unfold MediumAtom.scale
  field_simp [hU.ne', hQ.ne', hY0.ne']

end

end ImbalancedChen.Part3
