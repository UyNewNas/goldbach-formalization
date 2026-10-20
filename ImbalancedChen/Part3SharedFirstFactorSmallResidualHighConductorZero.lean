import ImbalancedChen.Part3SharedFirstFactorCharacterDictionary
import ImbalancedChen.Part3SharedFirstFactorHighConductor

/-!
# The actual small-residual high-conductor zero covariance

The two physical tail products are grouped exactly before any norm.
Their gcd fixes the full character level p*D throughout the subsequent
nonnegative enlargement. The original alpha interval is extended once
by zero and conjugated before the generic high-conductor mean is used.
There is no supplied mean-value hypothesis and no grouped unit bound.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators Pointwise
open SharedFirstFactorCharacterDictionary
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace SharedFirstFactorSmallResidualHighConductorZero

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

private def smallDivisors (d : MediumAtom) (Y : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 (Nat.floor (tailCap d))).filter (fun D ↦ (D : ℝ) ≤ Y)

end SharedFirstFactorSmallResidualHighConductorZero

open SharedFirstFactorSmallResidualHighConductorZero

/-- The literal zero-mode dictionary restricted to high conductor and
small gcd of the two remaining physical factor products. -/
def MediumAtom.sharedFirstFactorSmallResidualHighConductorZero
    (d : MediumAtom) (Y R : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    ∑ u ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
      ∑ v ∈ factorCarrier d.Q2 ×ˢ factorCarrier d.Q3,
        if ((u.1 * u.2).gcd (v.1 * v.2) : ℝ) ≤ Y then
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

namespace SharedFirstFactorSmallResidualHighConductorZero

/-- The actual signed expression is grouped twice before any norm:
first by each full tail product, then by their exact gcd. -/
private theorem actual_eq_gcd_slices
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y R : ℝ) :
    d.sharedFirstFactorSmallResidualHighConductorZero Y R =
      ∑ p ∈ d.primitiveFirstFactorCarrier,
        ∑ D ∈ smallDivisors d Y, gcdSlice d p D R := by
  unfold MediumAtom.sharedFirstFactorSmallResidualHighConductorZero
  apply Finset.sum_congr rfl
  intro p _
  calc
    _ = ∑ u ∈ tailLabels d, ∑ v ∈ tailLabels d,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
          (if ((u.1 * u.2).gcd (v.1 * v.2) : ℝ) ≤ Y then
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
            (if (v.gcd w : ℝ) ≤ Y then characterKernel d p v w R else 0) :=
      tail_pair_sum_eq_prefix hd (fun v w ↦
        if (v.gcd w : ℝ) ≤ Y then characterKernel d p v w R else 0)
    _ = ∑ D ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
        ∑ v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
          ∑ w ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
            if v.gcd w = D then tailGamma d v * star (tailGamma d w) *
              (if (v.gcd w : ℝ) ≤ Y then characterKernel d p v w R else 0) else 0 :=
      pair_sum_by_gcd _ _
    _ = _ := by
      rw [smallDivisors, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro D _
      by_cases hY : (D : ℝ) ≤ Y
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

private def alphaStar (d : MediumAtom) (n : ℕ) : ℂ :=
  if n ∈ d.alphaCarrier then star (d.alpha n) else 0

private def commonLog (d : MediumAtom) : ℝ :=
  1 + Real.log (32 * d.U * d.Q1 * d.Q2 * d.Q3)

private def highEnergy (d : MediumAtom) (k q : ℕ) (R : ℝ) : ℝ :=
  ((q : ℝ) / (q.totient : ℝ)) *
    ∑ chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
        (fun chi ↦ R < (chi.conductor : ℝ)),
      ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k q chi‖ ^ 2

private theorem highEnergy_nonneg (d : MediumAtom) (k q : ℕ) (R : ℝ) :
    0 ≤ highEnergy d k q R := by
  unfold highEnergy
  positivity

private theorem alpha_subset_Icc
    {d : MediumAtom} (hU : 1 ≤ d.U) :
    d.alphaCarrier ⊆ Finset.Icc 1 (Nat.floor (2 * d.U)) := by
  intro n hn
  obtain ⟨hn, _⟩ := Finset.mem_filter.mp hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hc : 1 ≤ Nat.ceil d.U := by exact_mod_cast hU.trans (Nat.le_ceil d.U)
  exact Finset.mem_Icc.mpr ⟨hc.trans hlo, hhi⟩

private theorem alpha_prefix_pos {d : MediumAtom} (hU : 1 ≤ d.U) :
    0 < Nat.floor (2 * d.U) := by
  exact (Nat.one_le_floor_iff (2 * d.U)).mpr (by linarith)

/-- One sequence, zero-extended before all physical levels and auxiliary
factors, gives the precise conjugation bridge to the generic mean. -/
private theorem auxiliary_star_bridge
    {d : MediumAtom} (hU : 1 ≤ d.U) (k q : ℕ)
    (chi : DirichletCharacter ℂ q) :
    auxiliaryCharacterSum d.alphaCarrier d.alpha k q chi =
      star (∑ n ∈ Finset.Icc 1 (Nat.floor (2 * d.U)),
        (if n.Coprime k then alphaStar d n else 0) * chi (n : ZMod q)) := by
  calc
    _ = ∑ n ∈ d.alphaCarrier,
        star ((if n.Coprime k then alphaStar d n else 0) * chi (n : ZMod q)) := by
      unfold auxiliaryCharacterSum
      apply Finset.sum_congr rfl
      intro n hn
      unfold alphaStar
      rw [if_pos hn]
      by_cases hk : n.Coprime k
      · simp only [if_pos hk, star_mul', star_star]
      · simp only [if_neg hk, zero_mul, star_zero]
    _ = ∑ n ∈ Finset.Icc 1 (Nat.floor (2 * d.U)),
        star ((if n.Coprime k then alphaStar d n else 0) * chi (n : ZMod q)) := by
      apply Finset.sum_subset (alpha_subset_Icc hU)
      intro n _ hn
      unfold alphaStar
      simp only [if_neg hn, ite_self, zero_mul, star_zero]
    _ = _ := (star_sum _ _).symm

private theorem alphaStar_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖alphaStar d n‖ ≤ 1 := by
  unfold alphaStar
  by_cases hn : n ∈ d.alphaCarrier
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ha, _⟩ := hd
    simpa only [if_pos hn, norm_star] using ha n hn
  · simp only [if_neg hn, norm_zero, zero_le_one]

private theorem commonLog_one_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ commonLog d := by
  have h12 : 1 ≤ d.U * d.Q1 := by
    simpa only [one_mul] using mul_le_mul hd.1 hd.2.2.1
      zero_le_one (by linarith [hd.1] : 0 ≤ d.U)
  have h123 : 1 ≤ d.U * d.Q1 * d.Q2 := by
    simpa only [one_mul] using mul_le_mul h12 hd.2.2.2.1
      zero_le_one (by linarith [h12] : 0 ≤ d.U * d.Q1)
  have h1234 : 1 ≤ d.U * d.Q1 * d.Q2 * d.Q3 := by
    simpa only [one_mul] using mul_le_mul h123 hd.2.2.2.2.1
      zero_le_one (by linarith [h123] : 0 ≤ d.U * d.Q1 * d.Q2)
  have harg : 1 ≤ 32 * d.U * d.Q1 * d.Q2 * d.Q3 := by
    nlinarith only [h1234]
  unfold commonLog
  linarith [Real.log_nonneg harg]

private theorem tail_log_le_commonLog
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    1 + Real.log (tailCap d) ≤ commonLog d := by
  have hT0 : 0 < tailCap d := zero_lt_one.trans_le (one_le_tailCap hd)
  have hU := hd.1
  have hQ := hd.2.2.1
  have h2 := hd.2.2.2.1
  have h3 := hd.2.2.2.2.1
  have harg : tailCap d ≤ 32 * d.U * d.Q1 * d.Q2 * d.Q3 := by
    calc
      tailCap d = 4 * (1 : ℝ) * 1 * d.Q2 * d.Q3 := by unfold tailCap; ring
      _ ≤ 32 * d.U * d.Q1 * d.Q2 * d.Q3 := by
        gcongr; first | assumption | norm_num
  exact add_le_add le_rfl (Real.log_le_log hT0 harg)

private theorem floor_inverse_rpow_le
    {eta R : ℝ} (heta : 0 < eta) (heta1 : eta < 1) (hR : 1 ≤ R) :
    1 / (Nat.floor R : ℝ) ^ (1 - eta) ≤ 2 / R ^ (1 - eta) := by
  have hr : 1 ≤ Nat.floor R := (Nat.one_le_floor_iff R).mpr hR
  have hrR : (1 : ℝ) ≤ Nat.floor R := by exact_mod_cast hr
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hr0 : (0 : ℝ) < Nat.floor R := zero_lt_one.trans_le hrR
  have hRr : R ≤ 2 * (Nat.floor R : ℝ) := by
    have hf := Nat.lt_floor_add_one R
    linarith
  have he : 0 ≤ 1 - eta := by linarith
  have htwo : (2 : ℝ) ^ (1 - eta) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hp : R ^ (1 - eta) ≤ 2 * (Nat.floor R : ℝ) ^ (1 - eta) := by
    calc
      _ ≤ (2 * (Nat.floor R : ℝ)) ^ (1 - eta) :=
        Real.rpow_le_rpow hR0.le hRr he
      _ = (2 : ℝ) ^ (1 - eta) * (Nat.floor R : ℝ) ^ (1 - eta) :=
        Real.mul_rpow (by norm_num) hr0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hr0.le _)
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hr0 _) (Real.rpow_pos_of_pos hR0 _)).mpr
  simpa only [one_mul] using hp

/-- The named generic high-conductor theorem is applied to the one
original-alpha sequence. No mean-value hypothesis is supplied. -/
private theorem actual_real_cutoff_mean
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        MediumAdmissible B sigma kappa c0 d →
        ∀ Q k : ℕ, 0 < Q → 0 < k → ∀ R : ℝ, 1 ≤ R →
          (∑ q ∈ Finset.Icc 1 Q, highEnergy d k q R) ≤
            C * (1 + Real.log (2 * (Nat.floor (2 * d.U) : ℝ) * (Q : ℝ))) ^ 12 *
              ((Q : ℝ) * (Nat.floor (2 * d.U) : ℝ) ^ 2 /
                  (Nat.floor R : ℝ) ^ (1 - eta) +
                (Q : ℝ) ^ (2 + eta) * (Nat.floor (2 * d.U) : ℝ)) := by
  obtain ⟨C, hC, hm⟩ := SharedFirstFactorHighConductor.auxiliary_highConductor_mean_le
    heta heta1
  refine ⟨C, hC, fun B sigma kappa c0 d hd Q k hQ hk R hR ↦ ?_⟩
  have hr : 0 < Nat.floor R := (Nat.one_le_floor_iff R).mpr hR
  have hfilter (q : ℕ) :
      (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun chi ↦ R < (chi.conductor : ℝ)) =
        (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun chi ↦ Nat.floor R < chi.conductor) := by
    apply Finset.filter_congr
    intro chi _
    exact (Nat.floor_lt (by linarith : 0 ≤ R)).symm
  have hmean := hm (Nat.floor (2 * d.U)) Q (Nat.floor R) k
    (alpha_prefix_pos hd.1) hQ hr hk (alphaStar d)
    (fun n _ ↦ alphaStar_norm_le_one hd n)
  refine le_trans (le_of_eq ?_) hmean
  apply Finset.sum_congr rfl
  intro q _
  rw [highEnergy, hfilter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  rw [auxiliary_star_bridge hd.1, norm_star]

private theorem physical_level_image_subset
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (hD : 0 < D) :
    (d.primitiveFirstFactorCarrier.image (fun p ↦ p * D)) ⊆
      Finset.Icc 1 (Nat.floor (2 * d.Q1) * D) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  have hp' := (Finset.mem_filter.mp hp).1
  exact Finset.mem_Icc.mpr
    ⟨Nat.mul_pos (factor_bounds hd.2.2.1 hp').1 hD,
      Nat.mul_le_mul_right D (Finset.mem_Icc.mp hp').2⟩

private theorem physical_level_mean_le
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        MediumAdmissible B sigma kappa c0 d →
        ∀ D k : ℕ, 0 < D → (D : ℝ) ≤ tailCap d → 0 < k →
          ∀ R : ℝ, 1 ≤ R →
            (∑ p ∈ d.primitiveFirstFactorCarrier, highEnergy d k (p * D) R) ≤
              C * commonLog d ^ 12 *
                (d.Q1 * (D : ℝ) * d.U ^ 2 / R ^ (1 - eta) +
                  d.Q1 ^ (2 + eta) * (D : ℝ) ^ (2 + eta) * d.U) := by
  obtain ⟨C, hC, hmean⟩ := actual_real_cutoff_mean heta heta1
  refine ⟨16 * C, by positivity,
    fun B sigma kappa c0 d hd D k hD hDT hk R hR ↦ ?_⟩
  let N : ℕ := Nat.floor (2 * d.U)
  let P : ℕ := Nat.floor (2 * d.Q1)
  let Q : ℕ := P * D
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hN : 0 < N := alpha_prefix_pos hd.1
  have hP : 0 < P := (Nat.one_le_floor_iff (2 * d.Q1)).mpr (by linarith [hd.2.2.1])
  have hQ : 0 < Q := Nat.mul_pos hP hD
  have hNr : (N : ℝ) ≤ 2 * d.U := Nat.floor_le (by linarith)
  have hPr : (P : ℝ) ≤ 2 * d.Q1 := Nat.floor_le (by linarith)
  have hQr : (Q : ℝ) ≤ 2 * d.Q1 * (D : ℝ) := by
    dsimp only [Q]
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hPr hDR.le
  have hlog : 1 + Real.log (2 * (N : ℝ) * (Q : ℝ)) ≤ commonLog d := by
    change 1 + Real.log (2 * (N : ℝ) * (Q : ℝ)) ≤
      1 + Real.log (32 * d.U * d.Q1 * d.Q2 * d.Q3)
    apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    calc
      2 * (N : ℝ) * (Q : ℝ) ≤ 2 * (2 * d.U) * (2 * d.Q1 * (D : ℝ)) := by
        gcongr
      _ ≤ 2 * (2 * d.U) * (2 * d.Q1 * tailCap d) := by gcongr
      _ = 32 * d.U * d.Q1 * d.Q2 * d.Q3 := by unfold tailCap; ring
  have hlog0 : 0 ≤ 1 + Real.log (2 * (N : ℝ) * (Q : ℝ)) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hQ1' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have := Real.log_nonneg (show 1 ≤ 2 * (N : ℝ) * (Q : ℝ) by nlinarith)
    linarith
  have hRpow : 0 < R ^ (1 - eta) := Real.rpow_pos_of_pos (by linarith) _
  have hfirst : (Q : ℝ) * (N : ℝ) ^ 2 / (Nat.floor R : ℝ) ^ (1 - eta) ≤
      16 * (d.Q1 * (D : ℝ) * d.U ^ 2 / R ^ (1 - eta)) := by
    calc
      _ = ((Q : ℝ) * (N : ℝ) ^ 2) *
          (1 / (Nat.floor R : ℝ) ^ (1 - eta)) := by ring
      _ ≤ ((2 * d.Q1 * (D : ℝ)) * (2 * d.U) ^ 2) * (2 / R ^ (1 - eta)) := by
        apply mul_le_mul
        · exact mul_le_mul hQr (pow_le_pow_left₀ (Nat.cast_nonneg _) hNr 2)
            (sq_nonneg _) (by positivity)
        · exact floor_inverse_rpow_le heta heta1 hR
        · positivity
        · positivity
      _ = _ := by ring
  have he : 0 ≤ 2 + eta := by linarith
  have htwo : (2 : ℝ) ^ (2 + eta) ≤ 8 := by
    calc
      _ ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 := by norm_num
  have hsecond : (Q : ℝ) ^ (2 + eta) * (N : ℝ) ≤
      16 * (d.Q1 ^ (2 + eta) * (D : ℝ) ^ (2 + eta) * d.U) := by
    calc
      _ ≤ (2 * d.Q1 * (D : ℝ)) ^ (2 + eta) * (2 * d.U) := by
        exact mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) hQr he) hNr
          (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
      _ = (2 : ℝ) ^ (2 + eta) * d.Q1 ^ (2 + eta) *
          (D : ℝ) ^ (2 + eta) * (2 * d.U) := by
        rw [Real.mul_rpow (by positivity) hDR.le,
          Real.mul_rpow (by norm_num) hQ1.le]
      _ ≤ 8 * d.Q1 ^ (2 + eta) * (D : ℝ) ^ (2 + eta) * (2 * d.U) := by
        gcongr
      _ = _ := by ring
  have hsum : (∑ p ∈ d.primitiveFirstFactorCarrier, highEnergy d k (p * D) R) ≤
      ∑ q ∈ Finset.Icc 1 Q, highEnergy d k q R := by
    calc
      _ = ∑ q ∈ d.primitiveFirstFactorCarrier.image (fun p ↦ p * D),
          highEnergy d k q R := by
        rw [Finset.sum_image]
        intro p _ q _ hpq
        exact Nat.eq_of_mul_eq_mul_right hD hpq
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (physical_level_image_subset hd hD)
        (fun q _ _ ↦ highEnergy_nonneg d k q R)
  refine hsum.trans ((hmean B sigma kappa c0 d hd Q k hQ hk R hR).trans ?_)
  have hbracket : 0 ≤ (Q : ℝ) * (N : ℝ) ^ 2 / (Nat.floor R : ℝ) ^ (1 - eta) +
      (Q : ℝ) ^ (2 + eta) * (N : ℝ) := by positivity
  calc
    _ ≤ C * commonLog d ^ 12 *
        ((Q : ℝ) * (N : ℝ) ^ 2 / (Nat.floor R : ℝ) ^ (1 - eta) +
          (Q : ℝ) ^ (2 + eta) * (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 12) hC.le) hbracket
    _ ≤ C * commonLog d ^ 12 *
        (16 * (d.Q1 * (D : ℝ) * d.U ^ 2 / R ^ (1 - eta)) +
          16 * (d.Q1 ^ (2 + eta) * (D : ℝ) ^ (2 + eta) * d.U)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by positivity)
    _ = _ := by ring


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

private def quotientCarrier (d : MediumAtom) (D : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (Nat.floor (tailCap d) / D)

private def tailWeight (d : MediumAtom) (D k : ℕ) : ℝ :=
  ‖tailGamma d (D * k)‖ / (k : ℝ)

private theorem tailWeight_nonneg (d : MediumAtom) (D k : ℕ) :
    0 ≤ tailWeight d D k := by unfold tailWeight; positivity

private theorem tailWeight_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (D : ℕ) :
    (∑ k ∈ quotientCarrier d D, tailWeight d D k) ≤
      tau D * (1 + Real.log (tailCap d)) ^ 2 := by
  calc
    _ ≤ ∑ k ∈ quotientCarrier d D, tau D * (tau k / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _
      unfold tailWeight
      refine (div_le_div_of_nonneg_right
        ((tailGamma_norm_le_tau hd (D * k)).trans (tau_mul_le D k))
        (Nat.cast_nonneg _)).trans_eq ?_
      ring
    _ = tau D * ∑ k ∈ quotientCarrier d D, tau k / (k : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ tau D * ∑ k ∈ Finset.Ioc 0 (Nat.floor (tailCap d)), tau k / (k : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (tau_nonneg D)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hk).1,
          (Finset.mem_Ioc.mp hk).2.trans (Nat.div_le_self _ _)⟩
      · intro k _ _
        exact div_nonneg (tau_nonneg k) (Nat.cast_nonneg _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (tau_nonneg D)
      simpa only [tau, fouvryTau_two] using
        sum_fouvryTau_div_le_real 2 (one_le_tailCap hd)

private theorem weighted_young_sum_eq (S : Finset ℕ) (a E : ℕ → ℝ) :
    (∑ k ∈ S, ∑ l ∈ S, a k * a l * ((E k + E l) / 2)) =
      (∑ k ∈ S, a k) * (∑ k ∈ S, a k * E k) := by
  have hpoint (k l : ℕ) : a k * a l * ((E k + E l) / 2) =
      ((a k * E k) * a l + a k * (a l * E l)) / 2 := by ring
  simp_rw [hpoint]
  simp only [← Finset.sum_div, Finset.sum_add_distrib]
  rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
  ring

/-- Enlarge only the nonnegative square sums. The ambient level and
the conductor filter are common to k and l, and remain fixed. -/
private theorem weighted_cross_norm_le (d : MediumAtom) (k l delta : ℕ) (R : ℝ) :
    ((delta : ℝ) / (delta.totient : ℝ)) *
      ‖∑ chi ∈ ((Finset.univ : Finset (DirichletCharacter ℂ delta)).erase 1).filter
          (fun chi ↦ R < (chi.conductor : ℝ)),
        auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi *
          star (auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi)‖ ≤
      (highEnergy d k delta R + highEnergy d l delta R) / 2 := by
  let C := ((Finset.univ : Finset (DirichletCharacter ℂ delta)).erase 1).filter
    (fun chi ↦ R < (chi.conductor : ℝ))
  let F := (Finset.univ : Finset (DirichletCharacter ℂ delta)).filter
    (fun chi ↦ R < (chi.conductor : ℝ))
  have hCF : C ⊆ F := by
    intro chi hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩
  have hsq (j : ℕ) :
      (∑ chi ∈ C, ‖auxiliaryCharacterSum d.alphaCarrier d.alpha j delta chi‖ ^ 2) ≤
        ∑ chi ∈ F, ‖auxiliaryCharacterSum d.alphaCarrier d.alpha j delta chi‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hCF (fun _ _ _ ↦ sq_nonneg _)
  have hc : ‖∑ chi ∈ C,
      auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi *
        star (auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi)‖ ≤
      ((∑ chi ∈ F, ‖auxiliaryCharacterSum d.alphaCarrier d.alpha k delta chi‖ ^ 2) +
        (∑ chi ∈ F, ‖auxiliaryCharacterSum d.alphaCarrier d.alpha l delta chi‖ ^ 2)) / 2 := by
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
      _ ≤ _ := by linarith [hsq k, hsq l]
  refine (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq ?_
  unfold highEnergy
  dsimp only [F]
  ring

private theorem gcd_pair_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {p D v w : ℕ} (hp : 0 < p) (hD : 0 < D) (hv : 0 < v) (hw : 0 < w)
    (hg : v.gcd w = D) (R : ℝ) :
    ‖tailGamma d v * star (tailGamma d w) * characterKernel d p v w R‖ ≤
      (|CommonSmoothCutoff.cutoffMass| * d.V / ((p : ℝ) ^ 2 * (D : ℝ) ^ 2)) *
        tailWeight d D (v / D) * tailWeight d D (w / D) *
          ((highEnergy d (v / D) (p * D) R + highEnergy d (w / D) (p * D) R) / 2) := by
  have hDv : D ∣ v := hg ▸ Nat.gcd_dvd_left v w
  have hDw : D ∣ w := hg ▸ Nat.gcd_dvd_right v w
  have hvk : D * (v / D) = v := Nat.mul_div_cancel' hDv
  have hwl : D * (w / D) = w := Nat.mul_div_cancel' hDw
  have hk : 0 < v / D := Nat.div_pos (Nat.le_of_dvd hv hDv) hD
  have hl : 0 < w / D := Nat.div_pos (Nat.le_of_dvd hw hDw) hD
  have hL : 0 < v.lcm w := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hv.ne' hw.ne')
  have hphi : 0 < (p * D).totient := Nat.totient_pos.mpr (Nat.mul_pos hp hD)
  have hprod : (D : ℝ) * (v.lcm w : ℝ) = (v : ℝ) * w := by
    exact_mod_cast (hg ▸ Nat.gcd_mul_lcm v w)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hkR : ((v / D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hlR : ((w / D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have hLR : (v.lcm w : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hphiR : ((p * D).totient : ℝ) ≠ 0 := by exact_mod_cast hphi.ne'
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  have hnorm : ‖tailGamma d v * star (tailGamma d w) * characterKernel d p v w R‖ =
      (|CommonSmoothCutoff.cutoffMass| * d.V / ((p : ℝ) ^ 2 * (D : ℝ) ^ 2)) *
        tailWeight d D (v / D) * tailWeight d D (w / D) *
          (((p * D : ℕ) : ℝ) / ((p * D).totient : ℝ) *
            ‖∑ chi ∈ ((Finset.univ : Finset (DirichletCharacter ℂ (p * D))).erase 1).filter
                (fun chi ↦ R < (chi.conductor : ℝ)),
              auxiliaryCharacterSum d.alphaCarrier d.alpha (v / D) (p * D) chi *
                star (auxiliaryCharacterSum d.alphaCarrier d.alpha (w / D) (p * D) chi)‖) := by
    unfold characterKernel tailWeight
    rw [hg, hvk, hwl]
    simp only [norm_mul, norm_star, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hV, Complex.norm_natCast, Nat.cast_mul]
    have hvR : (D : ℝ) * ((v / D : ℕ) : ℝ) = (v : ℝ) := by exact_mod_cast hvk
    have hwR : (D : ℝ) * ((w / D : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast hwl
    have hLcast : (v.lcm w : ℝ) =
        (D : ℝ) * ((v / D : ℕ) : ℝ) * ((w / D : ℕ) : ℝ) := by
      apply (mul_left_cancel₀ hDR)
      calc
        (D : ℝ) * (v.lcm w : ℝ) = (v : ℝ) * w := hprod
        _ = (D : ℝ) * ((D : ℝ) * ((v / D : ℕ) : ℝ) * ((w / D : ℕ) : ℝ)) := by
          rw [← hvR, ← hwR]
          ring
    rw [hLcast]
    field_simp [hpR, hDR, hkR, hlR, hphiR]
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left (weighted_cross_norm_le d (v / D) (w / D) (p * D) R)
    (mul_nonneg (mul_nonneg
      (div_nonneg (mul_nonneg (abs_nonneg _) hV)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (tailWeight_nonneg d D (v / D))) (tailWeight_nonneg d D (w / D)))

/-- Extra pairs are inserted only after the exact gcd has fixed p*D.
Their character level is never recomputed from the extra pair. -/
private theorem gcdSlice_norm_le_energy
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {p D : ℕ} (hp : 0 < p) (hD : 0 < D) (R : ℝ) :
    ‖gcdSlice d p D R‖ ≤
      (|CommonSmoothCutoff.cutoffMass| * d.V / ((p : ℝ) ^ 2 * (D : ℝ) ^ 2)) *
        (∑ k ∈ quotientCarrier d D, tailWeight d D k) *
          (∑ k ∈ quotientCarrier d D, tailWeight d D k * highEnergy d k (p * D) R) := by
  let K := |CommonSmoothCutoff.cutoffMass| * d.V / ((p : ℝ) ^ 2 * (D : ℝ) ^ 2)
  let F : ℕ → ℕ → ℝ := fun k l ↦
    K * tailWeight d D k * tailWeight d D l *
      ((highEnergy d k (p * D) R + highEnergy d l (p * D) R) / 2)
  have hK : 0 ≤ K := by dsimp [K]; have := hd.2.1; positivity
  have hF (k l : ℕ) : 0 ≤ F k l := by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK (tailWeight_nonneg d D k))
      (tailWeight_nonneg d D l))
      (div_nonneg (add_nonneg (highEnergy_nonneg d k (p * D) R)
        (highEnergy_nonneg d l (p * D) R)) (by norm_num))
  have hpoint {v w : ℕ}
      (hv : v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)))
      (hw : w ∈ Finset.Ioc 0 (Nat.floor (tailCap d))) :
      ‖if v.gcd w = D then
        tailGamma d v * star (tailGamma d w) * characterKernel d p v w R else 0‖ ≤
        if D ∣ v then (if D ∣ w then F (v / D) (w / D) else 0) else 0 := by
    by_cases hg : v.gcd w = D
    · have hDv : D ∣ v := hg ▸ Nat.gcd_dvd_left v w
      have hDw : D ∣ w := hg ▸ Nat.gcd_dvd_right v w
      rw [if_pos hg, if_pos hDv, if_pos hDw]
      exact gcd_pair_norm_le hd hp hD (Finset.mem_Ioc.mp hv).1 (Finset.mem_Ioc.mp hw).1 hg R
    · rw [if_neg hg, norm_zero]
      split_ifs <;> first | exact hF _ _ | exact le_rfl
  unfold gcdSlice
  calc
    _ ≤ ∑ v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
        ∑ w ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
          if D ∣ v then (if D ∣ w then F (v / D) (w / D) else 0) else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro v hv
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro w hw
      exact hpoint hv hw
    _ = ∑ v ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
        if D ∣ v then (∑ w ∈ Finset.Ioc 0 (Nat.floor (tailCap d)),
          if D ∣ w then F (v / D) (w / D) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp
    _ = ∑ k ∈ quotientCarrier d D, ∑ l ∈ quotientCarrier d D, F k l := by
      rw [sum_multiples_real _ _ hD]
      apply Finset.sum_congr rfl
      intro k _
      rw [sum_multiples_real _ _ hD]
      simp only [Nat.mul_div_cancel_left _ hD]
      rfl
    _ = _ := by
      dsimp only [F, K]
      have hY := weighted_young_sum_eq (quotientCarrier d D)
        (tailWeight d D) (fun k ↦ highEnergy d k (p * D) R)
      calc
        _ = (|CommonSmoothCutoff.cutoffMass| * d.V / ((p : ℝ) ^ 2 * (D : ℝ) ^ 2)) *
            ∑ k ∈ quotientCarrier d D, ∑ l ∈ quotientCarrier d D,
              tailWeight d D k * tailWeight d D l *
                ((highEnergy d k (p * D) R + highEnergy d l (p * D) R) / 2) := by
          simp only [Finset.mul_sum, mul_assoc]
        _ = _ := by rw [hY]; ring

private theorem shared_gcd_sum_norm_le_energy
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {D : ℕ} (hD : 0 < D) (R : ℝ) :
    ‖∑ p ∈ d.primitiveFirstFactorCarrier, gcdSlice d p D R‖ ≤
      (|CommonSmoothCutoff.cutoffMass| * d.V / (d.Q1 ^ 2 * (D : ℝ) ^ 2)) *
        (∑ k ∈ quotientCarrier d D, tailWeight d D k) *
          (∑ k ∈ quotientCarrier d D, tailWeight d D k *
            (∑ p ∈ d.primitiveFirstFactorCarrier, highEnergy d k (p * D) R)) := by
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        (|CommonSmoothCutoff.cutoffMass| * d.V / ((p : ℝ) ^ 2 * (D : ℝ) ^ 2)) *
          (∑ k ∈ quotientCarrier d D, tailWeight d D k) *
            (∑ k ∈ quotientCarrier d D, tailWeight d D k * highEnergy d k (p * D) R) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      exact gcdSlice_norm_le_energy hd
        (factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1).1 hD R
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        (|CommonSmoothCutoff.cutoffMass| * d.V / (d.Q1 ^ 2 * (D : ℝ) ^ 2)) *
          (∑ k ∈ quotientCarrier d D, tailWeight d D k) *
            (∑ k ∈ quotientCarrier d D, tailWeight d D k * highEnergy d k (p * D) R) := by
      apply Finset.sum_le_sum
      intro p hp
      have hlo := (factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1).2.1
      apply mul_le_mul_of_nonneg_right _
        (Finset.sum_nonneg (fun k _ ↦ mul_nonneg (tailWeight_nonneg d D k)
          (highEnergy_nonneg d k (p * D) R)))
      apply mul_le_mul_of_nonneg_right _
        (Finset.sum_nonneg (fun k _ ↦ tailWeight_nonneg d D k))
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hQ.le hlo 2) (sq_nonneg _))
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]

private theorem tau_square_harmonic_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y : ℝ) :
    (∑ D ∈ smallDivisors d Y, tau D ^ 2 / (D : ℝ)) ≤ commonLog d ^ 4 := by
  have hfull : (∑ D ∈ Finset.Ioc 0 (Nat.floor (tailCap d)), tau D ^ 2 / (D : ℝ)) ≤
      (1 + Real.log (tailCap d)) ^ 4 := by
    have hfour : (2 : ℕ) ^ 2 = 4 := by norm_num
    simpa only [tau, fouvryTau_two, hfour] using
      sum_fouvryTau_sq_div_le_real 2 (one_le_tailCap hd)
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun D _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))).trans (hfull.trans ?_)
  exact pow_le_pow_left₀ (by linarith [Real.log_nonneg (one_le_tailCap hd)])
    (tail_log_le_commonLog hd) 4

private theorem tau_square_power_sum_le
    {B : ℕ} {sigma kappa c0 eta : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (heta : 0 < eta)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∑ D ∈ smallDivisors d Y, tau D ^ 2 * (D : ℝ) ^ eta) ≤
      Y ^ (1 + eta) * commonLog d ^ 4 := by
  calc
    _ ≤ ∑ D ∈ smallDivisors d Y, Y ^ (1 + eta) * (tau D ^ 2 / (D : ℝ)) := by
      apply Finset.sum_le_sum
      intro D hD
      obtain ⟨hD, hDY⟩ := Finset.mem_filter.mp hD
      have hDR : (0 : ℝ) < D := by exact_mod_cast (Finset.mem_Ioc.mp hD).1
      calc
        _ = (D : ℝ) ^ (1 + eta) * (tau D ^ 2 / (D : ℝ)) := by
          rw [Real.rpow_add hDR 1 eta, Real.rpow_one]
          field_simp [hDR.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hDR.le hDY (by linarith)) (by positivity)
    _ = Y ^ (1 + eta) * ∑ D ∈ smallDivisors d Y, tau D ^ 2 / (D : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (tau_square_harmonic_le hd Y)
      (Real.rpow_nonneg (by linarith : 0 ≤ Y) _)

end SharedFirstFactorSmallResidualHighConductorZero

open SharedFirstFactorSmallResidualHighConductorZero

/-- The complete physical small-residual high-conductor estimate.
The constant precedes the varying atom and both cutoffs. -/
theorem actual_smallResidualHighConductorZero_bound
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        MediumAdmissible B sigma kappa c0 d →
        ∀ Y R : ℝ, 1 ≤ Y → 1 ≤ R →
          ‖d.sharedFirstFactorSmallResidualHighConductorZero Y R‖ ≤
            C * d.V * (1 + Real.log (32 * d.U * d.Q1 * d.Q2 * d.Q3)) ^ 20 *
              (d.U ^ 2 / (d.Q1 * R ^ (1 - eta)) +
                d.Q1 ^ eta * Y ^ (1 + eta) * d.U) := by
  obtain ⟨C, hC, hlevel⟩ := physical_level_mean_le heta heta1
  refine ⟨(1 + |CommonSmoothCutoff.cutoffMass|) * C, by positivity,
    fun B sigma kappa c0 d hd Y R hY hR ↦ ?_⟩
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hH : 1 ≤ commonLog d := commonLog_one_le hd
  have hT : 0 ≤ 1 + Real.log (tailCap d) := by
    linarith [Real.log_nonneg (one_le_tailCap hd)]
  have hW (D : ℕ) : (∑ k ∈ quotientCarrier d D, tailWeight d D k) ≤
      tau D * commonLog d ^ 2 := by
    exact (tailWeight_sum_le hd D).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hT (tail_log_le_commonLog hd) 2) (tau_nonneg D))
  have hDpoint {D : ℕ} (hD : D ∈ smallDivisors d Y) :
      ‖∑ p ∈ d.primitiveFirstFactorCarrier, gcdSlice d p D R‖ ≤
        |CommonSmoothCutoff.cutoffMass| * C * d.V * commonLog d ^ 16 *
          (tau D ^ 2 / (D : ℝ) * (d.U ^ 2 / (d.Q1 * R ^ (1 - eta))) +
            tau D ^ 2 * (D : ℝ) ^ eta * (d.Q1 ^ eta * d.U)) := by
    have hDmem := (Finset.mem_filter.mp hD).1
    have hD0 := (Finset.mem_Ioc.mp hDmem).1
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
    have hDT : (D : ℝ) ≤ tailCap d :=
      (show (D : ℝ) ≤ (Nat.floor (tailCap d) : ℝ) by
        exact_mod_cast (Finset.mem_Ioc.mp hDmem).2).trans
          (Nat.floor_le (by linarith [one_le_tailCap hd]))
    let A : ℝ := d.Q1 * (D : ℝ) * d.U ^ 2 / R ^ (1 - eta) +
      d.Q1 ^ (2 + eta) * (D : ℝ) ^ (2 + eta) * d.U
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hinner :
        (∑ k ∈ quotientCarrier d D, tailWeight d D k *
          (∑ p ∈ d.primitiveFirstFactorCarrier, highEnergy d k (p * D) R)) ≤
            C * commonLog d ^ 12 * A *
              (∑ k ∈ quotientCarrier d D, tailWeight d D k) := by
      calc
        _ ≤ ∑ k ∈ quotientCarrier d D, tailWeight d D k *
            (C * commonLog d ^ 12 * A) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left
            (hlevel B sigma kappa c0 d hd D k hD0 hDT (Finset.mem_Ioc.mp hk).1 R hR)
            (tailWeight_nonneg d D k)
        _ = _ := by rw [← Finset.sum_mul]; ring
    have hW0 : 0 ≤ ∑ k ∈ quotientCarrier d D, tailWeight d D k :=
      Finset.sum_nonneg (fun k _ ↦ tailWeight_nonneg d D k)
    calc
      _ ≤ (|CommonSmoothCutoff.cutoffMass| * d.V / (d.Q1 ^ 2 * (D : ℝ) ^ 2)) *
          (∑ k ∈ quotientCarrier d D, tailWeight d D k) *
            (C * commonLog d ^ 12 * A *
              (∑ k ∈ quotientCarrier d D, tailWeight d D k)) := by
        exact (shared_gcd_sum_norm_le_energy hd hD0 R).trans
          (mul_le_mul_of_nonneg_left hinner (by positivity))
      _ = (|CommonSmoothCutoff.cutoffMass| * d.V / (d.Q1 ^ 2 * (D : ℝ) ^ 2)) *
          C * commonLog d ^ 12 * A *
            (∑ k ∈ quotientCarrier d D, tailWeight d D k) ^ 2 := by ring
      _ ≤ (|CommonSmoothCutoff.cutoffMass| * d.V / (d.Q1 ^ 2 * (D : ℝ) ^ 2)) *
          C * commonLog d ^ 12 * A * (tau D * commonLog d ^ 2) ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 (hW D) 2) (by positivity)
      _ = _ := by
        dsimp only [A]
        rw [Real.rpow_add hQ 2 eta, Real.rpow_add hDR 2 eta]
        norm_num only [Real.rpow_two]
        field_simp [hQ.ne', hDR.ne', (Real.rpow_pos_of_pos hR0 (1 - eta)).ne']
  rw [actual_eq_gcd_slices hd, Finset.sum_comm]
  calc
    _ ≤ ∑ D ∈ smallDivisors d Y,
        |CommonSmoothCutoff.cutoffMass| * C * d.V * commonLog d ^ 16 *
          (tau D ^ 2 / (D : ℝ) * (d.U ^ 2 / (d.Q1 * R ^ (1 - eta))) +
            tau D ^ 2 * (D : ℝ) ^ eta * (d.Q1 ^ eta * d.U)) := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun D hD ↦ hDpoint hD)
    _ = |CommonSmoothCutoff.cutoffMass| * C * d.V * commonLog d ^ 16 *
        ((∑ D ∈ smallDivisors d Y, tau D ^ 2 / (D : ℝ)) *
            (d.U ^ 2 / (d.Q1 * R ^ (1 - eta))) +
          (∑ D ∈ smallDivisors d Y, tau D ^ 2 * (D : ℝ) ^ eta) * (d.Q1 ^ eta * d.U)) := by
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, mul_add, mul_assoc]
    _ ≤ |CommonSmoothCutoff.cutoffMass| * C * d.V * commonLog d ^ 16 *
        (commonLog d ^ 4 * (d.U ^ 2 / (d.Q1 * R ^ (1 - eta))) +
          (Y ^ (1 + eta) * commonLog d ^ 4) * (d.Q1 ^ eta * d.U)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_right (tau_square_harmonic_le hd Y) (by positivity))
        (mul_le_mul_of_nonneg_right (tau_square_power_sum_le hd heta hY) (by positivity))
    _ = |CommonSmoothCutoff.cutoffMass| * C * d.V * commonLog d ^ 20 *
        (d.U ^ 2 / (d.Q1 * R ^ (1 - eta)) + d.Q1 ^ eta * Y ^ (1 + eta) * d.U) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hV.le
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg CommonSmoothCutoff.cutoffMass]) hC.le

/-- The actual outside factors retain the complete second relative term,
including the eta powers of both Q1 and the residual cutoff. -/
theorem actual_outside_mul_smallResidualHighConductorZero_bound
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        MediumAdmissible B sigma kappa c0 d →
        ∀ Y R : ℝ, 1 ≤ Y → 1 ≤ R →
          ((∑ m ∈ d.betaCarrier, ‖d.beta m‖ ^ 2) *
              (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)) *
            ‖d.sharedFirstFactorSmallResidualHighConductorZero Y R‖ ≤
              C * d.scale ^ 2 *
                (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
                (1 + Real.log (32 * d.U * d.Q1 * d.Q2 * d.Q3)) ^ 20 *
                (1 / R ^ (1 - eta) +
                  d.Q1 ^ (1 + eta) * Y ^ (1 + eta) / d.U) := by
  obtain ⟨C, hC, hbound⟩ := actual_smallResidualHighConductorZero_bound heta heta1
  refine ⟨4 * C, by positivity, fun B sigma kappa c0 d hd Y R hY hR ↦ ?_⟩
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hLV : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hH := commonLog_one_le hd
  refine (mul_le_mul (d.sharedFirstFactor_outside_le hd)
    (hbound B sigma kappa c0 d hd Y R hY hR) (norm_nonneg _) (by positivity)).trans_eq ?_
  unfold MediumAtom.scale
  rw [Real.rpow_add hQ 1 eta, Real.rpow_one]
  field_simp [hU.ne', hQ.ne', (Real.rpow_pos_of_pos hR0 (1 - eta)).ne']

end

end ImbalancedChen.Part3
