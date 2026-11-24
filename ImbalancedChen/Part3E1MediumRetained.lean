import ImbalancedChen.Part3E1FixedDEstimate
import ImbalancedChen.Part3E1MediumCaps

/-! The retained E1 power estimate at the original medium scales. -/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Finset
open scoped BigOperators SchwartzMap FourierTransform

private theorem fixedDModuli_subset_factorCarrier_mul (k : ℕ) (Q₀ : ℝ) (hQ₀ : 1 ≤ Q₀)
    (S : Finset ℕ) (hS : S ⊆ factorCarrier Q₀) :
    fixedDModuli k S ⊆ factorCarrier ((k : ℝ) * Q₀) := by
  intro q hq
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hq
  obtain ⟨hlo, hhi⟩ := e1FactorCarrier_bounds (zero_le_one.trans hQ₀) (hS hm)
  apply mem_Icc.mpr
  constructor
  · apply Nat.ceil_le.mpr
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hlo (by positivity)
  · apply (Nat.le_floor_iff (by positivity : 0 ≤ 2 * ((k : ℝ) * Q₀))).mpr
    rw [Nat.cast_mul, mul_left_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left hhi (by positivity)

/-- One retained S2 cell at fixed split divisor, with its physical Poisson
factor `V` divided out. The cutoff uses the same original `Q₁` scale
throughout the q cells. -/
theorem exists_retainedS2FixedD_medium_cell {σ c0 Ccut B₀ : ℝ}
    (hσ : 0 < σ) (hc0 : 0 < c0) (hCcut : 0 ≤ Ccut) (hB₀ : 0 < B₀) (ψ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (κ : ℝ) (d : MediumAtom),
      MediumAdmissible B σ κ c0 d → 2 ≤ d.scale →
      (4 * Ccut) * Real.log d.scale ^ 5 ≤ d.scale →
      ∀ (k : ℕ) (q₀ R H : ℝ) (Qs Rs : Finset ℕ)
        (qWeight : ℕ → ℝ) (lambdaTrim : ℕ → ℂ),
        0 < k → (k : ℝ) ≤ d.scale ^ σ → 1 ≤ q₀ → d.Q1 / 4 ≤ q₀ → q₀ ≤ 4 * d.Q1 →
        1 ≤ R → (k : ℝ) * R ≤ 4 * d.Q2 * d.Q3 → 0 ≤ H →
        H ≤ (Ccut * Real.log d.scale ^ 5) * (((k : ℝ) * d.Q1) * R / d.V) →
        Qs ⊆ factorCarrier q₀ → Rs ⊆ factorCarrier R →
        (∀ q ∈ Qs, qWeight q ∈ Set.Icc 0 1) →
        (∀ r ∈ Rs, ‖lambdaTrim r‖ ≤ B₀ * d.scale ^ (σ / 10)) →
        (∀ r ∈ Rs, lambdaTrim r ≠ 0 → (k * r).Coprime d.residue.natAbs) →
        ‖retainedS2FixedD Qs Rs d.alphaCarrier ⌊H⌋₊ k d.residue d.V
            (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) qWeight lambdaTrim d.alpha‖ / d.V ≤
          C * (d.U ^ 2 / ((k : ℝ) * d.Q1)) * d.scale ^ (-σ) := by
  obtain ⟨A, hA, h18⟩ := exists_retainedS2FixedD_norm_sq_le
    (κ := 12) (ε := σ / 10) (Ccut := 4 * Ccut) (by norm_num) (by positivity) (by positivity) ψ
  let A' := 512 * A * B₀ ^ 4
  have hA' : 0 < A' := by dsimp only [A']; positivity
  refine ⟨Real.sqrt (A' * (5 + 64 * c0 ^ (-35 / 512 : ℝ))), by positivity, ?_⟩
  intro B κ d hd hX hlog k q₀ R H Qs Rs qWeight lambdaTrim hk hksub hq₀ hlo hhi
    hR hprod hH hcut hQs hRs hqWeight hlambda hprimitive
  have hdData := hd
  obtain ⟨hU, hV, hQ₁, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hdData
  have hU0 := zero_lt_one.trans_le hU
  have hV0 := zero_lt_one.trans_le hV
  have hQ₁0 := zero_lt_one.trans_le hQ₁
  have hX0 := (by norm_num : (0 : ℝ) < 2).trans_le hX
  let X := d.scale
  have hX1 : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ 2).trans hX
  have hlogX := Real.log_nonneg hX1
  let Q := (k : ℝ) * d.Q1
  let Q' := (k : ℝ) * q₀
  have hQ0 : 0 < Q := mul_pos (Nat.cast_pos.mpr hk) hQ₁0
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hQ'1 : 1 ≤ Q' := one_le_mul_of_one_le_of_one_le hk1 hq₀
  have hQlo : Q / 4 ≤ Q' := by
    change ((k : ℝ) * d.Q1) / 4 ≤ (k : ℝ) * q₀
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlo (by positivity)
  have hQhi : Q' ≤ 4 * Q := by
    change (k : ℝ) * q₀ ≤ 4 * ((k : ℝ) * d.Q1)
    rw [mul_left_comm (4 : ℝ)]
    exact mul_le_mul_of_nonneg_left hhi (by positivity)
  have hcut' : H ≤ (4 * Ccut * Real.log X ^ 5) * (Q' * R / d.V) := by
    have hcomp : Q ≤ 4 * Q' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hQlo |>.trans_eq (mul_comm _ _)
    calc
      _ ≤ (Ccut * Real.log X ^ 5) * (Q * R / d.V) := hcut
      _ ≤ (Ccut * Real.log X ^ 5) * ((4 * Q') * R / d.V) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcomp (zero_le_one.trans hR)) hV0.le) (by positivity)
      _ = _ := by ring
  obtain ⟨hcapQR, hcapHR⟩ := medium_e1_realDyadic_polynomialCaps hσ.le hX hd k hk
    q₀ R H (4 * Ccut) hq₀ hhi hR hprod hlog hcut'
  let E := retainedS2FixedD Qs Rs d.alphaCarrier ⌊H⌋₊ k d.residue d.V
    (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) qWeight lambdaTrim d.alpha
  let Z := E / (d.V : ℂ)
  let Y := (d.U ^ 4 / Q' ^ 2) * e1Equation18Bracket X d.U Q' R
  let Y₀ := (d.U ^ 4 / Q ^ 2) * e1Equation18Bracket X d.U Q R
  have hNs : d.alphaCarrier ⊆ factorCarrier d.U := filter_subset _ _
  have hXeq : X = d.V * d.U := mul_comm _ _
  have hs := h18 X d.V Q' R d.U H hX hV0 hQ'1 hR hU hH hXeq hcapQR hcapHR hcut'
    k Qs Rs d.alphaCarrier (B₀ * X ^ (σ / 10)) d.residue qWeight lambdaTrim d.alpha hk (by positivity)
    (fixedDModuli_subset_factorCarrier_mul k q₀ hq₀ Qs hQs) hRs hNs hqWeight hlambda hprimitive hAlpha
  have hs' : ‖E‖ ^ 2 ≤ d.V ^ 2 * (B₀ * X ^ (σ / 10)) ^ 4 * (A * X ^ (σ / 10) * Y) := by
    simpa only [E, Y, e1Equation18Bracket, mul_assoc] using hs
  have hXexp : (X ^ (σ / 10)) ^ 4 * X ^ (σ / 10) = X ^ (σ / 2) := by
    rw [← Real.rpow_mul_natCast hX0.le, ← Real.rpow_add hX0]
    congr 1
    push_cast
    ring
  have hY := e1ShiftedQCell_monomials_le hX0 hU0.le hQ0 (zero_le_one.trans hR) hQlo hQhi
  have hZ : ‖Z‖ ^ 2 ≤ A' * X ^ (σ / 2) * (d.U ^ 4 / Q ^ 2) *
      e1Equation18Bracket X d.U Q R := by
    calc
      _ = ‖E‖ ^ 2 / d.V ^ 2 := by
        simp only [Z, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV0, div_pow]
      _ ≤ (d.V ^ 2 * (B₀ * X ^ (σ / 10)) ^ 4 * (A * X ^ (σ / 10) * Y)) / d.V ^ 2 :=
        div_le_div_of_nonneg_right hs' (by positivity)
      _ = (A * B₀ ^ 4) * ((X ^ (σ / 10)) ^ 4 * X ^ (σ / 10)) * Y := by
        field_simp [hV0.ne']
      _ ≤ (A * B₀ ^ 4) * X ^ (σ / 2) * (512 * Y₀) := by
        rw [hXexp]
        exact mul_le_mul_of_nonneg_left hY (by positivity)
      _ = _ := by dsimp only [A', Y₀]; ring
  have hmain := medium_e1_fixedBlock_le hσ hc0 hd k hk hksub R hR hprod
    (σ / 2) A' (by linarith) hA'.le Z hZ
  simpa only [Z, E, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV0] using hmain

/-- The fixed-divisor source splits exactly along disjoint slices of its
original outer carrier. Its weights and lower-level fibres are untouched. -/
theorem retainedS2FixedD_eq_sum_qCells {ι : Type*} (I : Finset ι) (Qs : ι → Finset ℕ)
    (hdis : Set.PairwiseDisjoint (↑I : Set ι) Qs) (R N : Finset ℕ)
    (H k : ℕ) (a : ℤ) (V : ℝ) (ψhat : ℝ → ℂ) (qWeight : ℕ → ℝ)
    (lambdaTrim alpha : ℕ → ℂ) :
    retainedS2FixedD (I.biUnion Qs) R N H k a V ψhat qWeight lambdaTrim alpha =
      ∑ i ∈ I, retainedS2FixedD (Qs i) R N H k a V ψhat qWeight lambdaTrim alpha := by
  simp only [retainedS2FixedD, primitive_eq_filter, sum_filter]
  exact sum_biUnion hdis

/-- The numerical estimate (20) for the retained original S2 source.
The q slices explicitly partition its outer carrier. The normalization
removes the common Poisson factor `V`, before summing the actual split divisors. -/
theorem exists_retainedS2_medium_dyadicBlock {σ c0 Ccut B₀ : ℝ}
    (hσ : 0 < σ) (hc0 : 0 < c0) (hCcut : 0 ≤ Ccut) (hB₀ : 0 < B₀) (ψ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (κ : ℝ) (d : MediumAtom),
      MediumAdmissible B σ κ c0 d → 2 ≤ d.scale →
      (4 * Ccut) * Real.log d.scale ^ 5 ≤ d.scale →
      ∀ (D : ℝ), 1 ≤ D → D ≤ d.scale ^ (σ / 2) → 2 ≤ d.scale ^ (σ / 2) →
      ∀ {ι : Type} (I : Finset ι) (J : ℕ), I.card ≤ J →
      ∀ (Q : Finset ℕ) (Qs : ι → Finset ℕ) (q₀ : ι → ℝ),
        Q = I.biUnion Qs → Set.PairwiseDisjoint (↑I : Set ι) Qs →
        (∀ i ∈ I, 1 ≤ q₀ i ∧ d.Q1 / 4 ≤ q₀ i ∧ q₀ i ≤ 4 * d.Q1 ∧ Qs i ⊆ factorCarrier (q₀ i)) →
      ∀ (R H : ℕ → ℝ) (Rs : ℕ → Finset ℕ) (qWeight : ℕ → ℝ) (lambdaTrim : ℕ → ℕ → ℂ),
        (∀ k ∈ factorCarrier D, (Rs k).Nonempty →
          1 ≤ R k ∧ (k : ℝ) * R k ≤ 4 * d.Q2 * d.Q3 ∧ Rs k ⊆ factorCarrier (R k)) →
        (∀ k ∈ factorCarrier D, 0 ≤ H k ∧
          H k ≤ (Ccut * Real.log d.scale ^ 5) * ((D * d.Q1) * R k / d.V)) →
        (∀ q ∈ Q, qWeight q ∈ Set.Icc 0 1) →
        (∀ k ∈ factorCarrier D, ∀ r ∈ Rs k, ‖lambdaTrim k r‖ ≤ B₀ * d.scale ^ (σ / 10)) →
        (∀ k ∈ factorCarrier D, ∀ r ∈ Rs k, lambdaTrim k r ≠ 0 → (k * r).Coprime d.residue.natAbs) →
        ‖∑ k ∈ factorCarrier D,
          retainedS2FixedD Q (Rs k) d.alphaCarrier ⌊H k⌋₊ k d.residue d.V
            (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) qWeight (lambdaTrim k) d.alpha‖ / d.V ≤
          (C * (J : ℝ)) * (d.U ^ 2 / (D * d.Q1)) * d.scale ^ (-σ / 2) := by
  obtain ⟨C, hC, hcell⟩ := exists_retainedS2FixedD_medium_cell hσ hc0 hCcut hB₀ ψ
  refine ⟨2 * C, by positivity, ?_⟩
  intro B κ d hd hX hlog D hD hDsub hXlarge ι I J hJ Q Qs q₀ hcover hdis hCells
    R H Rs qWeight lambdaTrim hR hH hqWeight hlambda hprimitive
  have hX0 := (by norm_num : (0 : ℝ) < 2).trans_le hX
  have hX1 : 1 ≤ d.scale := (by norm_num : (1 : ℝ) ≤ 2).trans hX
  have hlogX := Real.log_nonneg hX1
  have hV0 := zero_lt_one.trans_le hd.2.1
  have hQ₁0 := zero_lt_one.trans_le hd.2.2.1
  let ψhat : ℝ → ℂ := ⇑(𝓕 ψ : 𝓢(ℝ, ℂ))
  let E (S : Finset ℕ) (k : ℕ) : ℂ := retainedS2FixedD S (Rs k) d.alphaCarrier
    ⌊H k⌋₊ k d.residue d.V ψhat qWeight (lambdaTrim k) d.alpha
  let Z (k : ℕ) : ℂ := E Q k / (d.V : ℂ)
  have hcell_subset_Q (i : ι) (hi : i ∈ I) : Qs i ⊆ Q := by
    intro q hq
    rw [hcover]
    exact mem_biUnion.mpr ⟨i, hi, hq⟩
  have hpoint (k : ℕ) (hk : k ∈ factorCarrier D) :
      ‖Z k‖ ≤ (C * (J : ℝ)) * (d.U ^ 2 / ((k : ℝ) * d.Q1)) * d.scale ^ (-σ) := by
    by_cases hnonempty : (Rs k).Nonempty
    · obtain ⟨hk0, _, hksub⟩ := e1DyadicSplitDivisor_bounds hX0 hD hDsub hXlarge hk
      obtain ⟨hRk, hprod, hRsub⟩ := hR k hk hnonempty
      obtain ⟨hHk, hcut⟩ := hH k hk
      have hDk := (e1FactorCarrier_bounds (zero_le_one.trans hD) hk).1
      have hcut' : H k ≤ (Ccut * Real.log d.scale ^ 5) * (((k : ℝ) * d.Q1) * R k / d.V) := by
        refine hcut.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hDk hQ₁0.le) (zero_le_one.trans hRk)) hV0.le
      have hE : E Q k = ∑ i ∈ I, E (Qs i) k := by
        dsimp only [E]
        rw [hcover, retainedS2FixedD_eq_sum_qCells _ _ hdis]
      let L := C * (d.U ^ 2 / ((k : ℝ) * d.Q1)) * d.scale ^ (-σ)
      have hL : 0 ≤ L := by dsimp only [L]; positivity
      calc
        _ = ‖∑ i ∈ I, E (Qs i) k‖ / d.V := by
          simp only [Z, hE, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV0]
        _ ≤ (∑ i ∈ I, ‖E (Qs i) k‖) / d.V :=
          div_le_div_of_nonneg_right (norm_sum_le _ _) hV0.le
        _ = ∑ i ∈ I, ‖E (Qs i) k‖ / d.V := sum_div _ _ _
        _ ≤ ∑ _i ∈ I, L := by
          apply sum_le_sum
          intro i hi
          obtain ⟨hqi, hlo, hhi, hQi⟩ := hCells i hi
          exact hcell B κ d hd hX hlog k (q₀ i) (R k) (H k) (Qs i) (Rs k) qWeight
            (lambdaTrim k) hk0 hksub hqi hlo hhi hRk hprod hHk hcut' hQi hRsub
            (fun q hq => hqWeight q (hcell_subset_Q i hi hq)) (hlambda k hk) (hprimitive k hk)
        _ = (I.card : ℝ) * L := by simp
        _ ≤ (J : ℝ) * L := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hJ) hL
        _ = _ := by dsimp only [L]; ring
    · have hempty : Rs k = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
      have hright : 0 ≤ (C * (J : ℝ)) * (d.U ^ 2 / ((k : ℝ) * d.Q1)) * d.scale ^ (-σ) := by positivity
      simpa [Z, E, retainedS2FixedD, hempty] using hright
  have hblock := e1DyadicBlock_sum_le hX0 hQ₁0 hD
    (mul_nonneg hC.le (Nat.cast_nonneg J)) hDsub Z hpoint
  have hZsum : (∑ k ∈ factorCarrier D, Z k) = (∑ k ∈ factorCarrier D, E Q k) / (d.V : ℂ) :=
    (sum_div _ _ _).symm
  rw [hZsum, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV0] at hblock
  simpa only [E, ψhat, mul_assoc] using hblock

end

end ImbalancedChen.Part3.E1Finite
