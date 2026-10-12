import ImbalancedChen.Part3RoughAuxiliarySW
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform logarithmic absorption of the actual rough auxiliary filter

This file treats the auxiliary-`k` removal in section 5 of the frozen
prime-product completion.  It keeps the coefficient, its interval, the
progression residue, and the coprime mean unchanged.  It proves the scalar
decay for the literal local cutoff `x ^ (1 / (log (log x)) ^ 3)` and uses
the finite arithmetic estimate from `Part3RoughAuxiliarySW`.

The threshold below is selected before the atom and before every `k,q,b`.
The last theorem explicitly assumes only the `k = 1` SW estimate for the
same family.  That arithmetic SW input remains open for the actual rough
one/Möbius slots; it is not an admissibility field or a dispersion premise.

Validation status: source proof candidates.  The unchanged pinned Lean
executable cannot start in the current environment; see the Part 3 report.
-/

namespace ImbalancedChen.Part3

open Filter Topology
open scoped BigOperators

noncomputable section

/-- The fourth logarithmic power is exactly what pays the cubic
`log log` in the roughness exponent and one further logarithm. -/
theorem tendsto_logLog_four_div_log :
    Tendsto (fun x : ℝ => (Real.log (Real.log x)) ^ 4 / Real.log x)
      atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  simpa only [Function.comp_def, Real.rpow_ofNat, Real.rpow_one] using
    h.comp Real.tendsto_log_atTop

/-- Every fixed logarithm power is eventually below the literal
subpower rough cutoff.  The real exponent `B` is fixed first. -/
theorem eventually_log_rpow_le_roughCutoff (B : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ B ≤ x ^ (1 / (Real.log (Real.log x)) ^ 3) := by
  have hlim : Tendsto
      (fun x : ℝ => B * ((Real.log (Real.log x)) ^ 4 / Real.log x))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_logLog_four_div_log.const_mul B
  have hsmall := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall, eventually_gt_atTop (Real.exp (Real.exp 1))]
    with x hsmallx hx
  have hxpos : 0 < x := (Real.exp_pos _).trans hx
  have hlog : Real.exp 1 < Real.log x := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hx
  have hlogpos : 0 < Real.log x := (Real.exp_pos 1).trans hlog
  have hloglog : 1 < Real.log (Real.log x) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hlog
  have hloglogpos : 0 < Real.log (Real.log x) := by linarith
  have hfour : B * (Real.log (Real.log x)) ^ 4 ≤ Real.log x := by
    have hs : B * (Real.log (Real.log x)) ^ 4 / Real.log x ≤ 1 := by
      simpa only [mul_div_assoc] using hsmallx.le
    simpa only [one_mul] using (div_le_iff₀ hlogpos).mp hs
  have hexponent : Real.log (Real.log x) * B ≤
      Real.log x * (1 / (Real.log (Real.log x)) ^ 3) := by
    rw [mul_one_div]
    apply (le_div_iff₀ (pow_pos hloglogpos 3)).mpr
    convert hfour using 1 <;> ring
  rw [Real.rpow_def_of_pos hlogpos, Real.rpow_def_of_pos hxpos]
  exact Real.exp_le_exp.mpr hexponent

/-- A fixed constant divided by the rough cutoff has arbitrary real
logarithmic accuracy, with no arithmetic parameter in its threshold. -/
theorem eventually_roughCutoff_inv_logAccuracy
    (A c epsilon : ℝ) (hc : 0 ≤ c) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      c / x ^ (1 / (Real.log (Real.log x)) ^ 3) ≤
        epsilon / (Real.log x) ^ A := by
  filter_upwards [eventually_log_rpow_le_roughCutoff (A + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop (c / epsilon),
    eventually_gt_atTop (1 : ℝ)] with x hpower hlarge hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hlogpowpos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hdenpos : 0 < (Real.log x) ^ (A + 1) :=
    Real.rpow_pos_of_pos hlogpos (A + 1)
  have hcsmall : c ≤ epsilon * Real.log x := by
    have h := (div_le_iff₀ hepsilon).mp hlarge
    simpa only [mul_comm] using h
  calc
    c / x ^ (1 / (Real.log (Real.log x)) ^ 3) ≤
        c / (Real.log x) ^ (A + 1) :=
      div_le_div_of_nonneg_left hc hdenpos hpower
    _ = c / ((Real.log x) ^ A * Real.log x) := by
      rw [Real.rpow_add hlogpos, Real.rpow_one]
    _ ≤ epsilon / (Real.log x) ^ A := by
      apply (div_le_div_iff₀ (mul_pos hlogpowpos hlogpos) hlogpowpos).mpr
      nlinarith [mul_le_mul_of_nonneg_right hcsmall hlogpowpos.le]

/-- The dyadic alpha carrier is a positive integer prefix subset.  Its
upper endpoint, rather than its cardinality alone, licenses the divisor
count used to remove the auxiliary coprimality condition. -/
theorem MediumAtom.alphaCarrier_subset_Ioc (d : MediumAtom) (hU : 0 < d.U) :
    d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U)) := by
  intro n hn
  have hn' := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  exact Finset.mem_Ioc.mpr
    ⟨(Nat.ceil_pos.mpr hU).trans_le hn'.1, hn'.2⟩

/-- Actual auxiliary-filter error on the fixed medium atom.  No SW,
modulus range, or primality equidistribution premise is used here. -/
theorem MediumAtom.auxSWError_sub_one_norm_le
    (d : MediumAtom) (z : ℝ) (hU : 0 < d.U) (hz : 0 < z)
    (hα : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (hrough : ∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n → z < (p : ℝ))
    (k q b : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    ‖d.auxSWError k q b - d.auxSWError 1 q b‖ ≤
      4 * d.U * (k.divisors.card : ℝ) / z := by
  simp only [MediumAtom.auxSWError_eq_auxiliarySWError]
  have h := auxiliarySWError_sub_one_norm_le d.alphaCarrier d.alpha
    (Nat.floor (2 * d.U)) k q b z (d.alphaCarrier_subset_Ioc hU)
    hz (by omega) (by omega) hα hrough
  calc
    _ ≤ 2 * (k.divisors.card : ℝ) * (Nat.floor (2 * d.U) : ℝ) / z := h
    _ ≤ 2 * (k.divisors.card : ℝ) * (2 * d.U) / z :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity))
          (by positivity)) hz.le
    _ = 4 * d.U * (k.divisors.card : ℝ) / z := by ring

/-- One threshold handles all medium atoms, intervals, complex
coefficients, auxiliary integers and progression parameters satisfying
the stated rough support.  In particular there is no `k`-dependent
threshold and no restriction to a fixed additive or Mellin phase. -/
theorem exists_medium_auxSWError_sub_one_logAccuracy
    (A epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom, x0 ≤ d.scale →
      0 < d.U →
      (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) →
      (∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
        Nat.Prime p → p ∣ n →
          d.scale ^ (1 / (Real.log (Real.log d.scale)) ^ 3) < (p : ℝ)) →
      ∀ k q b : ℕ, 1 ≤ k → 1 ≤ q →
        ‖d.auxSWError k q b - d.auxSWError 1 q b‖ ≤
          epsilon * d.U * (k.divisors.card : ℝ) / (Real.log d.scale) ^ A := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    (eventually_roughCutoff_inv_logAccuracy A 4 epsilon (by norm_num) hepsilon)
  refine ⟨max 2 X, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro d hd hU hα hrough k q b hk hq
  have hx : 1 < d.scale := lt_of_lt_of_le
    (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)) hd
  have hz : 0 < d.scale ^ (1 / (Real.log (Real.log d.scale)) ^ 3) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hsmall := hX d.scale ((le_max_right _ _).trans hd)
  calc
    _ ≤ 4 * d.U * (k.divisors.card : ℝ) /
        d.scale ^ (1 / (Real.log (Real.log d.scale)) ^ 3) :=
      d.auxSWError_sub_one_norm_le _ hU hz hα hrough k q b hk hq
    _ = (4 / d.scale ^ (1 / (Real.log (Real.log d.scale)) ^ 3)) *
        (d.U * (k.divisors.card : ℝ)) := by ring
    _ ≤ (epsilon / (Real.log d.scale) ^ A) *
        (d.U * (k.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = epsilon * d.U * (k.divisors.card : ℝ) / (Real.log d.scale) ^ A := by ring

/-- The full auxiliary SW family follows from its genuine `k = 1`
arithmetic SW input.  The latter is written explicitly, with the same
interval and coefficients and with its constants before every atom.
No dispersion or high-modulus error conclusion is hidden in this input. -/
theorem uniformAuxiliarySW_of_rough_one
    {ι : Type*} (F : ι → MediumAtom)
    (hU : ∀ i, 0 < (F i).U)
    (hα : ∀ i, ∀ n ∈ (F i).alphaCarrier, ‖(F i).alpha n‖ ≤ 1)
    (hrough : ∀ i, ∀ n ∈ (F i).alphaCarrier, (F i).alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n →
        (F i).scale ^ (1 / (Real.log (Real.log (F i).scale)) ^ 3) < (p : ℝ))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1 := by
  intro A hA
  obtain ⟨C, hC, X, hX, hbase⟩ := hSW A hA
  obtain ⟨Y, _hY, haux⟩ := exists_medium_auxSWError_sub_one_logAccuracy A 1 (by norm_num)
  refine ⟨C + 1, by linarith, max X Y, hX.trans_le (le_max_left _ _), ?_⟩
  intro i hi k q b hk hq hb
  have hXi : X ≤ (F i).scale := (le_max_left _ _).trans hi
  have hYi : Y ≤ (F i).scale := (le_max_right _ _).trans hi
  have hx : 1 < (F i).scale := hX.trans_le hXi
  have hden : 0 < (Real.log (F i).scale) ^ A :=
    Real.rpow_pos_of_pos (Real.log_pos hx) A
  have hτ : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by
    have hτnat : 1 ≤ k.divisors.card := Finset.card_pos.mpr
      (show k.divisors.Nonempty from ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩)
    exact_mod_cast hτnat
  have h0 := hbase i hXi q b hq hb
  have h1 := haux (F i) hYi (hU i) (hα i) (hrough i) k q b hk hq
  have hscaled : C * (F i).U / (Real.log (F i).scale) ^ A ≤
      C * (F i).U * (k.divisors.card : ℝ) / (Real.log (F i).scale) ^ A := by
    calc
      _ = (C * (F i).U / (Real.log (F i).scale) ^ A) * 1 := by ring
      _ ≤ (C * (F i).U / (Real.log (F i).scale) ^ A) *
          (k.divisors.card : ℝ) := mul_le_mul_of_nonneg_left hτ (by positivity)
      _ = _ := by ring
  simp only [pow_one]
  calc
    ‖(F i).auxSWError k q b‖ =
        ‖(F i).auxSWError 1 q b +
          ((F i).auxSWError k q b - (F i).auxSWError 1 q b)‖ := by
      congr 1
      ring
    _ ≤ ‖(F i).auxSWError 1 q b‖ +
        ‖(F i).auxSWError k q b - (F i).auxSWError 1 q b‖ := norm_add_le _ _
    _ ≤ C * (F i).U * (k.divisors.card : ℝ) / (Real.log (F i).scale) ^ A +
        1 * (F i).U * (k.divisors.card : ℝ) / (Real.log (F i).scale) ^ A :=
      add_le_add (h0.trans hscaled) h1
    _ = (C + 1) * (F i).U * (k.divisors.card : ℝ) /
        (Real.log (F i).scale) ^ A := by ring

/-- A genuine power gap pays a fixed real logarithmic power.  This
scalar threshold has no coefficient, modulus or interval parameter. -/
theorem eventually_const_mul_log_rpow_le_rpow
    (c A xi : ℝ) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, c * (Real.log x) ^ A ≤ x ^ xi := by
  have hlim : Tendsto (fun x : ℝ => c * ((Real.log x) ^ A / x ^ xi))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((isLittleO_log_rpow_rpow_atTop A hxi).tendsto_div_nhds_zero).const_mul c
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop (0 : ℝ)] with x hs hx
  have hs' : c * (Real.log x) ^ A / x ^ xi ≤ 1 := by
    simpa only [mul_div_assoc] using hs.le
  simpa only [one_mul] using
    (div_le_iff₀ (Real.rpow_pos_of_pos hx xi)).mp hs'

open MathlibNt.SieveTheory.Richert1969 in
/-- Large progression moduli are negligible for the literal complex
coefficient discrepancy.  This result needs no roughness or SW premise.
The upper support bound is `H ≤ 2*x`, and the positive lower power bound
pays the integer endpoint cost.  All auxiliary integers, moving residues,
carriers and coefficients are selected after the same threshold. -/
theorem eventually_auxiliarySW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, ∀ H k q b : ℕ, ∀ S : Finset ℕ, ∀ α : ℕ → ℂ,
      S ⊆ Finset.Ioc 0 H → x ^ xi ≤ (H : ℝ) → (H : ℝ) ≤ 2 * x →
      (Real.log x) ^ (A + 2) ≤ (q : ℝ) →
      (∀ n ∈ S, ‖α n‖ ≤ 1) →
      ‖auxiliarySWError S α k q b‖ ≤
        epsilon * (H : ℝ) / (Real.log x) ^ A := by
  let c := richertReciprocalTotientConstant
  have hc : 0 < c := richertReciprocalTotientConstant_pos
  let D := 1 + 2 * c
  filter_upwards [eventually_const_mul_log_rpow_le_rpow 1 (A + 2) xi hxi,
    eventually_const_mul_log_rpow_le_rpow (4 / epsilon) A xi hxi,
    (tendsto_rpow_atTop hxi).eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * D / epsilon),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2 : ℝ)]
    with x hpower hround hthree hlarge hlog hx
  intro H k q b S α hS hHlow hHhigh hq hα
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := by linarith
  have hR : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hR2 : 0 < (Real.log x) ^ (A + 2) :=
    Real.rpow_pos_of_pos hlogpos (A + 2)
  have hH3 : 3 ≤ H := by exact_mod_cast hthree.trans hHlow
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hqpos : 0 < q := by exact_mod_cast hR2.trans_le hq
  have hHlog : (Real.log x) ^ (A + 2) ≤ (H : ℝ) := by
    have ht : (Real.log x) ^ (A + 2) ≤ x ^ xi := by
      simpa only [one_mul] using hpower
    exact ht.trans hHlow
  have hmin : (Real.log x) ^ (A + 2) ≤ (min q H : ℕ) := by
    rw [Nat.cast_min]
    exact le_min hq hHlog
  have hminpos : (0 : ℝ) < (min q H : ℕ) := hR2.trans_le hmin
  have hlogH : Real.log (H : ℝ) ≤ 2 * Real.log x := by
    have hh := Real.log_le_log hHpos hHhigh
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne'] at hh
    have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hAP : (H : ℝ) / q ≤ (H : ℝ) * Real.log x /
      (Real.log x) ^ (A + 2) := by
    calc
      _ ≤ (H : ℝ) / (Real.log x) ^ (A + 2) :=
        div_le_div_of_nonneg_left hHpos.le hR2 hq
      _ ≤ _ := div_le_div_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hHpos.le) hR2.le
  have hmean : (H : ℝ) * c * Real.log (H : ℝ) / (min q H : ℕ) ≤
      (H : ℝ) * c * (2 * Real.log x) / (Real.log x) ^ (A + 2) := by
    calc
      _ ≤ (H : ℝ) * c * (2 * Real.log x) / (min q H : ℕ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogH (mul_nonneg hHpos.le hc.le)) hminpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hR2 hmin
  have hDsmall : D / Real.log x ≤ epsilon / 2 := by
    apply (div_le_iff₀ hlogpos).mpr
    have hm := (div_le_iff₀ hepsilon).mp hlarge
    nlinarith
  have htwo : 2 ≤ (epsilon / 2) * (H : ℝ) / (Real.log x) ^ A := by
    have hr : 4 * (Real.log x) ^ A / epsilon ≤ (H : ℝ) := by
      simpa only [div_mul_eq_mul_div] using hround.trans hHlow
    have hm := (div_le_iff₀ hepsilon).mp hr
    apply (le_div_iff₀ hR).mpr
    nlinarith
  calc
    ‖auxiliarySWError S α k q b‖ ≤
        (H : ℝ) / q + 2 + (H : ℝ) * c * Real.log (H : ℝ) / (min q H : ℕ) :=
      auxiliarySWError_norm_le_large_modulus S α H k q b hS hH3 hqpos hα
    _ ≤ (H : ℝ) * Real.log x / (Real.log x) ^ (A + 2) + 2 +
        (H : ℝ) * c * (2 * Real.log x) / (Real.log x) ^ (A + 2) :=
      add_le_add (add_le_add_right hAP 2) hmean
    _ = (D / Real.log x) * ((H : ℝ) / (Real.log x) ^ A) + 2 := by
      rw [Real.rpow_add hlogpos, Real.rpow_ofNat]
      dsimp [D]
      field_simp [hlogpos.ne', hR.ne'] <;> ring
    _ ≤ (epsilon / 2) * ((H : ℝ) / (Real.log x) ^ A) +
        (epsilon / 2) * (H : ℝ) / (Real.log x) ^ A :=
      add_le_add (mul_le_mul_of_nonneg_right hDsmall (by positivity)) htwo
    _ = epsilon * (H : ℝ) / (Real.log x) ^ A := by ring

/-- Large-`q` SW for the actual medium alpha carrier, including rough
one/Möbius slots as special cases.  The bound is independent of `k`;
roughness is unnecessary in this branch. -/
theorem exists_medium_auxSW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom, x0 ≤ d.scale →
      d.scale ^ xi ≤ d.U → 1 ≤ d.V →
      (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) →
      ∀ k q b : ℕ, (Real.log d.scale) ^ (A + 2) ≤ (q : ℝ) →
        ‖d.auxSWError k q b‖ ≤ epsilon * d.U / (Real.log d.scale) ^ A := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    (eventually_auxiliarySW_large_modulus_logAccuracy A (epsilon / 2) xi
      (by positivity) hxi)
  refine ⟨max 2 X, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro d hd hUlow hV hα k q b hq
  have hx : 1 < d.scale := lt_of_lt_of_le
    (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)) hd
  have hU1 : 1 ≤ d.U := (Real.one_le_rpow hx.le hxi.le).trans hUlow
  have hUpos : 0 < d.U := by linarith
  have hUhigh : d.U ≤ d.scale := by
    dsimp [MediumAtom.scale]
    nlinarith
  have hfloorlow : d.U ≤ (Nat.floor (2 * d.U) : ℝ) := by
    have hf := Nat.lt_floor_add_one (2 * d.U)
    linarith
  have hfloorhigh : (Nat.floor (2 * d.U) : ℝ) ≤ 2 * d.U :=
    Nat.floor_le (by positivity)
  have he := hX d.scale ((le_max_right _ _).trans hd)
    (Nat.floor (2 * d.U)) k q b d.alphaCarrier d.alpha
    (d.alphaCarrier_subset_Ioc hUpos) (hUlow.trans hfloorlow)
    (hfloorhigh.trans (by linarith)) hq hα
  simp only [MediumAtom.auxSWError_eq_auxiliarySWError]
  calc
    _ ≤ (epsilon / 2) * (Nat.floor (2 * d.U) : ℝ) / (Real.log d.scale) ^ A := he
    _ ≤ (epsilon / 2) * (2 * d.U) / (Real.log d.scale) ^ A :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfloorhigh (by positivity))
        (Real.rpow_nonneg (Real.log_pos hx).le A)
    _ = epsilon * d.U / (Real.log d.scale) ^ A := by ring

/-- After the proved large-modulus estimate and auxiliary-filter removal,
the only arithmetic SW input is `k=1` at small progression moduli for the
same rough family.  This is a reduction theorem, not a proof of that
remaining input for arbitrary one-bounded rough coefficients. -/
theorem uniformAuxiliarySW_of_rough_small_moduli
    {ι : Type*} (F : ι → MediumAtom) (xi : ℝ) (hxi : 0 < xi)
    (hU : ∀ i, 1 ≤ (F i).U) (hV : ∀ i, 1 ≤ (F i).V)
    (hUlow : ∀ i, (F i).scale ^ xi ≤ (F i).U)
    (hα : ∀ i, ∀ n ∈ (F i).alphaCarrier, ‖(F i).alpha n‖ ≤ 1)
    (hrough : ∀ i, ∀ n ∈ (F i).alphaCarrier, (F i).alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n →
        (F i).scale ^ (1 / (Real.log (Real.log (F i).scale)) ^ 3) < (p : ℝ))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → (q : ℝ) < (Real.log (F i).scale) ^ (A + 2) →
        Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1 := by
  apply uniformAuxiliarySW_of_rough_one F
    (fun i => lt_of_lt_of_le zero_lt_one (hU i)) hα hrough
  intro A hA
  obtain ⟨C, _hC, X, hX, hsmall⟩ := hSW A hA
  obtain ⟨Y, _hY, hlarge⟩ := exists_medium_auxSW_large_modulus_logAccuracy A 1 xi
    (by norm_num) hxi
  refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _),
    max X Y, hX.trans_le (le_max_left _ _), ?_⟩
  intro i hi q b hq hb
  have hXi : X ≤ (F i).scale := (le_max_left _ _).trans hi
  have hYi : Y ≤ (F i).scale := (le_max_right _ _).trans hi
  have hx : 1 < (F i).scale := hX.trans_le hXi
  have hUpos : 0 < (F i).U := lt_of_lt_of_le zero_lt_one (hU i)
  have hden : 0 ≤ (Real.log (F i).scale) ^ A :=
    Real.rpow_nonneg (Real.log_pos hx).le A
  by_cases hsmallq : (q : ℝ) < (Real.log (F i).scale) ^ (A + 2)
  · exact (hsmall i hXi q b hq hsmallq hb).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 1) hUpos.le) hden)
  · exact (hlarge (F i) hYi (hUlow i) (hV i) (hα i) 1 q b
      (le_of_not_gt hsmallq)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right C 1) hUpos.le) hden)

/-- The existing medium range itself supplies the positive alpha power
gap: `1 ≤ Q1 < U*x^(-sigma)` forces `x^sigma < U`.  No new range or
policy assumption is introduced for the large-`q` SW branch. -/
theorem MediumAdmissible.alphaScaleLower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.scale ^ sigma < d.U := by
  obtain ⟨_, _, hQ1, _, _, hx, _, _, hQ, _⟩ := hd
  have hxpos : 0 < d.scale := (Real.exp_pos _).trans hx
  have hpow : 0 < d.scale ^ sigma := Real.rpow_pos_of_pos hxpos sigma
  have h1 : 1 < d.U * d.scale ^ (-sigma) := hQ1.trans_lt hQ
  rw [Real.rpow_neg hxpos.le] at h1
  have hm := mul_lt_mul_of_pos_right h1 hpow
  simpa only [one_mul, mul_assoc, inv_mul_cancel₀ hpow.ne', mul_one] using hm

/-- Direct application to the unchanged restricted-medium coefficient
and range class.  The sole remaining SW input is printed in full: the
actual `k=1` discrepancy for small `q`, with one family-wide threshold.
All other conditions here are the original structural admissibility.
This theorem does not conclude the signed medium distribution estimate. -/
theorem uniformAuxiliarySW_of_mediumAdmissible_small_moduli
    {ι : Type*} (F : ι → MediumAtom) (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → (q : ℝ) < (Real.log (F i).scale) ^ (A + 2) →
        Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1 := by
  apply uniformAuxiliarySW_of_rough_small_moduli F sigma hsigma
  · exact fun i => (hadmissible i).1
  · exact fun i => (hadmissible i).2.1
  · exact fun i => (MediumAdmissible.alphaScaleLower (hadmissible i)).le
  · intro i
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hα, _⟩ := hadmissible i
    exact hα
  · intro i
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrough, _⟩ := hadmissible i
    exact hrough
  · exact hSW

end

end ImbalancedChen.Part3
