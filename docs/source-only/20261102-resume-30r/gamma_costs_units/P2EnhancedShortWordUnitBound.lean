import ImbalancedChen.P2EnhancedNonunitMarkedMass

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The quotient-one atoms of short words are actual labelled cardinalities.
The independent five/six-prime unit surfaces are outside this argument.
-/
namespace ImbalancedChen.P2EnhancedShortWordUnitBound
noncomputable section
open Real Filter Finset Wu2008DoubleSieve
open P2EnhancedSwitchedUnsiftedSource P2EnhancedNonunitLabelGeometry
open P2SeedOmegaLiteralFibre (b)
open P2EnhancedSwitchedTrueNormalization
open P2EnhancedNonunitWordMass (rawScale)
open scoped Classical BigOperators Topology

private theorem list_product_cap (l : List ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (∀ p ∈ l, (p : ℝ) ≤ H) → (l.prod : ℝ) ≤ H^l.length := by
  induction l with
  | nil => intro _; simp
  | cons p ps ih =>
    intro hp
    have htail := ih (fun q hq => hp q (by simp [hq]))
    simp only [List.prod_cons, Nat.cast_mul, List.length_cons, pow_succ]
    calc
      _ ≤ H * H^ps.length := mul_le_mul (hp p (by simp)) htail
        (Nat.cast_nonneg _) hH
      _ = _ := mul_comm _ _

theorem label_product_cap {N d : ℕ} {Q : ℝ} {cs l : List ℕ}
    (hR : 1 < Q/d) (hl : l ∈ labels N Q d cs) :
    (l.prod : ℝ) ≤ (Q/d)^(b*(cs.length : ℝ)) := by
  have hh := list_product_cap l ((Q/d)^b) (rpow_nonneg (zero_le_one.trans hR.le) _) (by
    intro p hp
    exact (mem_primeWindow.mp ((label_data hl).2.2.1 p hp)).2.2.2.le)
  rw [(label_data hl).1, ← rpow_natCast, ← rpow_mul (zero_lt_one.trans hR).le] at hh
  exact hh

/-- The native reciprocal mass is reused on the injective COMPLETE-list image. -/
theorem reciprocal_labels_eventually :
    ∀ᶠ R : ℝ in atTop, ∀ (N d : ℕ) (cs : List ℕ), ∀ Q : ℝ, Q/d = R →
      (∑ l ∈ labels N Q d cs, 1/(l.prod : ℝ)) ≤ 5^cs.length := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    SecondFunctionalUnitFiniteKernel.mass_eventually] with R hR hm
  intro N d cs Q he
  have hQR : 1 < Q/d := by simpa only [he] using hR
  let E := labelEmbedding hQR cs
  have hm' : ∀ n : ℕ, ∀ S : Finset (Fin n → primeSlabPrimes (Q/d)),
      (∑ f ∈ S, primeSlabWeight (Q/d) f) ≤ 5^n := by
    simpa only [he] using hm
  have hh' := hm' cs.length (univ.image E)
  rw [sum_image (fun a _ b _ h => E.injective h)] at hh'
  simpa only [E, label_weight, sum_coe_sort] using hh'

/-- Actual unit cardinality. No prime receiver and no product-map
injectivity are used; the full original label is kept throughout. -/
theorem short_unit_eventually :
    ∀ᶠ R : ℝ in atTop, ∀ (N d : ℕ) (cs : List ℕ), ∀ Q : ℝ,
      0 < d → Q/d = R → cs.length ≤ 4 →
      unitWordMass N Q d cs ≤ 625*R^(20/11 : ℝ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), reciprocal_labels_eventually]
    with R hR hm
  intro N d cs Q hd he hn
  have hQR : 1 < Q/d := by simpa only [he] using hR
  have hcap (l : List ℕ) (hl : l ∈ labels N Q d cs) :
      (l.prod : ℝ) ≤ R^(20/11 : ℝ) := by
    have h := label_product_cap hQR hl
    rw [he] at h
    exact h.trans (rpow_le_rpow_of_exponent_le hR.le (by
      have hn' : (cs.length : ℝ) ≤ 4 := by exact_mod_cast hn
      norm_num [b]; linarith))
  have hcount : ((labels N Q d cs).card : ℝ) ≤
      R^(20/11 : ℝ)*(∑ l ∈ labels N Q d cs, 1/(l.prod : ℝ)) := by
    rw [mul_sum]
    calc
      _ = ∑ l ∈ labels N Q d cs, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum fun l hl => by
        have hp : (0 : ℝ) < l.prod := Nat.cast_pos.mpr (label_prod_pos hl)
        rw [mul_one_div, le_div_iff₀ hp, one_mul]
        exact hcap l hl
  rw [unitWordMass_eq_product_count hd]
  calc
    _ ≤ ((labels N Q d cs).card : ℝ) := by
      exact_mod_cast card_filter_le (labels N Q d cs) (fun l => d*l.prod ≤ N)
    _ ≤ R^(20/11 : ℝ)*(5^cs.length) := hcount.trans
      (mul_le_mul_of_nonneg_left (hm N d cs Q he) (rpow_nonneg (zero_le_one.trans hR.le) _))
    _ ≤ R^(20/11 : ℝ)*(5^4) := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) hn)
      (rpow_nonneg (zero_le_one.trans hR.le) _)
    _ = _ := by norm_num; ring

/-- Literal original occurrence arities; tactics below remain UNEVALUATED. -/
theorem original_short_arity (j : Fin 11) {cs : List ℕ}
    (h : cs ∈ secondFunctionalMotherGammaWords (9+j.val)) : cs.length ≤ 4 := by
  fin_cases j <;> norm_num [secondFunctionalMotherGammaWords] at h <;>
    aesop

/-- Elementary quantitative absorption of the genuine short-word gap. -/
theorem power_gap_absorption {R X U epsilon : ℝ} (hR : 1 < R)
    (he : 0 < epsilon) (hlarge : 6875/epsilon ≤ R^(1/11 : ℝ))
    (hU : U ≤ 625*R^(20/11 : ℝ)) (hX : R^(2 : ℝ) ≤ X) :
    U ≤ epsilon*(X/log R) := by
  have hR0 := zero_lt_one.trans hR
  have hlog := log_pos hR
  have hsmall := log_le_sub_one_of_pos (rpow_pos_of_pos hR0 (1/11 : ℝ))
  rw [log_rpow hR0] at hsmall
  have hlogcap : log R ≤ 11*R^(1/11 : ℝ) := by linarith
  have hepay : 6875 ≤ epsilon*R^(1/11 : ℝ) := by
    have h := (div_le_iff₀ he).mp hlarge
    nlinarith
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlog).mpr
  calc
    U*log R ≤ (625*R^(20/11 : ℝ))*(11*R^(1/11 : ℝ)) :=
      mul_le_mul hU hlogcap hlog.le (by positivity)
    _ = 6875*R^(21/11 : ℝ) := by
      rw [show (21/11 : ℝ) = 20/11+1/11 by norm_num, rpow_add hR0]
      ring
    _ ≤ (epsilon*R^(1/11 : ℝ))*R^(21/11 : ℝ) :=
      mul_le_mul_of_nonneg_right hepay (rpow_nonneg hR0.le _)
    _ = epsilon*R^(2 : ℝ) := by
      rw [show (2 : ℝ) = 1/11+21/11 by norm_num, rpow_add hR0]
      ring
    _ ≤ epsilon*X := mul_le_mul_of_nonneg_left hX he.le

/-- One N threshold precedes the true Q, d, every short word, and alpha.
The source unit atom is paid; no zero continuous surface is substituted. -/
theorem actual_short_unit_upper {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      0 < d → (N : ℝ)^eta ≤ Q/d → 2 ≤ trueAlpha N Q d →
      ∀ cs : List ℕ, cs.length ≤ 4 →
        unitWordMass N Q d cs ≤ epsilon*P2EnhancedNonunitWordMass.rawScale N Q d := by
  have hlarge : ∀ᶠ R : ℝ in atTop, 6875/epsilon ≤ R^(1/11 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/11)).eventually_ge_atTop _
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp
    (short_unit_eventually.and hlarge)
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop R0)
  refine ⟨max 4 T0,le_max_left _ _,?_⟩
  intro N hN Q d hd hscale ha cs hn
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by omega
  have hR : 1 < Q/d := (one_lt_rpow
    (by exact_mod_cast (show 1 < N by omega)) heta).trans_le hscale
  have hRR := hR0 (Q/d) ((hT0 N ((le_max_right _ _).trans hN)).trans hscale)
  have hX : (Q/d)^(2 : ℝ) ≤ (N : ℝ)/d := by
    rw [← P2EnhancedUnitSourceMass.scale_identity hN0 hd hR]
    exact rpow_le_rpow_of_exponent_le hR.le ha
  have hh := power_gap_absorption hR he hRR.2
    (hRR.1 N d cs Q hd rfl hn) hX
  simpa only [P2EnhancedNonunitWordMass.rawScale, div_div] using hh

end
end ImbalancedChen.P2EnhancedShortWordUnitBound
