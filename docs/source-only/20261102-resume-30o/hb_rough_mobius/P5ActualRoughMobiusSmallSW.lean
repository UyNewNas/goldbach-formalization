import ImbalancedChen.P5ActualRoughMobiusInner

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The sole analytic premise below is classical UNROUGH Mobius SW on a
primitive progression, with the actual coprime mean and arbitrary real
interval endpoints.  It is stated once, before varying E, ell, w, q,
residue or endpoints.  A fixed multiplicative constant in the logarithmic
modulus range is included; this is an equivalent conventional form of
classical unrough SW, not a rough or supported-convolution hypothesis.
-/
namespace ImbalancedChen.P5Z.ActualRoughMobiusSmallSW
noncomputable section
open Classical Finset
open scoped BigOperators
open ActualRoughMobiusConvolution ActualRoughMobiusRankin
open ActualRoughMobiusInner OriginalBetaPrimeSource

/-- Named external classical input.  No roughness, E, Brun weights,
supported w, multiplier, or completed convolution appears in it. -/
def ClassicalUnroughMobiusSW : Prop :=
  ∀ A B K : ℝ, 0 ≤ A → 0 ≤ B → 1 ≤ K →
    ∃ C X : ℝ, 0 < C ∧ 2 ≤ X ∧
      ∀ W a b : ℝ, X ≤ W → W ≤ a → a ≤ b → b ≤ 2*W →
        ∀ q r : ℕ, 0 < q → (q : ℝ) ≤ K*(Real.log W)^B → r.Coprime q →
          ‖unroughError a b q r‖ ≤ C*W/(Real.log W)^A

theorem scale_div_quarter {x : ℝ} (hx : 0 < x) :
    x/x^(1/4 : ℝ) = x^(3/4 : ℝ) := by
  have h := Real.rpow_sub hx (1 : ℝ) (1/4 : ℝ)
  norm_num at h
  exact h.symm

theorem ell_inner_scale {U : ℝ} (hU : 0 < U) {ell : ℕ}
    (hell : 0 < ell) (hellU : (ell : ℝ) ≤ U^(1/4 : ℝ)) :
    U^(3/4 : ℝ) ≤ U/(ell : ℝ) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  rw [← scale_div_quarter hU]
  exact div_le_div_of_nonneg_left hU.le hellR hellU

/-- Both substitutions are paid at their true scale: ell costs at most
U^(1/4), and w costs at most V^(1/4), leaving U^(9/16). -/
theorem small_inner_scale {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hVU : U^(3/4 : ℝ) ≤ V) {w : ℕ} (hw : 0 < w)
    (hwV : (w : ℝ) ≤ V^(1/4 : ℝ)) :
    U^(9/16 : ℝ) ≤ V/(w : ℝ) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  calc
    U^(9/16 : ℝ) = (U^(3/4 : ℝ))^(3/4 : ℝ) := by
      rw [← Real.rpow_mul hU.le]; norm_num
    _ ≤ V^(3/4 : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hU.le _) hVU (by norm_num)
    _ = V/V^(1/4 : ℝ) := (scale_div_quarter hV).symm
    _ ≤ V/(w : ℝ) := div_le_div_of_nonneg_left hV.le hwR hwV

theorem log_comparison {U W : ℝ} (hU : 1 < U)
    (hW : U^(9/16 : ℝ) ≤ W) :
    0 < Real.log W ∧ Real.log U ≤ (16/9 : ℝ)*Real.log W := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hWp : 0 < U^(9/16 : ℝ) := Real.rpow_pos_of_pos hU0 _
  have hl := Real.log_le_log hWp hW
  rw [Real.log_rpow hU0] at hl
  have hlogU := Real.log_pos hU
  constructor <;> linarith

/-- One scale threshold and one constant precede every supported integer
and every changing modulus.  The explicit factor (16/9)^A is paid once. -/
theorem uniform_smallError (hSW : ClassicalUnroughMobiusSW)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C U0 : ℝ, 0 < C ∧ 2 ≤ U0 ∧
      ∀ U V a b : ℝ, U0 ≤ U → 0 < V → U^(3/4 : ℝ) ≤ V →
        V ≤ a → a ≤ b → b ≤ 2*V →
        ∀ E q r : ℕ, E ≠ 0 → E.Coprime q → 0 < q →
          (q : ℝ) ≤ (Real.log U)^B → r.Coprime q →
          ‖smallError E a b V q r‖ ≤ C*V*(E.divisors.card : ℝ)^2/(Real.log U)^A := by
  have hK : (1 : ℝ) ≤ (16/9 : ℝ)^B := Real.one_le_rpow (by norm_num) hB
  obtain ⟨C,X,hC,hX,hclassical⟩ := hSW A B ((16/9 : ℝ)^B) hA hB hK
  refine ⟨C*(16/9 : ℝ)^A,max 2 (X^(16/9 : ℝ)),
    mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _),le_max_left _ _,?_⟩
  intro U V a b hU0 hV hVU ha hab hb E q r hE hEq hq hqlog hr
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU0
  have hU1 : 1 < U := lt_of_lt_of_le (by norm_num) hU2
  have hU : 0 < U := zero_lt_one.trans hU1
  have hlogU : 0 < Real.log U := Real.log_pos hU1
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hXU : X ≤ U^(9/16 : ℝ) := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hX0.le (16/9 : ℝ))
      ((le_max_right _ _).trans hU0) (by norm_num : (0:ℝ)≤9/16)
    rw [← Real.rpow_mul hX0.le] at hp
    norm_num at hp
    exact hp
  let F : ℝ := C*(16/9 : ℝ)^A*V/(Real.log U)^A
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpoint (w : ℕ) (hw : w ∈ smallSupported E b V) :
      ‖unroughError (a/(w : ℝ)) (b/(w : ℝ)) q (pulledResidue w q r)‖ ≤
        F*(1/(w : ℝ)) := by
    obtain ⟨hwS,hwV⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwI,hwE⟩ := Finset.mem_filter.mp hwS
    have hw1 : 0 < w := (Finset.mem_Icc.mp hwI).1
    have hwR : (0 : ℝ) < w := by exact_mod_cast hw1
    have hwq : w.Coprime q := primeSupported_coprime hEq hwE
    have hscale := small_inner_scale hU hV hVU hw1 hwV
    have hlog := log_comparison hU1 hscale
    have hmod : (q : ℝ) ≤ (16/9 : ℝ)^B*(Real.log (V/(w : ℝ)))^B := by
      refine hqlog.trans ?_
      have hh := Real.rpow_le_rpow hlogU.le hlog.2 hB
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤16/9) hlog.1.le] at hh
      exact hh
    have happ := hclassical (V/(w : ℝ)) (a/(w : ℝ)) (b/(w : ℝ))
      (hXU.trans hscale) (div_le_div_of_nonneg_right ha hwR.le)
      (div_le_div_of_nonneg_right hab hwR.le)
      (by simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb hwR.le)
      q (pulledResidue w q r) hq hmod (pulledResidue_coprime hwq hr)
    have hden : (Real.log U)^A ≤
        (16/9 : ℝ)^A*(Real.log (V/(w : ℝ)))^A := by
      have hh := Real.rpow_le_rpow hlogU.le hlog.2 hA
      rwa [Real.mul_rpow (by norm_num : (0:ℝ)≤16/9) hlog.1.le] at hh
    have hinv : 1/(Real.log (V/(w : ℝ)))^A ≤ (16/9 : ℝ)^A/(Real.log U)^A := by
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hlog.1 A)
        (Real.rpow_pos_of_pos hlogU A)).mpr
      simpa only [one_mul] using hden
    calc
      _ ≤ C*(V/(w : ℝ))/(Real.log (V/(w : ℝ)))^A := happ
      _ ≤ (C*(V/(w : ℝ)))*((16/9 : ℝ)^A/(Real.log U)^A) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = F*(1/(w : ℝ)) := by dsimp [F]; ring
  unfold smallError
  calc
    _ ≤ ∑ w ∈ smallSupported E b V,
        ‖unroughError (a/(w : ℝ)) (b/(w : ℝ)) q (pulledResidue w q r)‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ smallSupported E b V, F*(1/(w : ℝ)) := Finset.sum_le_sum hpoint
    _ = F*(∑ w ∈ smallSupported E b V,1/(w : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ F*(∑ w ∈ supportedCarrier E (Nat.floor b),1/(w : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hF
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun w _ _ => by positivity)
    _ ≤ F*(E.divisors.card : ℝ)^2 :=
      mul_le_mul_of_nonneg_left (supported_reciprocal_sum_le E (Nat.floor b) hE) hF
    _ = _ := by dsimp [F]; ring

/-- Actual coprime-Mobius convolution: both quantitative terms are
derived above.  The only input is the stated unrough classical theorem. -/
theorem uniform_coprimeMobiusError (hSW : ClassicalUnroughMobiusSW)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C U0 : ℝ, 0 < C ∧ 2 ≤ U0 ∧
      ∀ U V a b : ℝ, U0 ≤ U → 0 < V → U^(3/4 : ℝ) ≤ V →
        V ≤ a → a ≤ b → b ≤ 2*V →
        ∀ E q r : ℕ, E ≠ 0 → E.Coprime q → 0 < q →
          (q : ℝ) ≤ (Real.log U)^B → r.Coprime q →
          ‖coprimeMobiusError E a b q r‖ ≤
            C*V*(E.divisors.card : ℝ)^2/(Real.log U)^A +
              2*V^(7/8 : ℝ)*(E.divisors.card : ℝ)^2 := by
  obtain ⟨C,U0,hC,hU0,hsmall⟩ := uniform_smallError hSW A B hA hB
  refine ⟨C,U0,hC,hU0,?_⟩
  intro U V a b hU hV hVU ha hab hb E q r hE hEq hq hqlog hr
  have ha0 : 0 ≤ a := hV.le.trans ha
  have hb0 : 0 ≤ b := ha0.trans hab
  rw [coprimeMobiusError_eq_small_add_large E ha0 hb0 hEq hr]
  exact (norm_add_le _ _).trans (add_le_add
    (hsmall U V a b hU hV hVU ha hab hb E q r hE hEq hq hqlog hr)
    (largeError_norm_le E hE hV hb0 hb hq hEq hr))

/-- Exact Brun atoms after ell substitution.  No inverse is selected
when ell is a nonunit modulo q; both AP and mean then vanish. -/
theorem uniform_divisibleMobiusAtom (hSW : ClassicalUnroughMobiusSW)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C U0 : ℝ, 0 < C ∧ 2 ≤ U0 ∧
      ∀ U a b : ℝ, U0 ≤ U → U ≤ a → a ≤ b → b ≤ 2*U →
        ∀ ell q r : ℕ, 0 < ell → (ell : ℝ) ≤ U^(1/4 : ℝ) →
          0 < q → (q : ℝ) ≤ (Real.log U)^B → r.Coprime q →
          ‖divisibleMobiusAtom ell a b q r‖ ≤
            C*(U/(ell : ℝ))*(ell.divisors.card : ℝ)^2/(Real.log U)^A +
              2*(U/(ell : ℝ))^(7/8 : ℝ)*(ell.divisors.card : ℝ)^2 := by
  obtain ⟨C,U0,hC,hU0,hinner⟩ := uniform_coprimeMobiusError hSW A B hA hB
  refine ⟨C,U0,hC,hU0,?_⟩
  intro U a b hU ha hab hb ell q r hell hellU hq hqlog hr
  have hU2 : 2 ≤ U := hU0.trans hU
  have hUp : 0 < U := lt_of_lt_of_le (by norm_num) hU2
  have hlogU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU2)
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have ha0 : 0 ≤ a := hUp.le.trans ha
  have hb0 : 0 ≤ b := ha0.trans hab
  rw [divisibleMobiusAtom_eq ell ha0 hb0 hell hr]
  by_cases heq : ell.Coprime q
  · rw [if_pos heq,norm_mul]
    refine (mul_le_mul_of_nonneg_right (muCoefficient_norm_le ell) (norm_nonneg _)).trans ?_
    rw [one_mul]
    exact hinner U (U/(ell : ℝ)) (a/(ell : ℝ)) (b/(ell : ℝ)) hU
      (div_pos hUp hellR) (ell_inner_scale hUp hell hellU)
      (div_le_div_of_nonneg_right ha hellR.le) (div_le_div_of_nonneg_right hab hellR.le)
      (by simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb hellR.le)
      ell q (pulledResidue ell q r) hell.ne' heq hq hqlog (pulledResidue_coprime heq hr)
  · rw [if_neg heq,norm_zero]
    positivity

/-- The true fixed-order ell sum.  There is no accuracy-dependent
divisor exponent, and the U^(29/32) term is unchanged. -/
theorem uniform_brunMobiusPolynomial (hSW : ClassicalUnroughMobiusSW)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C U0 : ℝ, 0 < C ∧ 2 ≤ U0 ∧
      ∀ U a b : ℝ, U0 ≤ U → U ≤ a → a ≤ b → b ≤ 2*U →
        ∀ (S : Finset ℕ) (c : ℕ → ℂ),
          S ⊆ Icc 1 (Nat.floor (U^(1/4 : ℝ))) →
          (∀ ell ∈ S, Squarefree ell) → (∀ ell ∈ S, ‖c ell‖ ≤ 1) →
          ∀ q r : ℕ, 0 < q → (q : ℝ) ≤ (Real.log U)^B → r.Coprime q →
          ‖∑ ell ∈ S,c ell*divisibleMobiusAtom ell a b q r‖ ≤
            C*U*(1+Real.log U)^4/(Real.log U)^A +
              2*U^(29/32 : ℝ)*(1+Real.log U)^4 := by
  obtain ⟨C,U0,hC,hU0,hatom⟩ := uniform_divisibleMobiusAtom hSW A B hA hB
  refine ⟨C,U0,hC,hU0,?_⟩
  intro U a b hU ha hab hb S c hS hsq hc q r hq hqlog hr
  have hU2 : 2 ≤ U := hU0.trans hU
  have hU1 : 1 ≤ U := (by norm_num : (1:ℝ)≤2).trans hU2
  have hUp : 0 < U := zero_lt_one.trans_le hU1
  have hlogU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU2)
  have hS' (ell : ℕ) (hell : ell ∈ S) :
      0 < ell ∧ (ell : ℝ) ≤ U^(1/4 : ℝ) := by
    have hh := Finset.mem_Icc.mp (hS hell)
    exact ⟨hh.1,(Nat.le_floor_iff (Real.rpow_nonneg hUp.le _)).mp hh.2⟩
  have hsmallmass : (∑ ell ∈ S,(ell.divisors.card : ℝ)^2/(ell : ℝ)) ≤
      (1+Real.log U)^4 := by
    have hSD : S ⊆ Icc 1 (Nat.floor U) := by
      intro ell hell
      have hh := hS' ell hell
      have hpower : U^(1/4 : ℝ) ≤ U := by
        nth_rw 2 [← Real.rpow_one U]
        exact Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
      exact Finset.mem_Icc.mpr ⟨hh.1,(Nat.le_floor_iff hUp.le).mpr (hh.2.trans hpower)⟩
    refine (squarefree_divisor_square_harmonic_le S _ hSD hsq).trans ?_
    have hmax : max 1 (Nat.floor U : ℝ) ≤ U := max_le hU1 (Nat.floor_le hUp.le)
    apply pow_le_pow_left₀
      (by have := Real.log_nonneg (le_max_left 1 (Nat.floor U : ℝ)); linarith)
      (add_le_add_left (Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax) 1) 4
  calc
    _ ≤ ∑ ell ∈ S, ‖c ell*divisibleMobiusAtom ell a b q r‖ := norm_sum_le _ _
    _ ≤ ∑ ell ∈ S,
        (C*(U/(ell : ℝ))*(ell.divisors.card : ℝ)^2/(Real.log U)^A +
          2*(U/(ell : ℝ))^(7/8 : ℝ)*(ell.divisors.card : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro ell hell
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hc ell hell) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hatom U a b hU ha hab hb ell q r
          (hS' ell hell).1 (hS' ell hell).2 hq hqlog hr)
    _ = (C*U/(Real.log U)^A)*(∑ ell ∈ S,(ell.divisors.card : ℝ)^2/(ell : ℝ)) +
        (∑ ell ∈ S,2*(U/(ell : ℝ))^(7/8 : ℝ)*(ell.divisors.card : ℝ)^2) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ell hell
      ring
    _ ≤ (C*U/(Real.log U)^A)*(1+Real.log U)^4 +
        2*U^(29/32 : ℝ)*(1+Real.log U)^4 := add_le_add
      (mul_le_mul_of_nonneg_left hsmallmass (by positivity))
      (brun_rankin_sum_le S hU1 hS hsq)
    _ = _ := by ring

end
end ImbalancedChen.P5Z.ActualRoughMobiusSmallSW
