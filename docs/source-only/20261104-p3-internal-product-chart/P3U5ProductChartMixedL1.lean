import ImbalancedChen.P3U5PhysicalProductChart

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Actual whole-space mixed L1 norms of the atlas * all group hats * one
complete-product trim, with fixed compact extension. The result supplies
the D-side of the paper's (F) calculation, NOT its Fourier identity or
arithmetic tail estimate. The remaining general W and HB log factors are
not silently assigned this bound.
-/
namespace ImbalancedChen.P3U5ProductChartMixedL1
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
open P3AffineTransitionJets P3U5RootAtlas
open P3U5ChartMixedL1Budget P3U5ProductChartDerivativeBudget P3U5PhysicalProductChart

/-- Actual derivatives of the physical multiplier, not formal jets. -/
def mixedD {d : ℕ} (f : Point d → ℝ) : ℝ :=
  ∑ S : Finset (Fin d),∫ x,|mixed (doubled S) f x|

theorem mixed_productProfile_zero_outside {d g : ℕ} (is : List (Fin d)) (ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) (l : Lane) :
    ∀ x ∉ cube d,mixed is (productProfile ell R slot group b trim m l) x=0 :=
  mixed_zero_on_open (isClosed_cube d).isOpen_compl
    (fun x hx => productProfile_zero_outside ell R slot group b trim m l hx) is

theorem mixed_productProfile_integrable {d g : ℕ} (is : List (Fin d)) (ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (m : ℕ) (l : Lane) :
    Integrable (mixed is (productProfile ell R slot group b trim m l)) := by
  have hs : Function.support (mixed is (productProfile ell R slot group b trim m l)) ⊆ cube d := by
    intro x hx
    by_contra hn
    exact hx (mixed_productProfile_zero_outside is ell R slot group b trim m l x hn)
  have hc : HasCompactSupport (mixed is (productProfile ell R slot group b trim m l)) :=
    (isCompact_cube d).of_isClosed_subset isClosed_closure (closure_minimal hs (isClosed_cube d))
  exact (continuous_mixed_productProfile is ell R slot group b trim m l).integrable_of_hasCompactSupport hc

theorem exists_productProfile_mixed_L1 (d g q : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ m : ℕ,∀ l : Lane,∀ v : Fin q → Fin d,
      (∫ x,|mixed (List.ofFn v) (productProfile ell R slot group b trim m l) x|) ≤
        C*(m+1 : ℝ)^q := by
  obtain ⟨C,hC,hbound⟩ := exists_productProfile_mixed_bound d g q
  have hV : 0 ≤ cubeVolume d := ENNReal.toReal_nonneg
  refine ⟨(cubeVolume d+1)*C,by nlinarith,?_⟩
  intro ell hell R slot group b trim m l v
  let f := mixed (List.ofFn v) (productProfile ell R slot group b trim m l)
  have hf := continuous_mixed_productProfile (List.ofFn v) ell R slot group b trim m l
  have heq : (fun x => |f x|)=(cube d).indicator (fun x => |f x|) := by
    funext x
    by_cases hx : x ∈ cube d
    · simp only [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        mixed_productProfile_zero_outside (List.ofFn v) ell R slot group b trim m l x hx]
      exact abs_zero
  have hconst : IntegrableOn (fun _ : Point d => C*(m+1 : ℝ)^q) (cube d) :=
    ContinuousOn.integrableOn_compact (isCompact_cube d) continuous_const.continuousOn
  have hi : (∫ x in cube d,|f x|) ≤ (∫ _x : Point d in cube d,C*(m+1 : ℝ)^q) :=
    integral_mono (ContinuousOn.integrableOn_compact (isCompact_cube d) hf.abs.continuousOn)
      hconst (fun x => hbound ell hell R slot group b trim m l v x)
  calc
    _ = ∫ x in cube d,|f x| := by rw [heq,integral_indicator (isClosed_cube d).measurableSet]
    _ ≤ _ := hi
    _ = cubeVolume d*(C*(m+1 : ℝ)^q) := by simp [cubeVolume]
    _ ≤ _ := by
      have hp : 0 ≤ C*(m+1 : ℝ)^q := by positivity
      nlinarith

/-- Both the number of coordinates d and number of original groups g are
fixed before C. The constants do NOT depend on later scale ratios or trim. -/
theorem exists_productD_budget (d g : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ m : ℕ,∀ l : Lane,
      mixedD (productProfile ell R slot group b trim m l) ≤ C*(m+1 : ℝ)^(2*d) := by
  have h : ∀ S : Finset (Fin d),∃ C : ℝ,1 ≤ C ∧
      ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ m : ℕ,∀ l : Lane,
      (∫ x,|mixed (doubled S) (productProfile ell R slot group b trim m l) x|) ≤
        C*(m+1 : ℝ)^(doubled S).length := by
    intro S
    obtain ⟨C,hC,hc⟩ := exists_productProfile_mixed_L1 d g (doubled S).length
    refine ⟨C,hC,?_⟩
    intro ell hell R slot group b trim m l
    have hv : List.ofFn (fun i : Fin (doubled S).length => (doubled S)[i])=doubled S := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'; simp
    simpa only [hv] using hc ell hell R slot group b trim m l
      (fun i : Fin (doubled S).length => (doubled S)[i])
  choose c hc hb using h
  let C := 1+∑ S : Finset (Fin d),c S
  have hc0 (S : Finset (Fin d)) : 0 ≤ c S := zero_le_one.trans (hc S)
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    have hsum : 0 ≤ ∑ S : Finset (Fin d),c S := Finset.sum_nonneg (fun S _ => hc0 S)
    linarith
  intro ell hell R slot group b trim m l
  have hm : (1 : ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg m]
  calc
    _ ≤ ∑ S : Finset (Fin d),c S*(m+1 : ℝ)^(doubled S).length :=
      Finset.sum_le_sum (fun S _ => hb S ell hell R slot group b trim m l)
    _ ≤ ∑ S : Finset (Fin d),c S*(m+1 : ℝ)^(2*d) :=
      Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hm (doubled_length_le S)) (hc0 S))
    _ = (∑ S : Finset (Fin d),c S)*(m+1 : ℝ)^(2*d) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)

theorem exists_productD_polylog (d g B : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ N : ℕ,1 ≤ Real.log (N : ℝ) → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ m : ℕ,
      (m+1 : ℝ) ≤ (Real.log (N : ℝ))^B → ∀ l : Lane,
      mixedD (productProfile (Real.log (N : ℝ)) R slot group b trim m l) ≤
        C*(Real.log (N : ℝ))^(B*(2*d)) := by
  obtain ⟨C,hC,hc⟩ := exists_productD_budget d g
  refine ⟨C,hC,?_⟩
  intro N hN R slot group b trim m hm l
  apply (hc _ hN R slot group b trim m l).trans
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤m+1) hm (2*d)
  simpa only [pow_mul] using mul_le_mul_of_nonneg_left hp (zero_le_one.trans hC)

/-- Final actual-factor endpoint: G may be instantiated by groupBase U.
The smooth cutoff is the COMPLETE N^(1-kappa0) trim from the manuscript;
no support-level, Fourier, PP, composite derivative or L1 bound is an input. -/
theorem exists_physicalProduct_D_polylog (d g B : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ N : ℕ,2 ≤ N → 1 ≤ Real.log (N : ℝ) →
      ∀ G R : Fin g → ℝ,(∀ j,0 < G j) → (∀ j,0 < R j) →
      ∀ group : Fin d → Fin g,∀ pair : Fin 2 → Fin g,pair 0 ≠ pair 1 →
      ∀ kappa0 : ℝ,∀ m : ℕ,(m+1 : ℝ) ≤ (Real.log (N : ℝ))^B → ∀ l : Lane,
      mixedD (physicalProfile (Real.log (N : ℝ)) G R group pair
        ((N : ℝ)^(1-kappa0)) m l) ≤ C*(Real.log (N : ℝ))^(B*(2*d)) := by
  obtain ⟨C,hC,hc⟩ := exists_productD_polylog d g B
  refine ⟨C,hC,?_⟩
  intro N hN hlog G R hG hR group pair hpair kappa0 m hm l
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [physicalProfile_eq_productProfile _ G R hG hR group pair hpair (Real.rpow_pos_of_pos hNp _)]
  exact hc N hlog _ _ group _ _ m hm l

/-- Integrability is provided separately, so the ledger does not rely on
Lean's value for an integral whose integrability is unknown. -/
theorem physicalProduct_mixed_integrable {d g : ℕ} (is : List (Fin d))
    (ell : ℝ) (G R : Fin g → ℝ) (hG : ∀ j,0<G j) (hR : ∀ j,0<R j)
    (group : Fin d → Fin g) (pair : Fin 2 → Fin g) (hpair : pair 0 ≠ pair 1)
    {T : ℝ} (hT : 0<T) (m : ℕ) (l : Lane) :
    Integrable (mixed is (physicalProfile ell G R group pair T m l)) := by
  rw [physicalProfile_eq_productProfile ell G R hG hR group pair hpair hT]
  exact mixed_productProfile_integrable _ _ _ _ _ _ _ _ _

end
end ImbalancedChen.P3U5ProductChartMixedL1
