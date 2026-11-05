import ImbalancedChen.P3U5HBLogChart

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Actual mixed/L1 budget of the concrete atlas * all original group hats *
complete trim * one physical HB log ratio per group. The scalar extensions
are smooth globally and equal the physical ratios on admitted source points.
General W, Fourier inversion/tail and arithmetic PP payment remain separate.
-/
namespace ImbalancedChen.P3U5HBLogMixedL1
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter Set
open P3AffineTransitionJets P3SmoothScalarJets P3U5RootAtlas
open P3U5LogChartDerivativeBudget P3U5ProductChartDerivativeBudget
open P3U5PhysicalProductChart P3U5ChartMixedL1Budget P3U5HBLogChart

/-- Only the exponent floor a is fixed before C. All later log offsets,
actual original group assignments and selected log slots are uniform. -/
theorem exists_hbProfile_mixed_bound (d g q : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d,∀ m : ℕ,∀ l : Lane,∀ is : Fin q → Fin d,∀ x : Point d,
      |mixed (List.ofFn is) (hbProfile a ell R slot group b trim u v pick m l) x| ≤
        C*(m+1 : ℝ)^q := by
  obtain ⟨C,hC,hb⟩ := exists_family_mixed_boundS
    (P3HBLogScalarProfiles.scalar a) (P3HBLogScalarProfiles.scalar_contDiff ha)
    (P3HBLogScalarProfiles.exists_scalar_derivative_bound a ha) (hbExpr d g) q 2 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro ell hell R slot group b trim u v pick m l is x
  rw [← eval_hbExpr]
  exact hb hbKind (hbOffsets ell R m b trim u v pick) (hbSlopes ell slot m group pick)
    (hbSlopes_bound hell slot group pick m) (m+1) (by positivity) l is x

theorem continuous_mixed_hbProfile {d g : ℕ} (is : List (Fin d))
    (a : ℝ) (ha : 0 < a) (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) (l : Lane) :
    Continuous (mixed is (hbProfile a ell R slot group b trim u v pick m l)) := by
  rw [← eval_hbExpr]
  exact continuous_mixed_evalS _ _ _
    (fun j => P3HBLogScalarProfiles.scalar_contDiff ha (hbKind j)) _ _ _

theorem hbProfile_zero_outside {d g : ℕ} (a ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) (l : Lane) {x : Point d}
    (hx : x ∉ cube d) : hbProfile a ell R slot group b trim u v pick m l x=0 := by
  rw [hbProfile,productProfile_zero_outside ell R slot group b trim m l hx,zero_mul]

theorem mixed_hbProfile_zero_outside {d g : ℕ} (is : List (Fin d))
    (a ell : ℝ) (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) (l : Lane) :
    ∀ x ∉ cube d,mixed is (hbProfile a ell R slot group b trim u v pick m l) x=0 :=
  mixed_zero_on_open (isClosed_cube d).isOpen_compl
    (fun x hx => hbProfile_zero_outside a ell R slot group b trim u v pick m l hx) is

theorem mixed_hbProfile_integrable {d g : ℕ} (is : List (Fin d))
    (a : ℝ) (ha : 0 < a) (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) (l : Lane) :
    Integrable (mixed is (hbProfile a ell R slot group b trim u v pick m l)) := by
  have hs : Function.support (mixed is (hbProfile a ell R slot group b trim u v pick m l)) ⊆ cube d := by
    intro x hx
    by_contra hn
    exact hx (mixed_hbProfile_zero_outside is a ell R slot group b trim u v pick m l x hn)
  have hc : HasCompactSupport (mixed is (hbProfile a ell R slot group b trim u v pick m l)) :=
    (isCompact_cube d).of_isClosed_subset isClosed_closure
      (closure_minimal hs (isClosed_cube d))
  exact (continuous_mixed_hbProfile is a ha ell R slot group b trim u v pick m l).
    integrable_of_hasCompactSupport hc

theorem exists_hbProfile_mixed_L1_bound (d g q : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d,∀ m : ℕ,∀ l : Lane,∀ is : Fin q → Fin d,
      (∫ x,|mixed (List.ofFn is) (hbProfile a ell R slot group b trim u v pick m l) x|) ≤
        C*(m+1 : ℝ)^q := by
  obtain ⟨C,hC,hb⟩ := exists_hbProfile_mixed_bound d g q a ha
  have hV : 0 ≤ cubeVolume d := ENNReal.toReal_nonneg
  refine ⟨(cubeVolume d+1)*C,by nlinarith,?_⟩
  intro ell hell R slot group b trim u v pick m l is
  let f := mixed (List.ofFn is) (hbProfile a ell R slot group b trim u v pick m l)
  have hf := continuous_mixed_hbProfile (List.ofFn is) a ha ell R slot group b trim u v pick m l
  have heq : (fun x => |f x|)=(cube d).indicator (fun x => |f x|) := by
    funext x
    by_cases hx : x ∈ cube d
    · simp only [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        mixed_hbProfile_zero_outside (List.ofFn is) a ell R slot group b trim u v pick m l x hx]
      exact abs_zero
  have hi : (∫ x in cube d,|f x|) ≤ ∫ _x : Point d in cube d,C*(m+1 : ℝ)^q :=
    integral_mono (ContinuousOn.integrableOn_compact (isCompact_cube d) hf.abs.continuousOn)
      (ContinuousOn.integrableOn_compact (isCompact_cube d) continuous_const.continuousOn)
      (fun x => hb ell hell R slot group b trim u v pick m l is x)
  calc
    _ = ∫ x in cube d,|f x| := by rw [heq,integral_indicator (isClosed_cube d).measurableSet]
    _ ≤ _ := hi
    _ = cubeVolume d*(C*(m+1 : ℝ)^q) := by simp [cubeVolume]
    _ ≤ _ := by
      have hp : 0 ≤ C*(m+1 : ℝ)^q := by positivity
      nlinarith

/-- The actual mixed L1 sum D for the extended HB chart. -/
def hbD {d g : ℕ} (a ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) (l : Lane) : ℝ :=
  ∑ S : Finset (Fin d),∫ x,|mixed (doubled S) (hbProfile a ell R slot group b trim u v pick m l) x|

theorem exists_hbD_budget (d g : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d,∀ m : ℕ,∀ l : Lane,
      hbD a ell R slot group b trim u v pick m l ≤ C*(m+1 : ℝ)^(2*d) := by
  have hh := fun S : Finset (Fin d) => exists_hbProfile_mixed_L1_bound d g (doubled S).length a ha
  choose c hc hb using hh
  let C := 1+∑ S : Finset (Fin d),c S
  have hc0 (S : Finset (Fin d)) : 0 ≤ c S := zero_le_one.trans (hc S)
  refine ⟨C,?_,?_⟩
  · have hsum := Finset.sum_nonneg (s:=Finset.univ) (fun S _ => hc0 S)
    dsimp [C]; linarith
  intro ell hell R slot group b trim u v pick m l
  have hm : (1 : ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg m]
  have heach (S : Finset (Fin d)) :
      (∫ x,|mixed (doubled S) (hbProfile a ell R slot group b trim u v pick m l) x|) ≤
        c S*(m+1 : ℝ)^(2*d) := by
    have hv : List.ofFn (fun i : Fin (doubled S).length => (doubled S)[i])=doubled S := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'; simp
    have h := hb S ell hell R slot group b trim u v pick m l
      (fun i : Fin (doubled S).length => (doubled S)[i])
    rw [hv] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hm (doubled_length_le S)) (hc0 S))
  calc
    _ ≤ ∑ S : Finset (Fin d),c S*(m+1 : ℝ)^(2*d) := Finset.sum_le_sum (fun S _ => heach S)
    _ = (∑ S : Finset (Fin d),c S)*(m+1 : ℝ)^(2*d) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)

theorem exists_hbD_polylog (d g B : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ N : ℕ,1 ≤ Real.log (N : ℝ) → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d,∀ m : ℕ,(m+1 : ℝ) ≤ (Real.log (N : ℝ))^B → ∀ l : Lane,
      hbD a (Real.log (N : ℝ)) R slot group b trim u v pick m l ≤
        C*(Real.log (N : ℝ))^(B*(2*d)) := by
  obtain ⟨C,hC,hb⟩ := exists_hbD_budget d g a ha
  refine ⟨C,hC,?_⟩
  intro N hN R slot group b trim u v pick m hm l
  apply (hb _ hN R slot group b trim u v pick m l).trans
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m+1) hm (2*d)
  simpa only [pow_mul] using mul_le_mul_of_nonneg_left hp (zero_le_one.trans hC)

/-- Complete physical trim and original group bases are substituted,
not replaced by a residual quotient. Equality to the physical HB factor
on the source is supplied by eventually_physical_hb_identity. -/
theorem exists_physical_hbD_polylog (d g B : ℕ) (alpha : ℝ) (ha : 0 < alpha) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ N : ℕ,1 ≤ Real.log (N : ℝ) →
      ∀ U : Fin d → ℝ,∀ R : Fin g → ℝ,∀ group : Fin d → Fin g,
      ∀ pair : Fin 2 → Fin g,∀ pick : Fin g → Fin d,∀ kappa0 : ℝ,
      ∀ m : ℕ,(m+1 : ℝ) ≤ (Real.log (N : ℝ))^B → ∀ l : Lane,
      hbD (alpha/2) (Real.log (N : ℝ)) (fun j => groupBase U group (pair j))
        (pairSlots group pair) group (fun j => Real.log (groupBase U group j/R j))
        (Real.log ((∏ j,groupBase U group j)/(N : ℝ)^(1-kappa0)))
        (fun i => Real.log (U i)) (fun j => Real.log (groupBase U group j)) pick m l ≤
          C*(Real.log (N : ℝ))^(B*(2*d)) := by
  obtain ⟨C,hC,hb⟩ := exists_hbD_polylog d g B (alpha/2) (half_pos ha)
  exact ⟨C,hC,fun N hN U R group pair pick kappa0 m hm l =>
    hb N hN _ _ group _ _ _ _ pick m hm l⟩

end
end ImbalancedChen.P3U5HBLogMixedL1
