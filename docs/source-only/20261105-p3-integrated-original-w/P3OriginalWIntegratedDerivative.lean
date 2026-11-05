import ImbalancedChen.P3PhysicalOriginalWInsertion
import ImbalancedChen.P3U5OriginalWMixedL1

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

The previous W*HB estimate required pointwise bounded partial derivatives of
the ORIGINAL W. The manuscript permits polylogarithmic *integrated* Euler
derivative norms instead. This file pays the genuine derivative-integral
budget using the exact 2^q-term Leibniz rule; it does not replace integrated
W norms with sup norms or assume a bound on the desired W*HB product.

Each derivative of the HB multiplier is bounded uniformly; each derivative
of the arbitrary original W is integrated over the old fixed cube. The
original signed rho, physical group products and arithmetic kernel are
unchanged. No Fourier or distribution statement is asserted.
-/

namespace ImbalancedChen.P3OriginalWIntegratedDerivative
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
open P3AffineTransitionJets P3FiniteMixedLeibniz
open P3U5RootAtlas P3U5HBLogChart
open P3U5ChartMixedL1Budget P3U5HBLogMixedL1
open P3U5OriginalWComposition P3U5OriginalWMixedL1
open P3PhysicalOriginalW

/-- The primitive W condition is an integral of W's OWN ordinary mixed
partials on the fixed HB chart cube; it is NOT the combined D budget. -/
def PrimitiveIntegratedW {d : ℕ} (W : Point d → ℝ) (q : ℕ) (M : ℝ) : Prop :=
  WDerivCompatible W ∧
  (∀ js : List (Fin d), Continuous (mixed js W)) ∧
  ∀ js : List (Fin d), js.length ≤ q →
    (∫ x in cube d, |mixed js W x|) ≤ M

private theorem continuous_sum_abs_W {d : ℕ} (W : Point d → ℝ)
    (hc : ∀ js : List (Fin d), Continuous (mixed js W))
    (ps : List (List (Fin d) × List (Fin d))) :
    Continuous (fun x : Point d =>
      (ps.map (fun p => |mixed p.1 W x|)).sum) := by
  induction ps with
  | nil =>
      simpa using (continuous_const :
        Continuous (fun _ : Point d => (0 : ℝ)))
  | cons p ps ih =>
      simpa only [List.map_cons, List.sum_cons] using
        (hc p.1).abs.add ih

/-- Integrate the repeated-coordinate Leibniz list AS A LIST, rather
than making it a finset and losing its binomial multiplicities. -/
private theorem integral_list_abs_W_le {d : ℕ} (W : Point d → ℝ)
    (hc : ∀ js : List (Fin d), Continuous (mixed js W))
    (q : ℕ) (M : ℝ)
    (hM : ∀ js : List (Fin d), js.length ≤ q →
      (∫ x in cube d, |mixed js W x|) ≤ M)
    (ps : List (List (Fin d) × List (Fin d)))
    (hps : ∀ p ∈ ps, p.1.length ≤ q) :
    (∫ x in cube d,
      (ps.map (fun p => |mixed p.1 W x|)).sum) ≤
      (ps.length : ℝ) * M := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp : p.1.length ≤ q := hps p (by simp)
      have hps' : ∀ t ∈ ps, t.1.length ≤ q := by
        intro t ht
        exact hps t (by simp [ht])
      have hfirst : IntegrableOn (fun x : Point d => |mixed p.1 W x|)
          (cube d) :=
        ContinuousOn.integrableOn_compact (isCompact_cube d)
          (hc p.1).abs.continuousOn
      have htail : IntegrableOn (fun x : Point d =>
          (ps.map (fun t => |mixed t.1 W x|)).sum) (cube d) :=
        ContinuousOn.integrableOn_compact (isCompact_cube d)
          (continuous_sum_abs_W W hc ps).continuousOn
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      rw [integral_add hfirst htail]
      calc
        _ ≤ M + (ps.length : ℝ)*M := add_le_add (hM p.1 hp) (ih hps')
        _ = ((ps.length : ℝ)+1)*M := by ring

/-- Each HB factor in a Leibniz term is controlled by the already
constructed *actual* profile bound; W remains under the integral. -/
private theorem abs_list_products_le {d : ℕ} (W H : Point d → ℝ)
    (ps : List (List (Fin d) × List (Fin d))) :
    ∀ B : ℝ, 0 ≤ B →
      (∀ p ∈ ps, ∀ x, |mixed p.2 H x| ≤ B) →
      ∀ x, |(ps.map (fun p => mixed p.1 W x * mixed p.2 H x)).sum| ≤
        B * (ps.map (fun p => |mixed p.1 W x|)).sum := by
  induction ps with
  | nil =>
      intro B hB h x
      simp
  | cons p ps ih =>
      intro B hB h x
      have hp : |mixed p.2 H x| ≤ B := h p (by simp) x
      have hrest : ∀ t ∈ ps, ∀ x, |mixed t.2 H x| ≤ B := by
        intro t ht y
        exact h t (by simp [ht]) y
      simp only [List.map_cons, List.sum_cons]
      calc
        _ ≤ |mixed p.1 W x * mixed p.2 H x| +
            |(ps.map (fun t => mixed t.1 W x*mixed t.2 H x)).sum| :=
              abs_add _ _
        _ ≤ |mixed p.1 W x|*B +
            B*(ps.map (fun t => |mixed t.1 W x|)).sum := by
              apply add_le_add
              · rw [abs_mul]
                exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
              · exact ih B hB hrest x
        _ = B * (|mixed p.1 W x| +
            (ps.map (fun t => |mixed t.1 W x|)).sum) := by ring

/-- Actual whole-space mixed derivative L1, from primitive integrated
W norms on the fixed cube and the HB derivative bound. No assumption
about an L1 norm of W*HB or about its Fourier transform is made. -/
theorem exists_integrated_mixed_L1_bound (d g q : ℕ)
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ell : ℝ, 1 ≤ ell →
      ∀ R : Fin 2 → ℝ, ∀ slot : Fin d → Option (Fin 2),
      ∀ group : Fin d → Fin g, ∀ b : Fin g → ℝ,
      ∀ trim : ℝ, ∀ u : Fin d → ℝ, ∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d, ∀ m : ℕ, ∀ l : Lane,
      ∀ W : Point d → ℝ, ∀ M : ℝ, 0 ≤ M →
      PrimitiveIntegratedW W q M →
      ∀ is : Fin q → Fin d,
      (∫ x, |mixed (List.ofFn is)
        (withOriginalW W a ell R slot group b trim u v pick m l) x|) ≤
        C*M*(m+1 : ℝ)^q := by
  obtain ⟨Ch,hCh,hHB⟩ := exists_hb_upto_mixed_bound d g q a ha
  let C : ℝ := (2 : ℝ)^q * Ch
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    have hp : (1 : ℝ) ≤ 2^q :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  intro ell hell R slot group b trim u v pick m l W M hM hW is
  rcases hW with ⟨hcomp,hcont,hWint⟩
  let H : Point d → ℝ := hbProfile a ell R slot group b trim u v pick m l
  let ps : List (List (Fin d) × List (Fin d)) := splits (List.ofFn is)
  let B : ℝ := Ch*(m+1 : ℝ)^q
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hHBbound : ∀ p ∈ ps, ∀ x, |mixed p.2 H x| ≤ B := by
    intro p hp x
    have hlength := splits_total_length (List.ofFn is) p hp
    have hsmall : p.2.length ≤ q := by
      rw [List.length_ofFn] at hlength
      omega
    exact hHB ell hell R slot group b trim u v pick m l p.2 hsmall x
  have hWlength : ∀ p ∈ ps, p.1.length ≤ q := by
    intro p hp
    have hlength := splits_total_length (List.ofFn is) p hp
    rw [List.length_ofFn] at hlength
    omega
  have hpoint (x : Point d) :
      |mixed (List.ofFn is)
         (withOriginalW W a ell R slot group b trim u v pick m l) x| ≤
      B*(ps.map (fun p => |mixed p.1 W x|)).sum := by
    change |mixed (List.ofFn is) (fun z => W z*H z) x| ≤ _
    rw [mixed_product_eq (fun js => mixed js W)
      (fun js => mixed js H) hcomp
      (hb_compatible a ha ell R slot group b trim u v pick m l)
      (List.ofFn is)]
    exact abs_list_products_le W H ps B hB hHBbound x
  have hleft : IntegrableOn (fun x : Point d =>
      |mixed (List.ofFn is)
        (withOriginalW W a ell R slot group b trim u v pick m l) x|)
        (cube d) :=
    ContinuousOn.integrableOn_compact (isCompact_cube d)
      (continuous_mixed_withOriginalW W hcomp hcont (List.ofFn is)
        a ha ell R slot group b trim u v pick m l).abs.continuousOn
  have hright : IntegrableOn (fun x : Point d =>
      B*(ps.map (fun p => |mixed p.1 W x|)).sum) (cube d) :=
    ContinuousOn.integrableOn_compact (isCompact_cube d)
      (continuous_const.mul (continuous_sum_abs_W W hcont ps)).continuousOn
  have hmono :
      (∫ x in cube d,
        |mixed (List.ofFn is)
          (withOriginalW W a ell R slot group b trim u v pick m l) x|) ≤
      ∫ x in cube d, B*(ps.map (fun p => |mixed p.1 W x|)).sum :=
    integral_mono hleft hright (fun x => hpoint x)
  have hsum := integral_list_abs_W_le W hcont q M hWint ps hWlength
  have heq : (fun x : Point d =>
      |mixed (List.ofFn is)
        (withOriginalW W a ell R slot group b trim u v pick m l) x|) =
      (cube d).indicator (fun x : Point d =>
      |mixed (List.ofFn is)
        (withOriginalW W a ell R slot group b trim u v pick m l) x|) := by
    funext x
    by_cases hx : x ∈ cube d
    · simp only [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        mixed_withOriginalW_zero_outside (List.ofFn is) W a ell R slot
          group b trim u v pick m l x hx]
      exact abs_zero
  calc
    _ = ∫ x in cube d,
          |mixed (List.ofFn is)
            (withOriginalW W a ell R slot group b trim u v pick m l) x| := by
          rw [heq,integral_indicator (isClosed_cube d).measurableSet]
    _ ≤ ∫ x in cube d,
          B*(ps.map (fun p => |mixed p.1 W x|)).sum := hmono
    _ = B*(∫ x in cube d,
          (ps.map (fun p => |mixed p.1 W x|)).sum) := by
          rw [integral_const_mul]
    _ ≤ B*((ps.length : ℝ)*M) :=
      mul_le_mul_of_nonneg_left hsum hB
    _ = C*M*(m+1 : ℝ)^q := by
      simp only [ps, splits_length, List.length_ofFn, B, C]
      ring

/-- The manuscript's D is the finite sum of actual doubled-coordinate
L1 norms. The integrated class avoids the old, stronger sup norm. -/
theorem exists_originalWD_integrated (d g : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ell : ℝ, 1 ≤ ell →
      ∀ R : Fin 2 → ℝ, ∀ slot : Fin d → Option (Fin 2),
      ∀ group : Fin d → Fin g, ∀ b : Fin g → ℝ,
      ∀ trim : ℝ, ∀ u : Fin d → ℝ, ∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d, ∀ m : ℕ, ∀ l : Lane,
      ∀ W : Point d → ℝ, ∀ M : ℝ, 0 ≤ M →
      PrimitiveIntegratedW W (2*d) M →
      originalWD W a ell R slot group b trim u v pick m l ≤
        C*M*(m+1 : ℝ)^(2*d) := by
  have hh := fun S : Finset (Fin d) =>
    exists_integrated_mixed_L1_bound d g (doubled S).length a ha
  choose c hc hb using hh
  let C := 1+∑ S : Finset (Fin d), c S
  have hc0 (S : Finset (Fin d)) : 0 ≤ c S := zero_le_one.trans (hc S)
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    have hs := Finset.sum_nonneg (s:=Finset.univ) (fun S _ => hc0 S)
    linarith
  intro ell hell R slot group b trim u v pick m l W M hM hW
  rcases hW with ⟨hcomp,hcont,hWint⟩
  have hm : (1 : ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg m]
  have ht (S : Finset (Fin d)) :
      (∫ x, |mixed (doubled S)
        (withOriginalW W a ell R slot group b trim u v pick m l) x|) ≤
      c S*M*(m+1 : ℝ)^(2*d) := by
    have hv : List.ofFn (fun i : Fin (doubled S).length =>
        (doubled S)[i]) = doubled S := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'; simp
    have hclass : PrimitiveIntegratedW W (doubled S).length M := by
      refine ⟨hcomp,hcont,?_⟩
      intro js hjs
      exact hWint js (hjs.trans (doubled_length_le S))
    have h := hb S ell hell R slot group b trim u v pick m l W M hM
      hclass (fun i : Fin (doubled S).length => (doubled S)[i])
    rw [hv] at h
    have hp : (m+1 : ℝ)^(doubled S).length ≤ (m+1 : ℝ)^(2*d) :=
      pow_le_pow_right₀ hm (doubled_length_le S)
    exact h.trans (mul_le_mul_of_nonneg_left hp
      (mul_nonneg (hc0 S) hM))
  calc
    _ ≤ ∑ S : Finset (Fin d), c S*M*(m+1 : ℝ)^(2*d) :=
      Finset.sum_le_sum (fun S _ => ht S)
    _ = (∑ S : Finset (Fin d), c S)*(M*(m+1 : ℝ)^(2*d)) := by
      simp_rw [mul_assoc]
      rw [← Finset.sum_mul]
    _ ≤ C*(M*(m+1 : ℝ)^(2*d)) :=
      mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
        (by positivity)
    _ = C*M*(m+1 : ℝ)^(2*d) := by ring

/-- The original W's own integrated derivative degree E is paid exactly
once. The HB chart contributes 2*d*B, with constants preceding N/W. -/
theorem exists_originalWD_integrated_polylog (d g E B : ℕ)
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ,
      1 ≤ Real.log (N : ℝ) →
      ∀ R : Fin 2 → ℝ, ∀ slot : Fin d → Option (Fin 2),
      ∀ group : Fin d → Fin g, ∀ b : Fin g → ℝ,
      ∀ trim : ℝ, ∀ u : Fin d → ℝ, ∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d, ∀ m : ℕ,
      (m+1 : ℝ) ≤ (Real.log (N : ℝ))^B →
      ∀ l : Lane, ∀ W : Point d → ℝ, ∀ A : ℝ, 0 ≤ A →
      PrimitiveIntegratedW W (2*d) (A*(Real.log (N : ℝ))^E) →
      originalWD W a (Real.log (N : ℝ)) R slot group b trim u v pick m l ≤
        C*A*(Real.log (N : ℝ))^(E+B*(2*d)) := by
  obtain ⟨C,hC,hb⟩ := exists_originalWD_integrated d g a ha
  refine ⟨C,hC,?_⟩
  intro N hN R slot group b trim u v pick m hm l W A hA hW
  have hM : 0 ≤ A*(Real.log (N : ℝ))^E := by positivity
  have h := hb (Real.log (N : ℝ)) hN R slot group b trim u v pick
    m l W (A*(Real.log (N : ℝ))^E) hM hW
  have hp : (m+1 : ℝ)^(2*d) ≤
      (Real.log (N : ℝ))^(B*(2*d)) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m+1)
      hm (2*d)
    simpa only [pow_mul] using hh
  calc
    _ ≤ C*(A*(Real.log (N : ℝ))^E)*(m+1 : ℝ)^(2*d) := h
    _ ≤ C*(A*(Real.log (N : ℝ))^E)*
        (Real.log (N : ℝ))^(B*(2*d)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C*A*(Real.log (N : ℝ))^(E+B*(2*d)) := by
      rw [pow_add]
      ring

/-- Physically labelled original W_T, evaluated on the actual ORIGINAL
group products. The premise is ONLY the primitive integrated Euler norm
of this explicitly defined pullback, not a new filtered W or PP bound. -/
def PhysicalIntegratedClass {d g : ℕ} (W : (Fin g → ℝ) → ℝ)
    (U : Fin d → ℝ) (group : Fin d → Fin g)
    (q : ℕ) (M : ℝ) : Prop :=
  PrimitiveIntegratedW (pulledOriginalW W U group) q M

/-- Specialize the integrated-norm theorem to the SAME physical-labelled
W already identified in P3PhysicalOriginalWInsertion. The needed family
membership is visible and must be supplied for each actual W_T. -/
theorem exists_physicalW_integrated_polylog (d g E B : ℕ)
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ,
      1 ≤ Real.log (N : ℝ) →
      ∀ U : Fin d → ℝ, (∀ i, 0 < U i) →
      ∀ W : (Fin g → ℝ) → ℝ,
      ∀ group : Fin d → Fin g,
      ∀ pair : Fin 2 → Fin g, pair 0 ≠ pair 1 →
      ∀ R : Fin 2 → ℝ, ∀ b : Fin g → ℝ,
      ∀ trim : ℝ, ∀ u : Fin d → ℝ, ∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d, ∀ m : ℕ,
      (m+1 : ℝ) ≤ (Real.log (N : ℝ))^B →
      ∀ l : Lane, ∀ A : ℝ, 0 ≤ A →
      PhysicalIntegratedClass W U group (2*d)
        (A*(Real.log (N : ℝ))^E) →
      originalWD (pulledOriginalW W U group) a
        (Real.log (N : ℝ)) R
        (P3U5PhysicalProductChart.pairSlots group pair)
        group b trim u v pick m l ≤
        C*A*(Real.log (N : ℝ))^(E+B*(2*d)) := by
  obtain ⟨C,hC,hb⟩ := exists_originalWD_integrated_polylog d g E B a ha
  refine ⟨C,hC,?_⟩
  intro N hN U hU W group pair hpair R b trim u v pick m hm l A hA hW
  exact hb N hN R (P3U5PhysicalProductChart.pairSlots group pair)
    group b trim u v pick m hm l (pulledOriginalW W U group) A hA hW

end
end ImbalancedChen.P3OriginalWIntegratedDerivative
