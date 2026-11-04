import ImbalancedChen.P3U5LogChartDerivativeBudget
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Actual mixed derivative L1 ledger for the compactified U5 atlas multiplier.
The ledger is the D appearing in the manuscript's Fourier calculation,
NOT a newly assumed Fourier norm and NOT a full PP estimate. Every derivative
is an ordinary repeated coordinate derivative of the original profile.
-/
namespace ImbalancedChen.P3U5ChartMixedL1Budget
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter Set
open P3AffineTransitionJets P3U5LogChartDerivativeBudget P3U5RootAtlas

/-- Fixed support box, independent of N, m, root level and group scales. -/
def cube (d : ℕ) : Set (Point d) := Icc (fun _ => -2) (fun _ => 2)

theorem isCompact_cube (d : ℕ) : IsCompact (cube d) := isCompact_Icc

theorem isClosed_cube (d : ℕ) : IsClosed (cube d) := isClosed_Icc

theorem profile_zero_outside {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (l : Lane) {x : Point d}
    (hx : x ∉ cube d) : profile ell R slot m l x = 0 := by
  have hex : ∃ i : Fin d,x i < -2 ∨ 2 < x i := by
    by_contra h
    apply hx
    simp only [cube,Set.mem_Icc,Pi.le_def]
    push_neg at h
    exact ⟨fun i => (h i).1,fun i => (h i).2⟩
  obtain ⟨i,hi⟩ := hex
  have hw : window x = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hi with hi | hi
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith),zero_mul]
    · rw [Real.smoothTransition.one_of_one_le (by linarith),sub_self,mul_zero]
  rw [profile,hw,zero_mul]

private theorem continuous_shift {d : ℕ} (x : Point d) (i : Fin d) :
    Continuous (shift x i) := by
  apply continuous_pi
  intro k
  by_cases h : k=i <;> simp only [shift,h,if_true,if_false] <;> fun_prop

/-- Derivatives of the zero germ are zero. This does not discard boundary
points: it is applied only to the OPEN complement of the closed support. -/
theorem coordinateDeriv_zero_on_open {d : ℕ} {U : Set (Point d)} (hU : IsOpen U)
    {f : Point d → ℝ} (hf : ∀ x ∈ U,f x=0) (i : Fin d) {x : Point d} (hx : x ∈ U) :
    coordinateDeriv i f x=0 := by
  have hmem : shift x i 0 ∈ U := by simpa using hx
  have he : (fun t : ℝ => f (shift x i t)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [((continuous_shift x i).tendsto 0).eventually (hU.mem_nhds hmem)] with t ht
    exact hf _ ht
  simpa only [coordinateDeriv,deriv_const] using he.deriv_eq

theorem mixed_zero_on_open {d : ℕ} {U : Set (Point d)} (hU : IsOpen U)
    {f : Point d → ℝ} (hf : ∀ x ∈ U,f x=0) (is : List (Fin d)) :
    ∀ x ∈ U,mixed is f x=0 := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact fun x hx => coordinateDeriv_zero_on_open hU ih i hx

theorem mixed_profile_zero_outside {d : ℕ} (is : List (Fin d)) (ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2)) (m : ℕ) (l : Lane) :
    ∀ x ∉ cube d,mixed is (profile ell R slot m l) x=0 :=
  mixed_zero_on_open (isClosed_cube d).isOpen_compl
    (fun x hx => profile_zero_outside ell R slot m l hx) is

theorem mixed_profile_integrable {d : ℕ} (is : List (Fin d)) (ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2)) (m : ℕ) (l : Lane) :
    Integrable (mixed is (profile ell R slot m l)) := by
  have hs : Function.support (mixed is (profile ell R slot m l)) ⊆ cube d := by
    intro x hx
    by_contra hn
    exact hx (mixed_profile_zero_outside is ell R slot m l x hn)
  have hc : HasCompactSupport (mixed is (profile ell R slot m l)) := by
    exact (isCompact_cube d).of_isClosed_subset isClosed_closure
      (closure_minimal hs (isClosed_cube d))
  exact (continuous_mixed_profile is ell R slot m l).integrable_of_hasCompactSupport hc

def cubeVolume (d : ℕ) : ℝ := (volume (cube d)).toReal

theorem exists_profile_mixed_L1_bound (d q : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ m : ℕ,∀ l : Lane,∀ v : Fin q → Fin d,
        (∫ x, |mixed (List.ofFn v) (profile ell R slot m l) x|) ≤ C*(m+1 : ℝ)^q := by
  obtain ⟨C,hC,hbound⟩ := exists_profile_mixed_bound d q
  have hV : 0 ≤ cubeVolume d := ENNReal.toReal_nonneg
  refine ⟨(cubeVolume d+1)*C,by nlinarith,?_⟩
  intro ell hell R slot m l v
  let f := mixed (List.ofFn v) (profile ell R slot m l)
  have hf := continuous_mixed_profile (List.ofFn v) ell R slot m l
  have heq : (fun x => |f x|) = (cube d).indicator (fun x => |f x|) := by
    funext x
    by_cases hx : x ∈ cube d
    · simp only [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,mixed_profile_zero_outside (List.ofFn v) ell R slot m l x hx]
      exact abs_zero
  have hconst : IntegrableOn (fun _ : Point d => C*(m+1 : ℝ)^q) (cube d) :=
    ContinuousOn.integrableOn_compact (isCompact_cube d) continuous_const.continuousOn
  have hi : (∫ x in cube d,|f x|) ≤ (∫ _x : Point d in cube d,C*(m+1 : ℝ)^q) :=
    integral_mono (ContinuousOn.integrableOn_compact (isCompact_cube d) hf.abs.continuousOn)
      hconst (fun x => hbound ell hell R slot m l v x)
  calc
    _ = ∫ x in cube d,|f x| := by rw [heq,integral_indicator (isClosed_cube d).measurableSet]
    _ ≤ _ := hi
    _ = cubeVolume d*(C*(m+1 : ℝ)^q) := by simp [cubeVolume]
    _ ≤ _ := by
      have hp : 0 ≤ C*(m+1 : ℝ)^q := by positivity
      nlinarith

/-- Twice each chosen coordinate, in the actual finite order. -/
def twice {d : ℕ} : List (Fin d) → List (Fin d)
  | [] => []
  | i::is => i::i::twice is

theorem twice_length {d : ℕ} (is : List (Fin d)) : (twice is).length = 2*is.length := by
  induction is with
  | nil => simp [twice]
  | cons i is ih => simp only [twice,List.length_cons,ih]; omega

def doubled {d : ℕ} (S : Finset (Fin d)) : List (Fin d) := twice S.toList

theorem doubled_length_le {d : ℕ} (S : Finset (Fin d)) : (doubled S).length ≤ 2*d := by
  rw [doubled,twice_length,Finset.length_toList]
  have hs : S.card ≤ d := by simpa using Finset.card_le_univ S
  omega

/-- Exactly the finite sum of mixed-derivative L1 norms used as D in (F).
No Fourier transform is DEFINED to equal this majorant. -/
def atlasD {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (l : Lane) : ℝ :=
  ∑ S : Finset (Fin d),∫ x,|mixed (doubled S) (profile ell R slot m l) x|

theorem exists_atlasD_budget (d : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ m : ℕ,∀ l : Lane,
        atlasD ell R slot m l ≤ C*(m+1 : ℝ)^(2*d) := by
  have h : ∀ S : Finset (Fin d),∃ C : ℝ,1 ≤ C ∧
      ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ m : ℕ,∀ l : Lane,
        (∫ x,|mixed (doubled S) (profile ell R slot m l) x|) ≤ C*(m+1 : ℝ)^(doubled S).length := by
    intro S
    obtain ⟨C,hC,hc⟩ := exists_profile_mixed_L1_bound d (doubled S).length
    refine ⟨C,hC,?_⟩
    intro ell hell R slot m l
    have hv : List.ofFn (fun i : Fin (doubled S).length => (doubled S)[i]) = doubled S := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp
    simpa only [hv] using hc ell hell R slot m l
      (fun i : Fin (doubled S).length => (doubled S)[i])
  choose c hc hb using h
  let C := 1+∑ S : Finset (Fin d),c S
  have hc0 (S : Finset (Fin d)) : 0 ≤ c S := zero_le_one.trans (hc S)
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    have hsum : 0 ≤ ∑ S : Finset (Fin d),c S := Finset.sum_nonneg (fun S _ => hc0 S)
    linarith
  intro ell hell R slot m l
  have hm : (1 : ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg m]
  calc
    _ ≤ ∑ S : Finset (Fin d),c S*(m+1 : ℝ)^(doubled S).length :=
      Finset.sum_le_sum (fun S hS => hb S ell hell R slot m l)
    _ ≤ ∑ S : Finset (Fin d),c S*(m+1 : ℝ)^(2*d) :=
      Finset.sum_le_sum (fun S hS => mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hm (doubled_length_le S)) (hc0 S))
    _ = (∑ S : Finset (Fin d),c S)*(m+1 : ℝ)^(2*d) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)

/-- Explicit logarithmic degree for this ATLAS multiplier. Width is a
primitive parameter; no claim of an arithmetic wall estimate at m(N) follows. -/
theorem exists_atlasD_polylog (d B : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ N : ℕ,1 ≤ Real.log (N : ℝ) → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ m : ℕ,
      (m+1 : ℝ) ≤ (Real.log (N : ℝ))^B → ∀ l : Lane,
        atlasD (Real.log (N : ℝ)) R slot m l ≤ C*(Real.log (N : ℝ))^(B*(2*d)) := by
  obtain ⟨C,hC,hc⟩ := exists_atlasD_budget d
  refine ⟨C,hC,?_⟩
  intro N hN R slot m hm l
  apply (hc _ hN R slot m l).trans
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤m+1) hm (2*d)
  simpa only [pow_mul] using mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hC)

end
end ImbalancedChen.P3U5ChartMixedL1Budget
