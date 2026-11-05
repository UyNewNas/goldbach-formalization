import ImbalancedChen.P3U5OriginalWComposition

/-!
P3.6 manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Actual compactly supported mixed-L1 D ledger for ORIGINAL W multiplied by
the real physical HB chart extension. Primitive W requirements are its OWN
smooth derivative consistency and polylog-sized coordinate partials.

No Fourier, arithmetic discrepancy, root-fibre estimate, or PP conclusion
is made or assumed by the bounds below.
-/
namespace ImbalancedChen.P3U5OriginalWMixedL1
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter Set
open P3AffineTransitionJets P3FiniteMixedLeibniz
open P3U5RootAtlas P3U5HBLogChart
open P3U5HBLogMixedL1 P3U5ChartMixedL1Budget
open P3U5OriginalWComposition

/-- Continuity follows from the exact finite Leibniz sum and continuity
of the primitive ordinary partials of W and the existing HB profile. -/
theorem continuous_mixed_withOriginalW {d g : ℕ} (W : Point d → ℝ)
    (hW : WDerivCompatible W)
    (hWcont : ∀ is : List (Fin d),Continuous (mixed is W))
    (is : List (Fin d)) (a : ℝ) (ha : 0 < a) (ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2))
    (group : Fin d → Fin g) (b : Fin g → ℝ) (trim : ℝ)
    (u : Fin d → ℝ) (v : Fin g → ℝ) (pick : Fin g → Fin d)
    (m : ℕ) (l : Lane) :
    Continuous (mixed is
      (withOriginalW W a ell R slot group b trim u v pick m l)) := by
  let H := hbProfile a ell R slot group b trim u v pick m l
  have hH : Compatible (fun js => mixed js H) :=
    hb_compatible a ha ell R slot group b trim u v pick m l
  have hHcont (js : List (Fin d)) : Continuous (mixed js H) :=
    continuous_mixed_hbProfile js a ha ell R slot group b trim u v pick m l
  change Continuous (mixed is (fun x => W x*H x))
  rw [mixed_product_eq (fun js => mixed js W) (fun js => mixed js H) hW hH is]
  change Continuous (fun x => ((splits is).map
    (fun p => mixed p.1 W x*mixed p.2 H x)).sum)
  have aux (ps : List (List (Fin d) × List (Fin d))) :
      Continuous (fun x : Point d =>
        (ps.map (fun p => mixed p.1 W x*mixed p.2 H x)).sum) := by
    induction ps with
    | nil => simpa using (continuous_const : Continuous (fun _ : Point d => (0 : ℝ)))
    | cons p ps ih =>
        simpa only [List.map_cons,List.sum_cons] using
          ((hWcont p.1).mul (hHcont p.2)).add ih
  exact aux (splits is)

/-- Derivatives of the zero germ vanish on the open complement of the
same fixed cube; W itself needs no compact support assumption. -/
theorem mixed_withOriginalW_zero_outside {d g : ℕ}
    (is : List (Fin d)) (W : Point d → ℝ) (a ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2))
    (group : Fin d → Fin g) (b : Fin g → ℝ) (trim : ℝ)
    (u : Fin d → ℝ) (v : Fin g → ℝ) (pick : Fin g → Fin d)
    (m : ℕ) (l : Lane) :
    ∀ x ∉ cube d,
      mixed is (withOriginalW W a ell R slot group b trim u v pick m l) x=0 :=
  mixed_zero_on_open (isClosed_cube d).isOpen_compl
    (fun x hx => withOriginalW_zero_outside W a ell R slot group b trim
      u v pick m l hx) is

theorem integrable_mixed_withOriginalW {d g : ℕ} (is : List (Fin d))
    (W : Point d → ℝ) (hW : WDerivCompatible W)
    (hWcont : ∀ js : List (Fin d),Continuous (mixed js W))
    (a : ℝ) (ha : 0 < a) (ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2))
    (group : Fin d → Fin g) (b : Fin g → ℝ) (trim : ℝ)
    (u : Fin d → ℝ) (v : Fin g → ℝ) (pick : Fin g → Fin d)
    (m : ℕ) (l : Lane) :
    Integrable (mixed is (withOriginalW W a ell R slot group b trim u v pick m l)) := by
  have hs : Function.support
      (mixed is (withOriginalW W a ell R slot group b trim u v pick m l)) ⊆
        cube d := by
    intro x hx
    by_contra hn
    exact hx (mixed_withOriginalW_zero_outside is W a ell R slot group b trim
      u v pick m l x hn)
  have hc : HasCompactSupport
      (mixed is (withOriginalW W a ell R slot group b trim u v pick m l)) :=
    (isCompact_cube d).of_isClosed_subset isClosed_closure
      (closure_minimal hs (isClosed_cube d))
  exact (continuous_mixed_withOriginalW W hW hWcont is a ha ell R slot group
    b trim u v pick m l).integrable_of_hasCompactSupport hc

/-- Genuine integral bound derived from fixed support and a pointwise bound
for the ALREADY PROVED mixed derivative, not an L1 budget postulated for it. -/
theorem exists_withOriginalW_mixed_L1_bound (d g q : ℕ)
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d,∀ m : ℕ,∀ l : Lane,
      ∀ W : Point d → ℝ,WDerivCompatible W →
      (∀ js : List (Fin d),Continuous (mixed js W)) →
      ∀ M : ℝ,0 ≤ M →
      (∀ js : List (Fin d),js.length ≤ q → ∀ x,|mixed js W x| ≤ M) →
      ∀ is : Fin q → Fin d,
      (∫ x,|mixed (List.ofFn is)
        (withOriginalW W a ell R slot group b trim u v pick m l) x|) ≤
        C*M*(m+1 : ℝ)^q := by
  obtain ⟨C,hC,hb⟩ := exists_withOriginalW_mixed_bound d g q a ha
  have hV : 0 ≤ cubeVolume d := ENNReal.toReal_nonneg
  refine ⟨(cubeVolume d+1)*C,by nlinarith,?_⟩
  intro ell hell R slot group b trim u v pick m l W hW hWcont M hM hWb is
  let H := withOriginalW W a ell R slot group b trim u v pick m l
  let f := mixed (List.ofFn is) H
  have hf : Continuous f :=
    continuous_mixed_withOriginalW W hW hWcont (List.ofFn is) a ha ell R
      slot group b trim u v pick m l
  have heq : (fun x => |f x|)=(cube d).indicator (fun x => |f x|) := by
    funext x
    by_cases hx : x ∈ cube d
    · simp only [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        mixed_withOriginalW_zero_outside (List.ofFn is) W a ell R slot group
          b trim u v pick m l x hx]
      exact abs_zero
  have hp : 0 ≤ C*M*(m+1 : ℝ)^q := by positivity
  have hi : (∫ x in cube d,|f x|) ≤
      ∫ _x : Point d in cube d,C*M*(m+1 : ℝ)^q :=
    integral_mono (ContinuousOn.integrableOn_compact (isCompact_cube d)
        hf.abs.continuousOn)
      (ContinuousOn.integrableOn_compact (isCompact_cube d)
        continuous_const.continuousOn)
      (fun x => hb ell hell R slot group b trim u v pick m l W hW
        M hM hWb is x)
  calc
    _ = ∫ x in cube d,|f x| := by
      rw [heq,integral_indicator (isClosed_cube d).measurableSet]
    _ ≤ _ := hi
    _ = cubeVolume d*(C*M*(m+1 : ℝ)^q) := by simp [cubeVolume]
    _ ≤ ((cubeVolume d+1)*C)*M*(m+1 : ℝ)^q := by nlinarith

/-- The same actual D ledger as the manuscript's equation (F). -/
def originalWD {d g : ℕ} (W : Point d → ℝ) (a ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2))
    (group : Fin d → Fin g) (b : Fin g → ℝ) (trim : ℝ)
    (u : Fin d → ℝ) (v : Fin g → ℝ) (pick : Fin g → Fin d)
    (m : ℕ) (l : Lane) : ℝ :=
  ∑ S : Finset (Fin d),∫ x,
    |mixed (doubled S) (withOriginalW W a ell R slot group b trim u v pick m l) x|

/-- Only primitive W derivative supremums up to 2d are assumed. The
combined L1 norm is DERIVED and has no extra 2d-factor exponent. -/
theorem exists_originalWD_budget (d g : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d,∀ m : ℕ,∀ l : Lane,
      ∀ W : Point d → ℝ,WDerivCompatible W →
      (∀ js : List (Fin d),Continuous (mixed js W)) →
      ∀ M : ℝ,0 ≤ M →
      (∀ js : List (Fin d),js.length ≤ 2*d → ∀ x,|mixed js W x| ≤ M) →
      originalWD W a ell R slot group b trim u v pick m l ≤
        C*M*(m+1 : ℝ)^(2*d) := by
  have hh := fun S : Finset (Fin d) =>
    exists_withOriginalW_mixed_L1_bound d g (doubled S).length a ha
  choose c hc hb using hh
  let C := 1+∑ S : Finset (Fin d),c S
  have hc0 (S : Finset (Fin d)) : 0 ≤ c S := zero_le_one.trans (hc S)
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    have hs := Finset.sum_nonneg (s:=Finset.univ) (fun S _ => hc0 S)
    linarith
  intro ell hell R slot group b trim u v pick m l W hW hWcont M hM hWb
  have hm : (1 : ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg m]
  have ht (S : Finset (Fin d)) :
      (∫ x,|mixed (doubled S)
        (withOriginalW W a ell R slot group b trim u v pick m l) x|) ≤
        c S*M*(m+1 : ℝ)^(2*d) := by
    have hv : List.ofFn (fun i : Fin (doubled S).length => (doubled S)[i]) =
        doubled S := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'; simp
    have h := hb S ell hell R slot group b trim u v pick m l W hW hWcont
      M hM (fun js hjs x => hWb js (hjs.trans (doubled_length_le S)) x)
      (fun i : Fin (doubled S).length => (doubled S)[i])
    rw [hv] at h
    have hp : (m+1 : ℝ)^(doubled S).length ≤ (m+1 : ℝ)^(2*d) :=
      pow_le_pow_right₀ hm (doubled_length_le S)
    exact h.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg (hc0 S) hM))
  calc
    _ ≤ ∑ S : Finset (Fin d),c S*M*(m+1 : ℝ)^(2*d) :=
      Finset.sum_le_sum (fun S _ => ht S)
    _ = (∑ S : Finset (Fin d),c S)*(M*(m+1 : ℝ)^(2*d)) := by
      simp_rw [mul_assoc]
      rw [← Finset.sum_mul]
    _ ≤ C*(M*(m+1 : ℝ)^(2*d)) :=
      mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
    _ = C*M*(m+1 : ℝ)^(2*d) := by ring

/-- If the ORIGINAL W family has a fixed polylog derivative class with
constant A and degree E, the previous combined D costs exactly E+2dB. -/
theorem exists_originalWD_polylog (d g B E : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ N : ℕ,1 ≤ Real.log (N : ℝ) →
      ∀ R : Fin 2 → ℝ,∀ slot : Fin d → Option (Fin 2),
      ∀ group : Fin d → Fin g,∀ b : Fin g → ℝ,∀ trim : ℝ,
      ∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,∀ pick : Fin g → Fin d,
      ∀ m : ℕ,(m+1 : ℝ) ≤ (Real.log (N : ℝ))^B → ∀ l : Lane,
      ∀ W : Point d → ℝ,WDerivCompatible W →
      (∀ js : List (Fin d),Continuous (mixed js W)) →
      ∀ A : ℝ,0 ≤ A →
      (∀ js : List (Fin d),js.length ≤ 2*d → ∀ x,
        |mixed js W x| ≤ A*(Real.log (N : ℝ))^E) →
      originalWD W a (Real.log (N : ℝ)) R slot group b trim u v pick m l ≤
        C*A*(Real.log (N : ℝ))^(E+B*(2*d)) := by
  obtain ⟨C,hC,hb⟩ := exists_originalWD_budget d g a ha
  refine ⟨C,hC,?_⟩
  intro N hN R slot group b trim u v pick m hm l W hW hWcont A hA hWb
  have hM : 0 ≤ A*(Real.log (N : ℝ))^E := by positivity
  have h := hb (Real.log (N : ℝ)) hN R slot group b trim u v pick m l W
    hW hWcont (A*(Real.log (N : ℝ))^E) hM hWb
  have hp : (m+1 : ℝ)^(2*d) ≤ (Real.log (N : ℝ))^(B*(2*d)) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m+1) hm (2*d)
    simpa only [pow_mul] using hh
  calc
    _ ≤ C*(A*(Real.log (N : ℝ))^E)*(m+1 : ℝ)^(2*d) := h
    _ ≤ C*(A*(Real.log (N : ℝ))^E)*
        (Real.log (N : ℝ))^(B*(2*d)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C*A*(Real.log (N : ℝ))^(E+B*(2*d)) := by
      rw [pow_add]
      ring

end
end ImbalancedChen.P3U5OriginalWMixedL1
