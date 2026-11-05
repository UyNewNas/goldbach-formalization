import ImbalancedChen.P3U5HBLogMixedL1

/-!
P3.6 manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

Exact multivariate finite Leibniz rule for the EXISTING ordinary coordinate
mixed derivatives. A repeated coordinate is a distinct derivative occurrence.
The two-choice list retains its multiplicity; no factorial or symmetrical
multi-index shortcut is assumed. The primitive input for an original geometric
W is its OWN coordinate differentiation/derivative budget, never a bound for
the desired W-times-HB product, Fourier transform, or PP discrepancy.
-/
namespace ImbalancedChen.P3FiniteMixedLeibniz
noncomputable section
open scoped Classical BigOperators Topology
open P3AffineTransitionJets

abbrev Jet (d : ℕ) := List (Fin d) → Point d → ℝ

/-- Genuine directional derivative consistency, with the existing shift. -/
def Compatible {d : ℕ} (J : Jet d) : Prop :=
  ∀ (is : List (Fin d)) (i : Fin d) (x : Point d),
    HasDerivAt (fun t : ℝ => J is (shift x i t)) (J (i::is) x) 0

/-- Two choices for EACH ordered differentiation, including repetitions. -/
def splits {d : ℕ} : List (Fin d) → List (List (Fin d) × List (Fin d))
  | [] => [([],[])]
  | i::is =>
      (splits is).map (fun p => (i::p.1,p.2)) ++
      (splits is).map (fun p => (p.1,i::p.2))

theorem splits_length {d : ℕ} (is : List (Fin d)) :
    (splits is).length = 2^is.length := by
  induction is with
  | nil => simp [splits]
  | cons i is ih =>
      simp only [splits,List.length_append,List.length_map,
        List.length_cons,ih,pow_succ]
      omega

theorem splits_total_length {d : ℕ} (is : List (Fin d))
    (p : List (Fin d) × List (Fin d)) (hp : p ∈ splits is) :
    p.1.length+p.2.length=is.length := by
  induction is generalizing p with
  | nil =>
      simp only [splits,List.mem_singleton] at hp
      rcases hp with rfl
      simp
  | cons i is ih =>
      simp only [splits,List.mem_append,List.mem_map] at hp
      rcases hp with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
      · simp only [List.length_cons]
        have h := ih u hu
        omega
      · simp only [List.length_cons]
        have h := ih u hu
        omega

/-- The exact 2^q-term Leibniz sum, not a majorant declared as a derivative. -/
def productJet {d : ℕ} (A B : Jet d) (is : List (Fin d)) (x : Point d) : ℝ :=
  ((splits is).map (fun p => A p.1 x*B p.2 x)).sum

private theorem sum_map_add {α : Type*} (xs : List α) (f g : α → ℝ) :
    (xs.map (fun a => f a+g a)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons,List.sum_cons,ih]
      ring

theorem productJet_cons {d : ℕ} (A B : Jet d) (i : Fin d)
    (is : List (Fin d)) (x : Point d) :
    productJet A B (i::is) x =
      ((splits is).map (fun p =>
        A (i::p.1) x*B p.2 x+A p.1 x*B (i::p.2) x)).sum := by
  simpa [productJet,splits,List.map_append,List.sum_append,
    List.map_map,Function.comp_def] using
      (sum_map_add (splits is)
        (fun p => A (i::p.1) x*B p.2 x)
        (fun p => A p.1 x*B (i::p.2) x)).symm

/-- Differentiate each summand. Real differentiation is used; no formal
symbolic jet is silently substituted for an actual derivative. -/
theorem productJet_hasDerivAt {d : ℕ} (A B : Jet d)
    (hA : Compatible A) (hB : Compatible B)
    (is : List (Fin d)) (i : Fin d) (x : Point d) :
    HasDerivAt (fun t : ℝ => productJet A B is (shift x i t))
      (productJet A B (i::is) x) 0 := by
  have aux : ∀ xs : List (List (Fin d) × List (Fin d)),
      HasDerivAt
        (fun t : ℝ =>
          (xs.map (fun p => A p.1 (shift x i t)*B p.2 (shift x i t))).sum)
        ((xs.map (fun p =>
          A (i::p.1) x*B p.2 x + A p.1 x*B (i::p.2) x)).sum) 0 := by
    intro xs
    induction xs with
    | nil =>
        simpa only [List.map_nil,List.sum_nil] using
          (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    | cons p ps ih =>
        have hd := (hA p.1 i x).mul (hB p.2 i x)
        simpa only [List.map_cons,List.sum_cons,shift_zero] using hd.add ih
  have h := aux (splits is)
  rw [productJet_cons]
  simpa only [productJet] using h

/-- Exact ordinary iterated coordinate product rule, for arbitrary geometric
factors whose primitive derivatives are legitimate (not assumed estimates of
the product). -/
theorem mixed_product_eq {d : ℕ} (A B : Jet d)
    (hA : Compatible A) (hB : Compatible B)
    (is : List (Fin d)) :
    mixed is (fun x => A [] x*B [] x) = productJet A B is := by
  induction is with
  | nil => funext x; simp [mixed,productJet,splits]
  | cons i is ih =>
      funext x
      simp only [mixed,ih,coordinateDeriv]
      exact (productJet_hasDerivAt A B hA hB is i x).deriv

/-- Elementary finite triangle bound, counting all 2^q assignments. -/
theorem productJet_bound {d : ℕ} (A B : Jet d)
    (is : List (Fin d)) (x : Point d) (U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hA : ∀ js,js.length ≤ is.length → |A js x| ≤ U)
    (hB : ∀ js,js.length ≤ is.length → |B js x| ≤ V) :
    |productJet A B is x| ≤ (2 : ℝ)^is.length*(U*V) := by
  have ht (p : List (Fin d) × List (Fin d)) (hp : p ∈ splits is) :
      |A p.1 x*B p.2 x| ≤ U*V := by
    have hl := splits_total_length is p hp
    rw [abs_mul]
    exact mul_le_mul (hA _ (by omega)) (hB _ (by omega))
      (abs_nonneg _) hU
  have aux : ∀ xs : List (List (Fin d) × List (Fin d)),
      (∀ p ∈ xs,|A p.1 x*B p.2 x| ≤ U*V) →
      |(xs.map (fun p => A p.1 x*B p.2 x)).sum| ≤
        (xs.length : ℝ)*(U*V) := by
    intro xs
    induction xs with
    | nil => intro _; simp
    | cons p ps ih =>
        intro h
        have hp : |A p.1 x*B p.2 x| ≤ U*V := h p (by simp)
        have hps : ∀ p ∈ ps,|A p.1 x*B p.2 x| ≤ U*V := by
          intro a ha
          exact h a (by simp [ha])
        simp only [List.map_cons,List.sum_cons,List.length_cons,
          Nat.cast_add,Nat.cast_one]
        calc
          _ ≤ |A p.1 x*B p.2 x|+
              |(ps.map (fun p => A p.1 x*B p.2 x)).sum| := (abs_add _ _)
          _ ≤ U*V+(ps.length : ℝ)*(U*V) := add_le_add hp (ih hps)
          _ = ((ps.length : ℝ)+1)*(U*V) := by ring
  have h := aux (splits is) ht
  simpa only [productJet,splits_length,Nat.cast_pow,Nat.cast_ofNat] using h

/-- The actual user-supplied smooth W class can be described by its OWN
derivatives; hW is not a bound for W times the HB multiplier. -/
theorem mixed_mul_bound {d : ℕ} (W H : Point d → ℝ)
    (hW : Compatible (fun js => mixed js W))
    (hH : Compatible (fun js => mixed js H))
    (is : List (Fin d)) (x : Point d) (U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hWbound : ∀ js,js.length ≤ is.length → |mixed js W x| ≤ U)
    (hHbound : ∀ js,js.length ≤ is.length → |mixed js H x| ≤ V) :
    |mixed is (fun y => W y*H y) x| ≤ (2 : ℝ)^is.length*(U*V) := by
  rw [mixed_product_eq _ _ hW hH]
  exact productJet_bound _ _ is x U V hU hV hWbound hHbound

end
end ImbalancedChen.P3FiniteMixedLeibniz
