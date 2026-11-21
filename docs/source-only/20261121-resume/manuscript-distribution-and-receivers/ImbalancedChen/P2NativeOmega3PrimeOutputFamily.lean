import MathlibNt.Wu2008DoubleSieve.Omega3Relative
import ImbalancedChen.P5zPositiveFamilyBudget
import ImbalancedChen.ActualUpperCountingInputs

/-!
SOURCE ONLY / UNCOMPILED / ZERO ENDPOINT CREDIT.

The independent source is the existing strengthened Omega3 multiset, before
any test on the additive output. Its PRIME-output restriction, not its larger
sifted-output restriction, receives the original Omega3 count after the
already paid bad-d and exceptional-output losses.

The final theorem uses the literal attachedUpperCoefficient in the main
term, exact coprime correction, and signed PP error. Those errors and its
density are not estimated here. No U99, endpoint, geometric-admissibility,
or positive-K conclusion is a hypothesis.
-/
namespace ImbalancedChen.P2NativeOmega3PrimeOutputFamily

noncomputable section
open Finset Real Wu2008DoubleSieve
open scoped Classical BigOperators

abbrev Label := Omega3Index

def labels {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) : Finset Label :=
  omega3SwitchedLabels N δ s t W

def sourceProduct (a : Label) : ℕ := omega3IndexCofactor a * a.2.1

def weight {i : ℕ} (W : Fin i → Finset ℕ) (a : Label) : ℝ :=
  (convolutionCoeff W a.1 : ℝ)

def primeMass {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  p5z_labelledPrimeMass (labels N δ s t W) sourceProduct (weight W) N

theorem weight_nonneg {i : ℕ} (W : Fin i → Finset ℕ) (a : Label) :
    0 ≤ weight W a := Nat.cast_nonneg _

theorem source_product_le {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : Label} (ha : a ∈ labels N δ s t W) : sourceProduct a ≤ N := by
  exact (omega3_switched_label_size ha).2.1

/-- The same unsifted fibre as the native source, retaining output primality. -/
def primeFibre (N d p1 p2 p3 : ℕ) : Finset ℕ :=
  (omega3SwitchedFibre N d p1 p2 p3).filter
    (fun n => Nat.Prime (N - omega3Cofactor d p1 p2 n * p3))

theorem primeMass_eq_fibre_sum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) :
    primeMass N δ s t W =
      omega3LabelSum N δ s t W (fun d p1 p2 p3 =>
        ((primeFibre N d p1 p2 p3).card : ℝ)) := by
  have hf := omega3_switched_labels_sum N δ s t W
    (fun a => if Nat.Prime (omega3IndexOutput N a) then (1 : ℝ) else 0)
  have htest :
      primeMass N δ s t W =
        ∑ a ∈ labels N δ s t W, weight W a *
          (if Nat.Prime (omega3IndexOutput N a) then (1 : ℝ) else 0) := by
    unfold primeMass p5z_labelledPrimeMass
    apply sum_congr rfl
    intro a ha
    have hcap := source_product_le ha
    change (if sourceProduct a < N ∧ Nat.Prime (N-sourceProduct a)
      then weight W a else 0) =
      weight W a * (if Nat.Prime (N-sourceProduct a) then 1 else 0)
    by_cases hp : Nat.Prime (N-sourceProduct a)
    · have hlt : sourceProduct a < N := by have := hp.pos; omega
      simp only [if_pos hp, if_pos ⟨hlt,hp⟩, mul_one]
    · simp only [if_neg hp, if_neg (fun h => hp h.2), mul_zero]
  rw [htest]
  simpa only [labels,weight,primeFibre,omega3LabelSum,omega3IndexOutput,
    omega3IndexCofactor,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,
    Nat.cast_zero] using hf

/-- Refines the existing good-fibre injection by keeping its prime output.
This does not reconstruct the original label identity. -/
theorem good_original_prime_injects {N d p1 p2 p3 : ℕ} {Z : ℝ}
    (hN : 4 ≤ N) (heven : Even N) (hd : 0 < d)
    (h1 : p1.Prime) (h1N : p1.Coprime N) (h2N : p2.Coprime N) :
    (omega3GoodOriginalFibre N d p1 p2 p3 Z).card ≤
      (primeFibre N d p1 p2 p3).card := by
  apply card_le_card_of_injOn (omega3Quotient N d p1 p2 p3)
  · intro ell hell
    obtain ⟨hsrc,hgoodd,hgoodN,_hlarge⟩ := mem_filter.mp hell
    obtain ⟨hb,hp,hdiv,hs⟩ := mem_filter.mp hsrc
    have hle : ell ≤ N := by simpa using mem_range.mp hb
    have hlt := omega3_prime_output_lt hN heven hp hle
    obtain ⟨hn,_heq,hout,hsize⟩ := omega3_quotient_equation hlt hdiv
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨?_,hn,hsize,?_⟩,?_⟩
    · exact (mem_filter.mp (omega3_quotient_mem hN heven hsrc)).1
    · exact omega3_strengthened_of_source hd h1 h1N h2N hp hle hdiv hs hgoodd hgoodN
    · rw [←hout]
      exact hp
  · intro a ha b hb hab
    have ha' := mem_filter.mp (mem_filter.mp ha).1
    have hb' := mem_filter.mp (mem_filter.mp hb).1
    have hla := omega3_prime_output_lt hN heven ha'.2.1
      (by simpa using mem_range.mp ha'.1)
    have hlb := omega3_prime_output_lt hN heven hb'.2.1
      (by simpa using mem_range.mp hb'.1)
    rw [(omega3_quotient_equation hla ha'.2.2.1).2.2.1,
      (omega3_quotient_equation hlb hb'.2.2.1).2.2.1,hab]

/-- The original source cover, with the PRIME-output independent source
instead of the strictly larger switched-sifted source. -/
theorem original_fibre_le_prime_add_errors {N d p1 p2 p3 : ℕ} {δ : ℝ}
    (hN : 4 ≤ N) (heven : Even N) (hd : 0 < d)
    (h1 : p1.Prime) (h1N : p1.Coprime N) (h2N : p2.Coprime N) :
    (sourceSieveCarrier N (d*p1*p2*p3) (d*p1*N) (p2:ℝ)).card ≤
      (primeFibre N d p1 p2 p3).card +
      (omega3BadDFibre N d p1 p2 p3).card +
      (omega3ExceptionalOutputFibre N d p1 p2 p3 δ).card := by
  let Z := sqrt ((N:ℝ)^(1/2-δ))
  have hcover :
      sourceSieveCarrier N (d*p1*p2*p3) (d*p1*N) (p2:ℝ) ⊆
        (omega3GoodOriginalFibre N d p1 p2 p3 Z ∪ omega3BadDFibre N d p1 p2 p3) ∪
          omega3ExceptionalOutputFibre N d p1 p2 p3 δ := by
    intro ell hell
    by_cases hd' : Omega3BadD N d ell
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hell,hd'⟩))
    by_cases he : ell ∈ omega3ExceptionalOutputs N δ
    · exact mem_union_right _ (mem_filter.mpr ⟨hell,he⟩)
    have hp := (mem_filter.mp hell).2.1
    have hdiv : ¬ell ∣ N := fun h =>
      he (mem_omega3ExceptionalOutputs (by omega) hp (Or.inr h))
    have hlarge : Z ≤ (ell:ℝ) := by
      by_contra hl
      exact he (mem_omega3ExceptionalOutputs (by omega) hp (Or.inl (lt_of_not_ge hl)))
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hell,hd',hdiv,hlarge⟩))
  have hc := card_le_card hcover
  have h01 := card_union_le (omega3GoodOriginalFibre N d p1 p2 p3 Z)
    (omega3BadDFibre N d p1 p2 p3)
  have h012 := card_union_le
    (omega3GoodOriginalFibre N d p1 p2 p3 Z ∪ omega3BadDFibre N d p1 p2 p3)
    (omega3ExceptionalOutputFibre N d p1 p2 p3 δ)
  have hg := good_original_prime_injects (p3:=p3) (Z:=Z) hN heven hd h1 h1N h2N
  omega

theorem original_le_primeFamily_add_errors {i N : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} (hN : 4 ≤ N) (heven : Even N)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    wuOmega3Sum N δ s t W ≤ primeMass N δ s t W +
      omega3BadDCount N δ s t W + omega3ExceptionalOutputCount N δ s t W := by
  rw [wuOmega3Sum_eq_original_label_count,primeMass_eq_fibre_sum]
  unfold omega3BadDCount omega3ExceptionalOutputCount
  rw [←omega3LabelSum_add,←omega3LabelSum_add]
  apply omega3LabelSum_mono
  intro d hd' p3 _ p2 h2 p1 h1
  exact_mod_cast original_fibre_le_prime_add_errors (p3:=p3) (δ:=δ)
    hN heven (hd d hd') (mem_primeWindow.mp h1).1
    (mem_primeWindow.mp h1).2.1 (mem_primeWindow.mp h2).2.1

/-- The single threshold precedes i, Delta and V; k is arbitrary and fixed. -/
theorem uniform_original_le_primeFamily (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        wuOmega3Sum N δ s t (convolutionWuWindows N Δ V) ≤
          primeMass N δ s t (convolutionWuWindows N Δ V) +
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hhalf : δ < 1/2 := by linarith
  obtain ⟨T1,hT14,hT1⟩ := omega3_badD_relative k hδ hhalf (half_pos hε)
  obtain ⟨T2,_hT24,hT2⟩ := omega3_exceptional_relative k hδ hhalf (half_pos hε)
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have h4 := hT14.trans hN1
  have hbad := hT1 N hN1 he i Δ V hb s t hs hst ht
  have hex := hT2 N hN2 he i Δ V hb s t hs hst ht
  have hfinite := original_le_primeFamily_add_errors (δ:=δ) (s:=s) (t:=t)
    (W:=convolutionWuWindows N Δ V) h4 he
    (fun d hd => (omega3_source_support_le_Q (by omega) hδ hhalf hb hd).1)
  linarith

/-- A concrete finite instance of the existing positive-family comparison.
The actual physical rho is shared by density, coprime and distribution terms.
No estimate for those three objects is assumed or concluded. -/
theorem uniform_actual_rho_finite_comparison (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ (nu r e : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      0 < nu → 0 < e → e ≤ 1 → e^2 ≤ r →
      (N:ℝ)^(nu*r) ≤ (cap N:ℝ) →
        let W := convolutionWuWindows N Δ V
        let S := labels N δ s t W
        let D := attachedUpperModuli nu r e retain cap N
        let rho := attachedUpperCoefficient nu r e retain cap N
        let z := Nat.ceil ((N:ℝ)^(nu*r))
        wuOmega3Sum N δ s t W ≤
          p5z_labelledMass S (weight W)*physicalDensitySum D rho +
          p5z_labelledCoprimeCorrection S sourceProduct (weight W) D rho +
          p5z_labelledDistributionError S sourceProduct (weight W) N D rho +
          p5z_labelledSmallPrimeMass S sourceProduct (weight W) N z +
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) W := by
  obtain ⟨T,hT4,hT⟩ := uniform_original_le_primeFamily k hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN he i Δ V hb s t hs hst ht nu r e retain cap hnu he' he1 heR hcap
  dsimp only
  have hsource := hT N hN he i Δ V hb s t hs hst ht
  have hfinite := p5z_labelledPrimeMass_le_main_add_errors
    (labels N δ s t (convolutionWuWindows N Δ V)) sourceProduct
    (weight (convolutionWuWindows N Δ V)) N (Nat.ceil ((N:ℝ)^(nu*r)))
    (attachedUpperModuli nu r e retain cap N)
    (attachedUpperCoefficient nu r e retain cap N)
    (fun a _ => weight_nonneg _ a) (fun _ ha => source_product_le ha)
    (attachedUpperCoefficient_majorant hnu he' he1 heR retain cap
      (by have := hT4.trans hN; omega) hcap)
  change primeMass N δ s t (convolutionWuWindows N Δ V) ≤ _ at hfinite
  linarith

end
end ImbalancedChen.P2NativeOmega3PrimeOutputFamily
