import ImbalancedChen.P2NativeOmega3PrimeOutputFamily
import MathlibNt.Wu2008DoubleSieve.ConvolutionMultiplicity
import ImbalancedChen.PrimeHistoryLogCoordinates

/-!
SOURCE ONLY / UNCOMPILED.

The convolution coefficient is expanded by the existing exact fibre-sum
theorem. Thus each original ordered prefix tuple is kept, even when products
collide. The independent labels have unit weight and no additive-prime or
PP-modulus test. The strengthened native mask is retained, including p1
repetitions in the tail. The complete canonical word gives a rank bound
chosen from k,delta alone, before N,i,Delta,V.
-/
namespace ImbalancedChen.P2NativeOmega3ExpandedPrimeWords

noncomputable section
open Finset Real Wu2008DoubleSieve
open P2NativeOmega3PrimeOutputFamily
open scoped Classical BigOperators

abbrev TailLabel := Σ _p3 : ℕ, Σ _p2 : ℕ, Σ _p1 : ℕ, ℕ
abbrev ExpandedLabel (i : ℕ) := Σ _v : Fin i → ℕ, TailLabel

def tailLabels (N : ℕ) (δ s t : ℝ) (d : ℕ) : Finset TailLabel :=
  (primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)).sigma fun p3 =>
    (primeWindow N (wuLocalCutoff N δ d t) (p3:ℝ)).sigma fun p2 =>
      (primeWindow N (wuLocalCutoff N δ d t) (p2:ℝ)).sigma fun p1 =>
        omega3SwitchedFibre N d p1 p2 p3

def expandedLabels {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) :
    Finset (ExpandedLabel i) :=
  (Fintype.piFinset W).sigma fun v => tailLabels N δ s t (∏ j, v j)

def sourceIndex {i : ℕ} (a : ExpandedLabel i) : Label :=
  ⟨∏ j, a.1 j, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩

def expandedProduct {i : ℕ} (a : ExpandedLabel i) : ℕ := sourceProduct (sourceIndex a)

def primeWord {i : ℕ} (a : ExpandedLabel i) : List ℕ :=
  List.ofFn a.1 ++ [a.2.2.2.1,a.2.2.1,a.2.1] ++ a.2.2.2.2.primeFactorsList

theorem expanded_data {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (ha : a ∈ expandedLabels N δ s t W) :
    a.1 ∈ Fintype.piFinset W ∧ sourceIndex a ∈ labels N δ s t W := by
  obtain ⟨hv,htail⟩ := mem_sigma.mp ha
  refine ⟨hv,?_⟩
  exact mem_sigma.mpr ⟨mem_image_of_mem (fun v : Fin i → ℕ => ∏ j, v j) hv,htail⟩

/-- Exact expansion into original ordered prefix labels, for every test
function of the retained native label. There is no product-map injectivity. -/
theorem expanded_test {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ)
    (G : Label → ℝ) :
    (∑ a ∈ labels N δ s t W, weight W a * G a) =
      ∑ a ∈ expandedLabels N δ s t W, G (sourceIndex a) := by
  unfold labels weight
  rw [omega3_switched_labels_sum]
  unfold omega3LabelSum
  rw [boxConvolution_sum_fibres]
  simp only [expandedLabels,tailLabels,sum_sigma,sourceIndex]

theorem expanded_mass {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) :
    p5z_labelledMass (labels N δ s t W) (weight W) =
      p5z_labelledMass (expandedLabels N δ s t W) (fun _ => 1) := by
  simpa only [p5z_labelledMass,mul_one] using expanded_test N δ s t W (fun _ => 1)

theorem expanded_primeMass {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) :
    primeMass N δ s t W =
      p5z_labelledPrimeMass (expandedLabels N δ s t W) expandedProduct (fun _ => 1) N := by
  have h := expanded_test N δ s t W
    (fun a => if sourceProduct a < N ∧ Nat.Prime (N-sourceProduct a) then 1 else 0)
  simpa only [primeMass,p5z_labelledPrimeMass,expandedProduct,mul_ite,mul_one,mul_zero] using h

theorem expanded_distribution {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ)
    (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (labels N δ s t W) sourceProduct (weight W) N D rho =
      p5z_labelledDistributionError (expandedLabels N δ s t W) expandedProduct
        (fun _ => 1) N D rho := by
  unfold p5z_labelledDistributionError p5z_labelledCongruenceMass p5z_labelledCoprimeMass
  apply sum_congr rfl
  intro q hq
  have hc := expanded_test N δ s t W
    (fun a => if Nat.ModEq q (sourceProduct a) N then 1 else 0)
  have hp := expanded_test N δ s t W
    (fun a => if Nat.Coprime (sourceProduct a) q then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at hc hp
  change _ = rho q * (_ - _ / (Nat.totient q:ℝ))
  rw [hc,hp]
  rfl

theorem expanded_coprimeCorrection {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledCoprimeCorrection (labels N δ s t W) sourceProduct (weight W) D rho =
      p5z_labelledCoprimeCorrection (expandedLabels N δ s t W) expandedProduct
        (fun _ => 1) D rho := by
  unfold p5z_labelledCoprimeCorrection
  rw [expanded_mass]
  apply sum_congr rfl
  intro q hq
  have hp := expanded_test N δ s t W
    (fun a => if Nat.Coprime (sourceProduct a) q then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at hp
  unfold p5z_labelledCoprimeMass
  rw [hp]
  rfl

theorem word_product {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (ha : a ∈ expandedLabels N δ s t W) :
    (primeWord a).prod = expandedProduct a := by
  obtain ⟨hd,h3,h2,h1,hn⟩ := mem_omega3SwitchedLabels.mp (expanded_data ha).2
  have hn0 : 0 < a.2.2.2.2 := (mem_filter.mp hn).2.1
  simp only [primeWord,List.prod_append,List.prod_cons,List.prod_nil,mul_one,
    List.prod_ofFn,Nat.prod_primeFactorsList hn0.ne',
    expandedProduct,sourceProduct,sourceIndex,omega3IndexCofactor,omega3Cofactor]
  ring

theorem word_primes {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (hW : ∀ j p, p ∈ W j → p.Prime)
    (ha : a ∈ expandedLabels N δ s t W) :
    ∀ p ∈ primeWord a, p.Prime := by
  obtain ⟨hv,hsrc⟩ := expanded_data ha
  obtain ⟨hd,h3,h2,h1,hn⟩ := mem_omega3SwitchedLabels.mp hsrc
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
      exact hW j (a.1 j) (Fintype.mem_piFinset.mp hv j)
    · simp only [List.mem_cons,List.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact (mem_primeWindow.mp h1).1
      · exact (mem_primeWindow.mp h2).1
      · exact (mem_primeWindow.mp h3).1
  · exact Nat.prime_of_mem_primeFactorsList hp

/-- Native strengthening allows p1 repetitions. Every other tail prime is
at least p2. Both cases inherit the common physical cutoff. -/
theorem word_fixed_power {i N : ℕ} {δ s t eta : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (ha : a ∈ expandedLabels N δ s t W)
    (hW : ∀ j p, p ∈ W j → (N:ℝ)^eta ≤ (p:ℝ))
    (hcut : (N:ℝ)^eta ≤ wuLocalCutoff N δ (∏ j, a.1 j) t) :
    ∀ p ∈ primeWord a, (N:ℝ)^eta ≤ (p:ℝ) := by
  obtain ⟨hv,hsrc⟩ := expanded_data ha
  obtain ⟨hd,h3,h2,h1,hn⟩ := mem_omega3SwitchedLabels.mp hsrc
  have hg := (mem_filter.mp hn).2.2.2
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
      exact hW j (a.1 j) (Fintype.mem_piFinset.mp hv j)
    · simp only [List.mem_cons,List.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hcut.trans (mem_primeWindow.mp h1).2.2.1
      · exact hcut.trans (mem_primeWindow.mp h2).2.2.1
      · exact hcut.trans (mem_primeWindow.mp h3).2.2.1
  · by_cases he : p = a.2.2.2.1
    · subst p
      exact hcut.trans (mem_primeWindow.mp h1).2.2.1
    · have hlarge : (a.2.2.1:ℝ) ≤ p := by
        by_contra hsmall
        exact hg.2.2 p (Nat.prime_of_mem_primeFactorsList hp)
          (lt_of_not_ge hsmall) he (Nat.dvd_of_mem_primeFactorsList hp)
      exact hcut.trans ((mem_primeWindow.mp h2).2.2.1.trans hlarge)

private theorem list_power_le_product (v : List ℕ) (z : ℝ) (hz : 0 ≤ z)
    (hv : ∀ p ∈ v, z ≤ (p:ℝ)) : z^v.length ≤ (v.prod:ℝ) := by
  revert hv
  induction v with
  | nil => intro _; simp
  | cons p v ih =>
      intro hv
      rw [List.length_cons,pow_succ,List.prod_cons,Nat.cast_mul]
      calc
        z^v.length*z ≤ (v.prod:ℝ)*(p:ℝ) :=
          mul_le_mul (ih (fun q hq => hv q (List.mem_cons_of_mem _ hq)))
            (hv p (List.mem_cons_self _ _)) hz (Nat.cast_nonneg _)
        _ = _ := mul_comm _ _

theorem word_rank_bound {i N : ℕ} {δ s t eta : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (hN : 1 < N) (heta : 0 < eta)
    (ha : a ∈ expandedLabels N δ s t W)
    (hfloor : ∀ p ∈ primeWord a, (N:ℝ)^eta ≤ (p:ℝ)) :
    ((primeWord a).length:ℝ) ≤ 1/eta := by
  have hp := list_power_le_product (primeWord a) ((N:ℝ)^eta)
    (Real.rpow_nonneg (Nat.cast_nonneg N) eta) hfloor
  have hcap : ((primeWord a).prod:ℝ) ≤ N := by
    rw [word_product ha]
    exact_mod_cast source_product_le (expanded_data ha).2
  have hNr : (1:ℝ) < N := by exact_mod_cast hN
  have hpow : (N:ℝ)^(eta*((primeWord a).length:ℝ)) ≤ (N:ℝ)^1 := by
    rw [Real.rpow_mul (Nat.cast_nonneg N),Real.rpow_natCast,Real.rpow_one]
    exact hp.trans hcap
  have he := (Real.rpow_le_rpow_left_iff hNr).mp hpow
  apply (le_div_iff₀ heta).mpr
  nlinarith only [he]

/-- Arbitrary fixed k, not a hard-coded rank-200 family. One R and T cover
all later N, all i<=k, all shrinking Delta, all V and every label. -/
theorem uniform_complete_rank (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    ∃ R T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i Δ (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ a ∈ expandedLabels N δ s t (convolutionWuWindows N Δ V),
        (primeWord a).length ≤ R ∧
        (∀ p ∈ primeWord a, p.Prime ∧
          (N:ℝ)^(wuLocalExponent k δ/10) ≤ (p:ℝ)) := by
  let eta := wuLocalExponent k δ/10
  have hhalf : δ < 1/2 := by linarith
  have heta : 0 < eta := div_pos (wuLocalExponent_pos k hδ hhalf) (by norm_num)
  obtain ⟨R,hR⟩ := exists_nat_gt (1/eta)
  obtain ⟨T,hT4,hT⟩ := omega3_source_window_lower k hδ hhalf
  refine ⟨R,T,hT4,?_⟩
  intro N hN i Δ V hb s t hs hst ht a ha
  have h4 := hT4.trans hN
  have hsrc := (expanded_data ha).2
  have hd := (mem_omega3SwitchedLabels.mp hsrc).1
  have hgeom := wu_buchstab_prime_window_bounds (by omega) hδ hhalf hb hs hst ht hd
  have hfloor : ∀ p ∈ primeWord a, (N:ℝ)^eta ≤ (p:ℝ) :=
    word_fixed_power ha (fun j p hp => (hT N hN i Δ V hb j p hp).2.2) hgeom.2.2.2.1
  have hlen := (word_rank_bound (by omega) heta ha hfloor).trans hR.le
  refine ⟨by exact_mod_cast hlen,?_⟩
  intro p hp
  exact ⟨word_primes (fun j p hj => (mem_convolutionWuWindows.mp hj).1) ha p hp,
    hfloor p hp⟩

/-- The shrinking windows remain literal, with no fixed-box replacement. -/
theorem old_window_geometry {i N : ℕ} {δ s t Δ : ℝ} {V : Fin i → ℝ}
    {a : ExpandedLabel i}
    (ha : a ∈ expandedLabels N δ s t (convolutionWuWindows N Δ V)) :
    ∀ j, (a.1 j).Prime ∧ (a.1 j).Coprime N ∧
      V j/Δ ≤ (a.1 j:ℝ) ∧ (a.1 j:ℝ) < V j :=
  fun j => mem_convolutionWuWindows.mp (Fintype.mem_piFinset.mp (expanded_data ha).1 j)

theorem unit_tail_preserved {i : ℕ} (v : Fin i → ℕ) (p3 p2 p1 : ℕ) :
    primeWord (⟨v,p3,p2,p1,1⟩ : ExpandedLabel i) =
      List.ofFn v ++ [p1,p2,p3] := by simp [primeWord]

end
end ImbalancedChen.P2NativeOmega3ExpandedPrimeWords
