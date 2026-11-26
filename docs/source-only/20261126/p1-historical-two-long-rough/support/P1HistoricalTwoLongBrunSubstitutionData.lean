import ImbalancedChen.Part3TwoLongBrunSupport
import ImbalancedChen.Part3TwoLongHBMellinBrunProfiles
import ImbalancedChen.PrimeProductsMellinExactMeanInsertion

/-! SOURCE ONLY / UNCOMPILED. Original declaration bytes are preserved;
see EXTRACTION_BINDING.json. No compilation or kernel credit is added. -/
namespace ImbalancedChen.Part3.TwoLongLiteralBrunSubstitution
noncomputable section
open Classical Set
open scoped BigOperators
open TwoLongActualLowerBrunMoment TwoLongHBMellinBrunProfiles
open TwoLongLiteralMellinModes TwoLongFixedMRectangularCore
open ImbalancedChen.OriginalOneLongLiteralBrunDictionary
open ImbalancedChen.Part3.RoughSlotCharacterLift20261026b (smallPrimes)
open ImbalancedChen.PrimeProducts

def divisorIndicator (d n : ℕ) : ℂ := if d ∣ n then 1 else 0

theorem brun_ratio {U : ℝ} (hU : 0 < U) {d : ℕ} (hd : 0 < d) (u : ℕ) :
    ((d*u : ℕ) : ℝ)/U = (u : ℝ)/(U/d) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp [hU.ne', hdR] <;> ring

/-- Actual divisor substitution on the full smooth cover. Zero values
at the extra ceil endpoints are removed by the proved profile support,
not by identifying two generally unequal integer windows. -/
theorem sum_divisor_substitution {U : ℝ} (hU : 0 < U) {d : ℕ} (hd : 0 < d)
    (f : ℝ → ℂ) (hf : Function.support f ⊆ Icc (1/2 : ℝ) (5/2)) (H : ℕ → ℂ) :
    (∑ n ∈ wideWindow U, f ((n : ℝ)/U) * divisorIndicator d n * H n) =
      ∑ u ∈ wideWindow (U/d), f ((u : ℝ)/(U/d)) * H (d*u) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let A := (wideWindow U).filter (fun n => d ∣ n ∧ f ((n : ℝ)/U) ≠ 0)
  let B := (wideWindow (U/d)).filter (fun u => f ((u : ℝ)/(U/d)) ≠ 0)
  have ha : (∑ n ∈ wideWindow U, f ((n : ℝ)/U) * divisorIndicator d n * H n) =
      ∑ n ∈ A, f ((n : ℝ)/U) * H n := by
    dsimp [A]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hdn : d ∣ n <;> by_cases hfn : f ((n : ℝ)/U) = 0 <;>
      simp [divisorIndicator, hdn, hfn]
  have hb : (∑ u ∈ wideWindow (U/d), f ((u : ℝ)/(U/d)) * H (d*u)) =
      ∑ u ∈ B, f ((u : ℝ)/(U/d)) * H (d*u) := by
    dsimp [B]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hfu : f ((u : ℝ)/(U/d)) = 0 <;> simp [hfu]
  rw [ha, hb]
  refine Finset.sum_bij (fun n _ => n/d) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnW, hdn, hfn⟩ := Finset.mem_filter.mp hn
    have he : d*(n/d) = n := Nat.mul_div_cancel' hdn
    have hr : (n : ℝ)/U = ((n/d : ℕ) : ℝ)/(U/d) := by
      simpa only [he] using brun_ratio hU hd (n/d)
    have hnon : f (((n/d : ℕ) : ℝ)/(U/d)) ≠ 0 := by rwa [← hr]
    exact Finset.mem_filter.mpr
      ⟨nonzero_mem_wideWindow (div_pos hU hdR) hf hnon, hnon⟩
  · intro n hn n' hn' he
    have hd1 := (Finset.mem_filter.mp hn).2.1
    have hd2 := (Finset.mem_filter.mp hn').2.1
    calc
      n = d*(n/d) := (Nat.mul_div_cancel' hd1).symm
      _ = d*(n'/d) := by rw [he]
      _ = n' := Nat.mul_div_cancel' hd2
  · intro u hu
    obtain ⟨huW, hfu⟩ := Finset.mem_filter.mp hu
    have hr := brun_ratio hU hd u
    have hnon : f (((d*u : ℕ) : ℝ)/U) ≠ 0 := by rwa [hr]
    refine ⟨d*u, Finset.mem_filter.mpr
      ⟨nonzero_mem_wideWindow hU hf hnon, dvd_mul_right d u, hnon⟩, ?_⟩
    exact Nat.mul_div_cancel_left u hd
  · intro n hn
    have hdn := (Finset.mem_filter.mp hn).2.1
    have he : d*(n/d) = n := Nat.mul_div_cancel' hdn
    rw [← brun_ratio hU hd (n/d), he]

/-- Both independent long substitutions preserve the complete integer
in the residue test and in the coprimality test, even for nonprimitive m. -/
theorem pair_divisor_substitution {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (f g : ℝ → ℂ)
    (hf : Function.support f ⊆ Icc (1/2 : ℝ) (5/2))
    (hg : Function.support g ⊆ Icc (1/2 : ℝ) (5/2))
    (alpha : ℂ) (m : ℕ) (K : ℕ → ℂ) :
    (∑ n ∈ wideWindow U, ∑ k ∈ wideWindow V,
      alpha*f ((n : ℝ)/U)*g ((k : ℝ)/V)*divisorIndicator d₁ n*
        divisorIndicator d₂ k*K (m*n*k)) =
      ∑ u ∈ wideWindow (U/d₁), ∑ v ∈ wideWindow (V/d₂),
        alpha*f ((u : ℝ)/(U/d₁))*g ((v : ℝ)/(V/d₂))*
          K ((m*d₁*d₂)*u*v) := by
  calc
    _ = ∑ n ∈ wideWindow U, f ((n : ℝ)/U)*divisorIndicator d₁ n*
        (∑ k ∈ wideWindow V,
          g ((k : ℝ)/V)*divisorIndicator d₂ k*(alpha*K (m*n*k))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ u ∈ wideWindow (U/d₁), f ((u : ℝ)/(U/d₁))*
        (∑ k ∈ wideWindow V,
          g ((k : ℝ)/V)*divisorIndicator d₂ k*(alpha*K (m*(d₁*u)*k))) :=
      sum_divisor_substitution hU hd₁ f hf _
    _ = ∑ u ∈ wideWindow (U/d₁), f ((u : ℝ)/(U/d₁))*
        (∑ v ∈ wideWindow (V/d₂),
          g ((v : ℝ)/(V/d₂))*(alpha*K (m*(d₁*u)*(d₂*v)))) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [sum_divisor_substitution hV hd₂ g hg]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [show m*(d₁*u)*(d₂*v) = (m*d₁*d₂)*u*v by ring]
      ring

theorem fixedMCore_eq_kernel (I J : Finset ℕ) (m N q : ℕ)
    (alpha : ℂ) (f g : ℝ → ℂ) (U V : ℝ) :
    fixedMCore I J m N q alpha f g U V =
      ∑ u ∈ I, ∑ v ∈ J, alpha*f ((u : ℝ)/U)*g ((v : ℝ)/V)*
        MellinInsertion20261028.residueKernel q N (m*u*v) := by
  rw [fixedMCore_exact]
  have hp (u v : ℕ) : alpha*f ((u : ℝ)/U)*g ((v : ℝ)/V)*
      MellinInsertion20261028.residueKernel q N (m*u*v) =
      (if m*u*v % q = N % q then alpha*f ((u : ℝ)/U)*g ((v : ℝ)/V) else 0) -
      (((Nat.totient q : ℝ)⁻¹ : ℂ) *
        (if Nat.Coprime (m*u*v) q then alpha*f ((u : ℝ)/U)*g ((v : ℝ)/V) else 0)) := by
    by_cases ha : m*u*v % q = N % q <;> by_cases hc : Nat.Coprime (m*u*v) q <;>
      simp [MellinInsertion20261028.residueKernel, ha, hc, div_eq_mul_inv,
        Complex.ofReal_inv] <;> ring
  simp_rw [hp, Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]

def brunCoefficient (Z : ℝ) (h : ℕ) (gap : Bool) (d : ℕ) : ℂ :=
  ((if gap then gapCoefficient (smallPrimes Z) (2*h+1) d
    else upperCoefficient (smallPrimes Z) (2*h) d) : ℂ)

/-- Exactly the original upper or upper-minus-lower polynomial on the
inclusive p<=Z alphabet. These can be complex multiplied without ever
asserting positivity of the lower Brun polynomial. -/
def brunPolynomial (Z : ℝ) (h : ℕ) (gap : Bool) (n : ℕ) : ℂ :=
  ∑ d ∈ brunSupport Z (2*h+1), brunCoefficient Z h gap d * divisorIndicator d n

theorem brunPolynomial_eq_literal (Z : ℝ) (h : ℕ) (gap : Bool) (n : ℕ) :
    brunPolynomial Z h gap n =
      ((ImbalancedChen.OriginalOneLongFiniteBrun.polynomial
        (divisorSupport (smallPrimes Z) (2*h+1))
        ImbalancedChen.OriginalOneLongFiniteBrun.divisorMask
        (fun d => if gap then gapCoefficient (smallPrimes Z) (2*h+1) d
          else upperCoefficient (smallPrimes Z) (2*h) d) n : ℝ) : ℂ) := by
  cases gap <;>
    simp [brunPolynomial, brunSupport, brunCoefficient, divisorIndicator,
      ImbalancedChen.OriginalOneLongFiniteBrun.polynomial,
      ImbalancedChen.OriginalOneLongFiniteBrun.divisorMask,
      Complex.ofReal_sum, Complex.ofReal_mul]

theorem polynomial_pair (Z : ℝ) (h : ℕ) (b₁ b₂ : Bool) (n k : ℕ) :
    brunPolynomial Z h b₁ n * brunPolynomial Z h b₂ k =
      ∑ d ∈ (brunSupport Z (2*h+1)) ×ˢ (brunSupport Z (2*h+1)),
        brunPairCoefficient Z h b₁ b₂ d * divisorIndicator d.1 n * divisorIndicator d.2 k := by
  simp only [brunPolynomial, Finset.sum_mul, Finset.mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  apply Finset.sum_congr rfl
  intro d₂ hd₂
  unfold brunPairCoefficient brunCoefficient
  ring

/-- Source is the literal long-integer double sum with divisibility
polynomials, not a sum of P2 cores by definition. -/
def smoothBrunTupleCore (Z : ℝ) (h : ℕ) (b₁ b₂ : Bool)
    (delta U V t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (alpha : ℂ) (m N q : ℕ) : ℂ :=
  ∑ n ∈ wideWindow U, ∑ k ∈ wideWindow V,
    alpha * leftMellin delta U t₁ label log₁ ((n : ℝ)/U) *
      rightMellin delta V t₂ label log₂ ((k : ℝ)/V) *
      (brunPolynomial Z h b₁ n * brunPolynomial Z h b₂ k) *
      MellinInsertion20261028.residueKernel q N (m*n*k)

theorem smoothBrunTupleCore_eq_expansion {Z delta U V : ℝ}
    (hZ : 1 ≤ Z) (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (h : ℕ) (b₁ b₂ : Bool) (t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (alpha : ℂ) (m N q : ℕ) :
    smoothBrunTupleCore Z h b₁ b₂ delta U V t₁ t₂ label log₁ log₂ alpha m N q =
      ∑ d ∈ (brunSupport Z (2*h+1)) ×ˢ (brunSupport Z (2*h+1)),
        brunPairCoefficient Z h b₁ b₂ d *
          mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha m d.1 d.2 N q := by
  let I := (wideWindow U) ×ˢ (wideWindow V)
  let R := (brunSupport Z (2*h+1)) ×ˢ (brunSupport Z (2*h+1))
  let f := leftMellin delta U t₁ label log₁
  let g := rightMellin delta V t₂ label log₂
  have hf : Function.support f ⊆ Icc (1/2 : ℝ) (5/2) :=
    TwoLongTransitionMellinN2.profile_support _ _ hd hs U t₁
  have hg : Function.support g ⊆ Icc (1/2 : ℝ) (5/2) :=
    TwoLongTransitionMellinN2.profile_support _ _ hd hs V t₂
  calc
    _ = ∑ a ∈ I, ∑ d ∈ R, brunPairCoefficient Z h b₁ b₂ d *
        (alpha*f ((a.1 : ℝ)/U)*g ((a.2 : ℝ)/V)*
          divisorIndicator d.1 a.1*divisorIndicator d.2 a.2*
            MellinInsertion20261028.residueKernel q N (m*a.1*a.2)) := by
      unfold smoothBrunTupleCore
      simp_rw [polynomial_pair]
      simp only [I, R, Finset.sum_product, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro d₁ hd₁
      apply Finset.sum_congr rfl
      intro d₂ hd₂
      dsimp [f, g]
      ring
    _ = ∑ d ∈ R, brunPairCoefficient Z h b₁ b₂ d *
        ∑ a ∈ I, alpha*f ((a.1 : ℝ)/U)*g ((a.2 : ℝ)/V)*
          divisorIndicator d.1 a.1*divisorIndicator d.2 a.2*
            MellinInsertion20261028.residueKernel q N (m*a.1*a.2) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdr
      congr 1
      obtain ⟨hd₁, hd₂⟩ := Finset.mem_product.mp hdr
      have hp₁ := (brunSupport_bounds hZ _ hd₁).1
      have hp₂ := (brunSupport_bounds hZ _ hd₂).1
      simp only [I, Finset.sum_product]
      rw [pair_divisor_substitution hU hV hp₁ hp₂ f g hf hg alpha m]
      exact (fixedMCore_eq_kernel _ _ _ _ _ _ _ _ _ _).symm

end
end ImbalancedChen.Part3.TwoLongLiteralBrunSubstitution
