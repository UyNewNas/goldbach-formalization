import ImbalancedChen.P2EnhancedExactExceptionTheta
import ImbalancedChen.P5zMarkedPrimeFamilyMultiplicity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Source class: second-seed-stable-prefix-extension.tex:18--28, finite
nonnegative combinations of marked prime-box indicators. S below is the
ORIGINAL labelled subfamily, including its ordering/history/deletion
filters, and W is its original mark scalar. The existing weighted product
pushforward retains equal-product multiplicities. Its support bounds are
derived from literal prime-window membership and physical residual box
coordinates; d>0 is not substituted for source membership.

This supplies exceptional payment for this original source class. It does
not construct the complete causal 440-level arithmetic graph or identify
all of its leaf measures. Those are distinct source-dictionary obligations.
-/

namespace ImbalancedChen.P2EnhancedMarkedBoxExceptionSupply
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted
open P2EnhancedCollisionWeightedBudget
open P2EnhancedExactExceptionTheta
open scoped Classical BigOperators

def markSupport {r N : ℕ} (S : Finset (Fin r → Fin (N+1))) : Finset ℕ :=
  S.image Part3.labelledProduct

/-- Primitive prime-box membership gives every slot's lower bound.
The half-open endpoints and target deletion are inherited from primeWindow. -/
theorem marked_slot_data {r N : ℕ} {eta : ℝ} {lo hi : Fin r → ℝ}
    {S : Finset (Fin r → Fin (N+1))}
    (hN : 1 ≤ N) (hlo : ∀ j, eta ≤ lo j)
    (hbox : ∀ t ∈ S, ∀ j, (t j).val ∈
      primeWindow N ((N : ℝ)^(lo j)) ((N : ℝ)^(hi j)))
    {t : Fin r → Fin (N+1)} (ht : t ∈ S) :
    ∀ j, (t j).val.Prime ∧ (N : ℝ)^eta ≤ ((t j).val : ℝ) := by
  intro j
  have hw := mem_primeWindow.mp (hbox t ht j)
  exact ⟨hw.1, (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hN) (hlo j)).trans hw.2.2.1⟩

/-- Extract a genuine marked tuple from the product-support membership,
then inherit its prime divisors. No injectivity of product is assumed. -/
theorem marked_old_support {r N d : ℕ} {eta : ℝ} {lo hi : Fin r → ℝ}
    {S : Finset (Fin r → Fin (N+1))}
    (hN : 1 ≤ N) (hlo : ∀ j, eta ≤ lo j)
    (hbox : ∀ t ∈ S, ∀ j, (t j).val ∈
      primeWindow N ((N : ℝ)^(lo j)) ((N : ℝ)^(hi j)))
    (hd : d ∈ markSupport S) :
    0 < d ∧ ∀ p ∈ d.primeFactors, (N : ℝ)^eta ≤ (p : ℝ) := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hd
  have htdata := marked_slot_data hN hlo hbox ht
  have hpos : 0 < Part3.labelledProduct t := by
    unfold Part3.labelledProduct
    exact prod_pos (fun j _ => (htdata j).1.pos)
  refine ⟨hpos, ?_⟩
  intro p hp
  obtain ⟨hpprime, hpdiv, _⟩ := Nat.mem_primeFactors.mp hp
  let l : List ℕ := List.ofFn (fun j : Fin r => (t j).val)
  have hlprod : l.prod = Part3.labelledProduct t := by
    simp only [l, List.prod_ofFn, Part3.labelledProduct]
  apply list_prime_divisor_lower l hpprime (by simpa only [hlprod] using hpdiv)
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  exact htdata j

/-- A lower bound for the genuine residual exponent implies the seed's
new-prime cutoff; this uses log(Q/d), not a classical-Q replacement. -/
theorem cutoff_from_residual_box {N d : ℕ} {Q eta : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hQd : (d : ℝ) < Q)
    (hres : (227/50 : ℝ)*eta ≤ Real.log (Q/(d : ℝ))/Real.log N) :
    1 < Q/(d : ℝ) ∧ (N : ℝ)^eta ≤ cutoff Q d (227/50) := by
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hR : 1 < Q/(d : ℝ) := (one_lt_div hdr).mpr hQd
  refine ⟨hR, ?_⟩
  have hres' := (le_div_iff₀ hlog).mp hres
  unfold cutoff
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hNr),
    Real.rpow_def_of_pos (zero_lt_one.trans hR)]
  apply Real.exp_le_exp.mpr
  nlinarith only [hres']

/-- All primitive cutoff/support inputs to BOTH exception suppliers are
proved from each original mark, before any positive weighting. -/
theorem marked_support_data {r N : ℕ} {Q eta : ℝ} {lo hi : Fin r → ℝ}
    {S : Finset (Fin r → Fin (N+1))}
    (hN : 1 < N) (hlo : ∀ j, eta ≤ lo j)
    (hbox : ∀ t ∈ S, ∀ j, (t j).val ∈
      primeWindow N ((N : ℝ)^(lo j)) ((N : ℝ)^(hi j)))
    (hphysical : ∀ t ∈ S, (Part3.labelledProduct t : ℝ) < Q)
    (hres : ∀ t ∈ S, (227/50 : ℝ)*eta ≤
      Real.log (Q/(Part3.labelledProduct t : ℝ))/Real.log N) :
    ∀ d ∈ markSupport S, 0 < d ∧ 1 < Q/(d : ℝ) ∧
      (∀ p ∈ d.primeFactors, (N : ℝ)^eta ≤ (p : ℝ)) ∧
      (N : ℝ)^eta ≤ cutoff Q d (227/50) := by
  intro d hd
  have hold := marked_old_support hN.le hlo hbox hd
  obtain ⟨t, ht, htd⟩ := mem_image.mp hd
  have hnew := cutoff_from_residual_box hN hold.1
    (by simpa only [htd] using hphysical t ht) (by simpa only [htd] using hres t ht)
  exact ⟨hold.1, hnew.1, hold.2, hnew.2⟩

/-- Literal finite positive combinations, with the mark tag remaining in
the sum. Different ranks, paths and equal products are not identified. -/
def mixtureSupport {I : Type*} {N : ℕ} (A : Finset I) (rank : I → ℕ)
    (S : (i : I) → Finset (Fin (rank i) → Fin (N+1))) : Finset ℕ :=
  A.biUnion (fun i => markSupport (S i))

def mixtureSigma {I : Type*} {N : ℕ} (A : Finset I) (rank : I → ℕ)
    (S : (i : I) → Finset (Fin (rank i) → Fin (N+1)))
    (W : (i : I) → (Fin (rank i) → Fin (N+1)) → ℝ) (d : ℕ) : ℝ :=
  ∑ i ∈ A, p5z_markedProductWeight (S i) (W i) d

/-- Genuine original marked-prime-box supply, uniform before N, Q,
all original marks, ranks and nonnegative scalar weights. No target
error bound, PP estimate, density or positive-total licence is a premise.
This also reuses the previously completed selected-collision payment. -/
theorem marked_box_mixture_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Q : ℝ, Q ≤ (N : ℝ) →
      ∀ (I : Type*) (A : Finset I) (rank : I → ℕ)
        (lo hi : (i : I) → Fin (rank i) → ℝ)
        (S : (i : I) → Finset (Fin (rank i) → Fin (N+1)))
        (W : (i : I) → (Fin (rank i) → Fin (N+1)) → ℝ),
      (∀ i ∈ A, ∀ j, eta ≤ lo i j) →
      (∀ i ∈ A, ∀ t ∈ S i, ∀ j, (t j).val ∈
        primeWindow N ((N : ℝ)^(lo i j)) ((N : ℝ)^(hi i j))) →
      (∀ i ∈ A, ∀ t ∈ S i, (Part3.labelledProduct t : ℝ) < Q) →
      (∀ i ∈ A, ∀ t ∈ S i, (227/50 : ℝ)*eta ≤
        Real.log (Q/(Part3.labelledProduct t : ℝ))/Real.log N) →
      (∀ i ∈ A, ∀ t ∈ S i, 0 ≤ W i t) →
      let D := mixtureSupport A rank S
      let sigma := mixtureSigma A rank S W
      weightedErrors N Q D sigma + weightedCollisions N Q D sigma ≤
        epsilon*Theta N Q D sigma := by
  obtain ⟨T,hT,hpay⟩ := all_retained_errors_theta_payment heta hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT he Q hQ I A rank lo hi S W hlo hbox hphysical hres hW
  let D := mixtureSupport A rank S
  let sigma := mixtureSigma A rank S W
  have hN : 1 < N := by have := hT.trans hNT; omega
  have hsupport : ∀ d ∈ D, 0 < d ∧ 1 < Q/(d : ℝ) ∧
      (∀ p ∈ d.primeFactors, (N : ℝ)^eta ≤ (p : ℝ)) ∧
      (N : ℝ)^eta ≤ cutoff Q d (227/50) := by
    intro d hd
    obtain ⟨i, hiA, hdi⟩ := mem_biUnion.mp hd
    exact marked_support_data hN (hlo i hiA) (hbox i hiA)
      (hphysical i hiA) (hres i hiA) d hdi
  have hsigma : ∀ d ∈ D, 0 ≤ sigma d := by
    intro d _
    exact sum_nonneg (fun i hiA => p5z_markedProductWeight_nonneg
      (S i) (W i) (hW i hiA) d)
  exact hpay N hNT he Q D sigma hQ
    (fun d hd => (hsupport d hd).1) hsigma
    (fun d hd => (hsupport d hd).2.1)
    (fun d hd => (hsupport d hd).2.2.1)
    (fun d hd => (hsupport d hd).2.2.2)

end
end ImbalancedChen.P2EnhancedMarkedBoxExceptionSupply
