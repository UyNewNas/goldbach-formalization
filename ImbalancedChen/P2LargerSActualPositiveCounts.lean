import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The larger-S operation is proved on actual positive quotient counts,
with the given sigma and a fixed receiver/history predicate. Neither a
count estimate nor a defect/table value is an input. The same natural
multiplier d, old mask d*N, total real Q, and all fixed history tests are
used on both sides. No coprimality or squarefree assumption on d occurs.

The denominator is the existing literal manuscript Theta: singular
factor C(d*N), totient(d), log(Q/d), and literal integral li from 2 to N.
It is not silently replaced by the separately normalized trueLi, which
adds 2/log(2). A normalized deficit below means exactly 1-count/Theta;
identifying it with an analytic upper defect still needs the ordinary
A(s)=1 dictionary and an independent prior count supplier.

This finite monotonicity is valid for arbitrary fixed finite positive
families. It does not assert their ordinary AP distribution, native
enhanced-family admissibility, stable-ceiling closure, or K/4 estimate.
-/

namespace ImbalancedChen.P2LargerSActualPositiveCounts

noncomputable section

open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (cutoff Phi Theta Theta_pos)
open scoped Classical

/-- The fixed history predicate can retain every original receiver test.
Only roughness changes when the comparison parameter changes. -/
def historyCarrier (N d : ℕ) (E : ℕ → ℕ → Prop) (z : ℝ) : Finset ℕ :=
  (sieveCarrier N d (d*N) z).filter (E d)

/-- A literal positive family, at its possibly different physical cutoffs.
The original sigma remains the coefficient; no beta replaces it. -/
def physicalCount (N : ℕ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (E : ℕ → ℕ → Prop) (z : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * ((historyCarrier N d E (z d)).card : ℝ)

theorem historyCarrier_antitone (N d : ℕ) (E : ℕ → ℕ → Prop)
    {low high : ℝ} (h : low≤high) :
    historyCarrier N d E high ⊆ historyCarrier N d E low := by
  intro ell hell
  obtain ⟨hcarrier,hE⟩ := mem_filter.mp hell
  obtain ⟨hrange,hprime,hdiv,hsift⟩ := mem_filter.mp hcarrier
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨hrange,hprime,hdiv,?_⟩,hE⟩
  intro p hp hmask hpz
  exact hsift p hp hmask (hpz.trans_le h)

/-- At fixed positive weights, lowering each physical cutoff enlarges
the actual finite quotient count, including its unit receivers. -/
theorem physicalCount_antitone (N : ℕ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (E : ℕ → ℕ → Prop) {low high : ℕ → ℝ}
    (hsigma : ∀d∈D,0≤sigma d) (h : ∀d∈D,low d≤high d) :
    physicalCount N D sigma E high ≤ physicalCount N D sigma E low := by
  unfold physicalCount
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (hsigma d hd)
  exact_mod_cast card_le_card (historyCarrier_antitone N d E (h d hd))

/-- Larger S lowers the actual power cutoff at the unchanged Q/d. -/
theorem cutoff_larger_parameter {Q s S : ℝ} {d : ℕ}
    (hR : 1≤Q/(d:ℝ)) (hs : 0<s) (hsS : s≤S) :
    cutoff Q d S≤cutoff Q d s := by
  exact Real.rpow_le_rpow_of_exponent_le hR
    (one_div_le_one_div_of_le hs hsS)

/-- The original physical ceiling is inherited, with no new family test
or substitution of the larger comparison for the physical cutoff. -/
theorem larger_parameter_admitted {Q s S chi : ℝ} {d : ℕ}
    (hR : 1≤Q/(d:ℝ)) (hs : 0<s) (hsS : s≤S)
    (hphysical : cutoff Q d s≤chi) :
    cutoff Q d S≤cutoff Q d s ∧ cutoff Q d S≤chi := by
  have hc := cutoff_larger_parameter hR hs hsS
  exact ⟨hc,hc.trans hphysical⟩

/-- The comparison may vary with the original marked multiplier. Each
side uses precisely the same sigma, history predicate, Q and mask d*N. -/
theorem actual_count_larger_parameter (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop) {s S : ℕ → ℝ}
    (hsigma : ∀d∈D,0≤sigma d) (hR : ∀d∈D,1≤Q/(d:ℝ))
    (hs : ∀d∈D,0<s d) (hsS : ∀d∈D,s d≤S d) :
    physicalCount N D sigma E (fun d=>cutoff Q d (s d)) ≤
      physicalCount N D sigma E (fun d=>cutoff Q d (S d)) := by
  exact physicalCount_antitone N D sigma E hsigma
    (fun d hd=>cutoff_larger_parameter (hR d hd) (hs d hd) (hsS d hd))

/-- Direct physical form needed by inherited D5/D6 cutoffs: an admitted
comparison lies below the actual cutoff, which remains in the left count.
No arithmetic upper bound for the comparison is assumed here. -/
theorem actual_physical_count_le_comparison (N : ℕ) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop)
    (z : ℕ → ℝ) (S : ℝ) (hsigma : ∀d∈D,0≤sigma d)
    (hadmit : ∀d∈D,cutoff Q d S≤z d) :
    physicalCount N D sigma E z ≤
      physicalCount N D sigma E (fun d=>cutoff Q d S) :=
  physicalCount_antitone N D sigma E hsigma hadmit

/-- Unrestricted histories give the existing native source Phi EXACTLY.
The source/quotient equality uses d dividing its actual old mask d*N;
it imposes no new square or coprimality condition on selected factors. -/
theorem physicalCount_eq_native_Phi (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (s : ℝ) :
    physicalCount N D sigma (fun _ _=>True) (fun d=>cutoff Q d s)=
      Phi N Q D sigma s := by
  unfold physicalCount Phi
  apply sum_congr rfl
  intro d hd
  have hc := (source_double_sieve_carriers N d (cutoff Q d s)).1
  simp only [historyCarrier,filter_true_of_mem (fun _ _=>True.intro)]
  unfold sourceSieveCount
  rw [hc]
  norm_cast

/-- Native-family specialization, with the original sigma rather than
an independent convolution coefficient. -/
theorem native_Phi_larger_parameter (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) {s S : ℝ} (hsigma : ∀d∈D,0≤sigma d)
    (hR : ∀d∈D,1≤Q/(d:ℝ)) (hs : 0<s) (hsS : s≤S) :
    Phi N Q D sigma s≤Phi N Q D sigma S := by
  rw [←physicalCount_eq_native_Phi,←physicalCount_eq_native_Phi]
  exact actual_count_larger_parameter N Q D sigma (fun _ _=>True)
    hsigma hR (fun _ _=>hs) (fun _ _=>hsS)

/-- The common original Theta is proved positive from primitive support
data. This is a count comparison at that exact normalization. -/
theorem normalized_physical_count_le_comparison {N : ℕ} (hN : 4≤N)
    (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop)
    (z : ℕ → ℝ) (S : ℝ) (hdpos : ∀d∈D,0<d)
    (hsigma : ∀d∈D,0≤sigma d) (hR : ∀d∈D,1<Q/(d:ℝ))
    (hpositive : ∃d∈D,0<sigma d) (hadmit : ∀d∈D,cutoff Q d S≤z d) :
    physicalCount N D sigma E z / Theta N Q D sigma ≤
      physicalCount N D sigma E (fun d=>cutoff Q d S) / Theta N Q D sigma := by
  exact div_le_div_of_nonneg_right
    (actual_physical_count_le_comparison N Q D sigma E z S hsigma hadmit)
    (Theta_pos hN Q D sigma hdpos hsigma hR hpositive).le

/-- The algebraic normalized deficit at the actual physical cutoff is
at least the deficit of the admitted comparison. No analytic H value is
presupposed; using a proved prior upper estimate remains an external step. -/
theorem normalized_deficit_comparison {N : ℕ} (hN : 4≤N)
    (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop)
    (z : ℕ → ℝ) (S : ℝ) (hdpos : ∀d∈D,0<d)
    (hsigma : ∀d∈D,0≤sigma d) (hR : ∀d∈D,1<Q/(d:ℝ))
    (hpositive : ∃d∈D,0<sigma d) (hadmit : ∀d∈D,cutoff Q d S≤z d) :
    1-physicalCount N D sigma E (fun d=>cutoff Q d S)/Theta N Q D sigma ≤
      1-physicalCount N D sigma E z/Theta N Q D sigma := by
  exact sub_le_sub_left
    (normalized_physical_count_le_comparison hN Q D sigma E z S
      hdpos hsigma hR hpositive hadmit) 1

end
end ImbalancedChen.P2LargerSActualPositiveCounts
