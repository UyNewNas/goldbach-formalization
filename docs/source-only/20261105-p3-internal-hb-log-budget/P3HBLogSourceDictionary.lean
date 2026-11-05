import ImbalancedChen.P3HBLogScalarProfiles
import ImbalancedChen.P3U5PhysicalProductChart

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Exactly one log SLOT per original HB group, and the inverse log of the
FULL ORIGINAL GROUP. The fixed positive exponent floor is the manuscript's
source-class condition, not a PP estimate or a new analytic input.
The eventual normalization threshold precedes every later tuple and grouping.
This dictionary does not assert the HB convolution identity or its coverage.
-/
namespace ImbalancedChen.P3HBLogSourceDictionary
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P3HBLogScalarProfiles

/-- Product of ALL slots belonging to this original group. -/
def groupProduct {d g : ℕ} (group : Fin d → Fin g) (n : Fin d → ℝ) (j : Fin g) : ℝ :=
  ∏ i,if group i=j then n i else 1

theorem groupProduct_ge_one {d g : ℕ} (group : Fin d → Fin g)
    (n : Fin d → ℝ) (hn : ∀ i,1 ≤ n i) (j : Fin g) : 1 ≤ groupProduct group n j := by
  have h := Finset.prod_le_prod (s:=Finset.univ)
    (f:=fun _ : Fin d => (1 : ℝ)) (g:=fun i => if group i=j then n i else 1)
    (fun i _ => zero_le_one) (fun i _ => by
      by_cases h : group i=j
      · simpa only [if_pos h] using hn i
      · simp only [if_neg h,le_refl])
  simpa only [Finset.prod_const_one] using h

theorem groupProduct_le_total {d g : ℕ} (group : Fin d → Fin g)
    (n : Fin d → ℝ) (hn : ∀ i,1 ≤ n i) (j : Fin g) :
    groupProduct group n j ≤ ∏ i,n i := by
  apply Finset.prod_le_prod
  · intro i hi
    split_ifs
    · exact zero_le_one.trans (hn i)
    · norm_num
  · intro i hi
    split_ifs
    · exact le_rfl
    · exact hn i

theorem slot_le_groupProduct {d g : ℕ} (group : Fin d → Fin g)
    (n : Fin d → ℝ) (hn : ∀ i,1 ≤ n i) (j : Fin g) (k : Fin d)
    (hk : group k=j) : n k ≤ groupProduct group n j := by
  have hp := Finset.prod_le_prod (s:=Finset.univ)
    (f:=fun i => if i=k then n k else 1)
    (g:=fun i => if group i=j then n i else 1)
    (fun i _ => by
      by_cases h : i=k
      · simpa only [if_pos h] using zero_le_one.trans (hn k)
      · simp only [if_neg h]; norm_num)
    (fun i _ => by
      by_cases h : i=k
      · subst i; simp [hk]
      · simp only [if_neg h]
        by_cases hij : group i=j
        · simpa only [if_pos hij] using hn i
        · simp only [if_neg hij,le_refl])
  simpa using hp

theorem slot_le_total {d g : ℕ} (group : Fin d → Fin g)
    (n : Fin d → ℝ) (hn : ∀ i,1 ≤ n i) (k : Fin d) : n k ≤ ∏ i,n i :=
  (slot_le_groupProduct group n hn (group k) k rfl).trans
    (groupProduct_le_total group n hn (group k))

/-- The actual logarithmic factor left by Lambda/log(original group) and
one HB log slot. No inverse of an individual slot logarithm appears. -/
def originalLogFactor {d g : ℕ} (group : Fin d → Fin g) (pick : Fin g → Fin d)
    (n : Fin d → ℝ) : ℝ := ∏ j,Real.log (n (pick j))/Real.log (groupProduct group n j)

def normalizedLogFactor {d g : ℕ} (a ell : ℝ) (group : Fin d → Fin g)
    (pick : Fin g → Fin d) (n : Fin d → ℝ) : ℝ :=
  ∏ j,logProfile (Real.log (n (pick j))/ell)*
    inverseLogProfile a (Real.log (groupProduct group n j)/ell)

/-- Every power of ell cancels, group by group. The guard changes no
value in the physical core domain and introduces no logarithmic loss. -/
theorem normalized_product_eq_original {d g : ℕ} {a ell : ℝ}
    (ha : 0 < a) (hell : 0 < ell) (group : Fin d → Fin g)
    (pick : Fin g → Fin d) (n : Fin d → ℝ)
    (hslot : ∀ i,0 ≤ Real.log (n i)/ell ∧ Real.log (n i)/ell ≤ 2)
    (hgroup : ∀ j,a ≤ Real.log (groupProduct group n j)/ell ∧
      Real.log (groupProduct group n j)/ell ≤ 2) :
    normalizedLogFactor a ell group pick n=originalLogFactor group pick n := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [logProfile_core (hslot (pick j)).1 (hslot (pick j)).2,
    inverseLogProfile_core ha (hgroup j).1 (hgroup j).2]
  have hpos : 0 < Real.log (groupProduct group n j) :=
    (mul_pos ha hell).trans_le ((le_div_iff₀ hell).mp (hgroup j).1)
  field_simp [hell.ne',hpos.ne']

/-- A unit in the designated log slot kills that actual HB term. -/
theorem unit_log_slot_zero {d g : ℕ} (group : Fin d → Fin g)
    (pick : Fin g → Fin d) (n : Fin d → ℝ) (j : Fin g)
    (hj : n (pick j)=1) : originalLogFactor group pick n=0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hj,Real.log_one,zero_div]

theorem originalLogFactor_range {d g : ℕ} (group : Fin d → Fin g)
    (pick : Fin g → Fin d) (hpick : ∀ j,group (pick j)=j)
    (n : Fin d → ℝ) (hn : ∀ i,1 ≤ n i)
    (hG : ∀ j,1 < groupProduct group n j) :
    0 ≤ originalLogFactor group pick n ∧ originalLogFactor group pick n ≤ 1 := by
  have hj (j : Fin g) :
      0 ≤ Real.log (n (pick j))/Real.log (groupProduct group n j) ∧
      Real.log (n (pick j))/Real.log (groupProduct group n j) ≤ 1 := by
    have hg := Real.log_pos (hG j)
    refine ⟨div_nonneg (Real.log_nonneg (hn (pick j))) hg.le,(div_le_one hg).mpr ?_⟩
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one (hn (pick j)))
      (slot_le_groupProduct group n hn j (pick j) (hpick j))
  exact ⟨Finset.prod_nonneg (fun j _ => (hj j).1),
    Finset.prod_le_one (fun j _ => (hj j).1) (fun j _ => (hj j).2)⟩

private theorem normalized_log_upper {N : ℕ} {C x : ℝ} (hN : 1 < N)
    (hC : 0 < C) (hell : 1 ≤ Real.log (N : ℝ)) (hCbudget : Real.log C ≤ Real.log (N : ℝ))
    (hx : 1 ≤ x) (hupper : x ≤ C*(N : ℝ)) :
    0 ≤ Real.log x/Real.log (N : ℝ) ∧ Real.log x/Real.log (N : ℝ) ≤ 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he : 0 < Real.log (N : ℝ) := by linarith
  have hu := Real.log_le_log (lt_of_lt_of_le zero_lt_one hx) hupper
  rw [Real.log_mul hC.ne' hNp.ne'] at hu
  refine ⟨div_nonneg (Real.log_nonneg hx) he.le,(div_le_iff₀ he).mpr ?_⟩
  linarith

/-- No arithmetic estimate is assumed. The supplied physical size gates
are exactly n_i>=1, every original group>=c*N^alpha, and total product<=C*N. -/
theorem log_domains {N d g : ℕ} (hN : 1 < N) (alpha c C : ℝ)
    (halpha : 0 < alpha) (hc : 0 < c) (hC : 0 < C)
    (hell : 1 ≤ Real.log (N : ℝ))
    (hlower : 2*|Real.log c| ≤ alpha*Real.log (N : ℝ))
    (hupper : Real.log C ≤ Real.log (N : ℝ))
    (group : Fin d → Fin g) (n : Fin d → ℝ) (hn : ∀ i,1 ≤ n i)
    (hgroups : ∀ j,c*(N : ℝ)^alpha ≤ groupProduct group n j)
    (htotal : (∏ i,n i) ≤ C*(N : ℝ)) :
    (∀ i,0 ≤ Real.log (n i)/Real.log (N : ℝ) ∧
      Real.log (n i)/Real.log (N : ℝ) ≤ 2) ∧
    (∀ j,alpha/2 ≤ Real.log (groupProduct group n j)/Real.log (N : ℝ) ∧
      Real.log (groupProduct group n j)/Real.log (N : ℝ) ≤ 2) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he : 0 < Real.log (N : ℝ) := by linarith
  constructor
  · intro i
    exact normalized_log_upper hN hC hell hupper (hn i)
      ((slot_le_total group n hn i).trans htotal)
  · intro j
    have hgu := normalized_log_upper hN hC hell hupper (groupProduct_ge_one group n hn j)
      ((groupProduct_le_total group n hn j).trans htotal)
    refine ⟨(le_div_iff₀ he).mpr ?_,hgu.2⟩
    have hp : 0 < (N : ℝ)^alpha := Real.rpow_pos_of_pos hNp _
    have hl := Real.log_le_log (mul_pos hc hp) (hgroups j)
    rw [Real.log_mul hc.ne' hp.ne',Real.rpow_def_of_pos hNp,Real.log_exp] at hl
    nlinarith [neg_abs_le (Real.log c)]

/-- One threshold before ALL later tuples, dimensions, groupings and
chosen log slots. alpha,c,C are fixed source-class data. -/
theorem eventually_log_domains (alpha c C : ℝ)
    (halpha : 0 < alpha) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,1 ≤ Real.log (N : ℝ) ∧
      ∀ (d g : ℕ) (group : Fin d → Fin g) (n : Fin d → ℝ),
        (∀ i,1 ≤ n i) → (∀ j,c*(N : ℝ)^alpha ≤ groupProduct group n j) →
        (∏ i,n i) ≤ C*(N : ℝ) →
        (∀ i,0 ≤ Real.log (n i)/Real.log (N : ℝ) ∧ Real.log (n i)/Real.log (N : ℝ) ≤ 2) ∧
        (∀ j,alpha/2 ≤ Real.log (groupProduct group n j)/Real.log (N : ℝ) ∧
          Real.log (groupProduct group n j)/Real.log (N : ℝ) ≤ 2) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop
    (max 1 (max (2*|Real.log c|/alpha) (Real.log C)))),
    eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have he : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hN
  have hl : 2*|Real.log c| ≤ alpha*Real.log (N : ℝ) := by
    have hh : 2*|Real.log c|/alpha ≤ Real.log (N : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have hh' := (div_le_iff₀ halpha).mp hh
    nlinarith
  have hu : Real.log C ≤ Real.log (N : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  exact ⟨he,fun d g group n hn hg ht =>
    log_domains (by omega) alpha c C halpha hc hC he hl hu group n hn hg ht⟩

end
end ImbalancedChen.P3HBLogSourceDictionary
