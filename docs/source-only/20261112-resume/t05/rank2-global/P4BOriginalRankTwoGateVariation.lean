import ImbalancedChen.P4BOriginalTwoAtlasSmallPayment
import ImbalancedChen.P0VariableProfileWidthVariation

/-! The four actual affine walls and actual product eta on the complete
ordered pair. The companion integer is fixed, the first prime varies. -/
namespace ImbalancedChen.P4BOriginalRankTwoGateVariation
noncomputable section
open Classical
open scoped BigOperators
open P4B
open P4BOriginalPairFibreVariation (coord offset direction)
open P4BOriginalPairFibreDictionary (naturalWeight)
open P5Z.ActualEtaPsiOccurrenceBudget (eta eta_bounds)

def factor (b kap s kap0 : ℝ) (N t : ℕ) : Fin 5 → ℕ → ℝ :=
  Fin.cons (fun p => eta (((p:ℝ)*(t:ℝ))/(N:ℝ)^(1-kap0))) (fun i p =>
    smoothGateUpperStep s
      (smoothPhysicalProfileMargin b N (manuscriptHalfProductCutoff kap N) (offset true N t) i+
       smoothPhysicalWallRow b N i (direction true)*coord N p))

theorem actual_product (b kap s kap0 : ℝ) (N p t : ℕ) :
    naturalWeight b kap s kap0 N p t=∏ i:Fin 5,factor b kap s kap0 N t i p := by
  have hv : offset true N t+coord N p • direction true=![coord N p, coord N t] := by
    funext i
    fin_cases i <;> simp [offset,direction]
  have hg := congrFun (smoothPhysicalProfileLine_eq_affine_gate_product b N
    (manuscriptHalfProductCutoff kap N) s (offset true N t) (direction true)) (coord N p)
  rw [smoothPhysicalProfileLine,hv] at hg
  simp only [naturalWeight,hg,Fin.prod_univ_succ,factor,Fin.cons_zero,Fin.cons_succ]

theorem factor_unit (b kap s kap0 : ℝ) (N t p : ℕ) (i : Fin 5) :
    0≤factor b kap s kap0 N t i p ∧ factor b kap s kap0 N t i p≤1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact eta_bounds _
  · exact smoothGateUpperStep_bounds _ _

theorem factor_direction (b kap kap0 : ℝ) {s : ℝ} {N : ℕ}
    (hN : (1:ℝ)<N) (hs : 0<s) (t : ℕ) (i : Fin 5) :
    Monotone (factor b kap s kap0 N t i) ∨ Antitone (factor b kap s kap0 N t i) := by
  have hm : Monotone (coord N) := by
    intro p q hpq
    exact div_le_div_of_nonneg_right (Real.log_le_log
      (zero_lt_one.trans_le (le_max_left _ _)) (max_le_max_left 1 (Nat.cast_le.mpr hpq)))
      (Real.log_pos hN).le
  refine Fin.cases ?_ (fun j => ?_) i
  · left
    intro p q hpq
    exact Real.smoothTransition.monotone (sub_le_sub_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hpq) (Nat.cast_nonneg t))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _)
  · by_cases h : 0≤smoothPhysicalWallRow b N j (direction true)
    · exact Or.inl (fun p q hpq => monotone_smoothGateUpperStep hs
        (add_le_add_left (mul_le_mul_of_nonneg_left (hm hpq) h) _))
    · exact Or.inr (fun p q hpq => monotone_smoothGateUpperStep hs
        (add_le_add_left (mul_le_mul_of_nonpos_left (hm hpq) (lt_of_not_ge h).le) _))

def oscillation (b kap s kap0 : ℝ) (N t l u : ℕ) : ℝ :=
  ∑ i:Fin 5,|factor b kap s kap0 N t i u-factor b kap s kap0 N t i l|

theorem oscillation_nonneg (b kap s kap0 : ℝ) (N t l u : ℕ) :
    0≤oscillation b kap s kap0 N t l u := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem weight_unit (b kap s kap0 : ℝ) (N p t : ℕ) :
    0≤naturalWeight b kap s kap0 N p t ∧ naturalWeight b kap s kap0 N p t≤1 := by
  rw [actual_product]
  exact ⟨Finset.prod_nonneg (fun i _ => (factor_unit _ _ _ _ _ _ _ i).1),
    Finset.prod_le_one (fun i _ => (factor_unit _ _ _ _ _ _ _ i).1)
      (fun i _ => (factor_unit _ _ _ _ _ _ _ i).2)⟩

theorem local_oscillation (b kap kap0 : ℝ) {s : ℝ} {N : ℕ} (hN : (1:ℝ)<N) (hs : 0<s)
    (t : ℕ) {l p u : ℕ} (hl : l≤p) (hu : p≤u) :
    |naturalWeight b kap s kap0 N p t-naturalWeight b kap s kap0 N l t|≤
      oscillation b kap s kap0 N t l u := by
  rw [actual_product,actual_product]
  apply (P0VariableProfileWidthVariation.abs_prod_sub_prod_le_sum_abs_of_unit_interval
    Finset.univ _ _ (fun i _ => factor_unit _ _ _ _ _ _ _ i)
    (fun i _ => factor_unit _ _ _ _ _ _ _ i)).trans
  apply Finset.sum_le_sum
  intro i _
  rcases factor_direction b kap kap0 hN hs t i with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (h hl)),abs_of_nonneg (sub_nonneg.mpr (h (hl.trans hu)))]
    linarith [h hu]
  · rw [abs_of_nonpos (sub_nonpos.mpr (h hl)),abs_of_nonpos (sub_nonpos.mpr (h (hl.trans hu)))]
    linarith [h hu]

/-- Endpoints are common to all companion primes and both signs of
the modulus coefficient. All five sums telescope on the very same grid. -/
theorem total_oscillation (b kap kap0 : ℝ) {s : ℝ} {N : ℕ} (hN : (1:ℝ)<N) (hs : 0<s)
    (t J : ℕ) (edge : ℕ → ℕ) (he : Monotone edge) :
    (∑ i∈Finset.range J,oscillation b kap s kap0 N t (edge i) (edge (i+1)))≤5 := by
  unfold oscillation
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j:Fin 5,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      let f := factor b kap s kap0 N t j
      have hf (z : ℕ) : 0≤f z ∧ f z≤1 := factor_unit _ _ _ _ _ _ _ _
      change (∑ i∈Finset.range J,|f (edge (i+1))-f (edge i)|)≤1
      rcases factor_direction b kap kap0 hN hs t j with h|h
      · have ha (i : ℕ) := abs_of_nonneg (sub_nonneg.mpr (h (he (Nat.le_succ i))))
        simp only [ha,Finset.sum_range_sub]
        linarith [(hf (edge J)).2,(hf (edge 0)).1]
      · have ha (i : ℕ) : |f (edge (i+1))-f (edge i)|=f (edge i)-f (edge (i+1)) := by
          rw [abs_of_nonpos (sub_nonpos.mpr (h (he (Nat.le_succ i))))]
          ring
        simp only [ha,Finset.sum_range_sub']
        linarith [(hf (edge 0)).2,(hf (edge J)).1]
    _ = 5 := by simp

end
end ImbalancedChen.P4BOriginalRankTwoGateVariation
