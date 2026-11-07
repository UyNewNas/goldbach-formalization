import ImbalancedChen.BoundaryLogMesh
import ImbalancedChen.P2GammaRetainedPhysicalRows
import ImbalancedChen.P2GammaLowerRejectedPayment
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal O/Q logarithmic hats, at delta=(log N)^(-B).  The grid
ceiling includes the last endpoint.  Bounds are uniform in the original
target, marked pair, mother occurrence and grid labels.  Actual alpha,
beta, their multiplicities and the physical modulus coefficient are not
redefined.  Mellin/Fourier norms of additional coupled amplitudes are
not asserted by the one-variable logarithmic derivative result.
-/

namespace ImbalancedChen.P2GammaChosenLogGridBudget
noncomputable section
open Filter Set MeasureTheory
open scoped BigOperators Topology
open P2GammaSmoothLogGrid P2GammaHeadWindowDictionary
open P2GammaVariablePrimeProfile P2GammaLowerRejectedPayment
open P2GammaCompleteProductTrimPayment

/-- The actual mesh is chosen before any arithmetic data. -/
def gridLength (B N : ℕ) : ℕ :=
  Nat.ceil (Real.log (N : ℝ) / boundaryLogMesh B N + 1)

theorem gridLength_covers (B N : ℕ) :
    Real.log (N : ℝ) / boundaryLogMesh B N + 1 ≤ (gridLength B N : ℝ) :=
  Nat.le_ceil _

/-- The original partition identity, with its cover hypothesis supplied. -/
theorem chosen_grid_partition {B N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ))
    {p : ℝ} (hp : 1 ≤ p) (hpN : p ≤ N) :
    (∑ j ∈ Finset.range (gridLength B N), weight (boundaryLogMesh B N) j p) = 1 := by
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hδ : 0 < boundaryLogMesh B N := by unfold boundaryLogMesh; positivity
  apply weight_sum_eq_one hδ hp
  apply (add_le_add_right (div_le_div_of_nonneg_right
    (Real.log_le_log (zero_lt_one.trans_le hp) hpN) hδ.le) 1).trans
  exact gridLength_covers B N

theorem eventually_chosen_mesh_factor_two {B : ℕ} (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (N : ℝ) ∧ 0 < boundaryLogMesh B N ∧
        2 * boundaryLogMesh B N ≤ Real.log 2 := by
  have hsmall := (tendsto_boundaryLogMesh hB).eventually
    (gt_mem_nhds (show (0 : ℝ) < Real.log 2 / 2 by
      exact div_pos (Real.log_pos (by norm_num)) (by norm_num)))
  filter_upwards [eventually_one_le_nat_log, eventually_boundaryLogMesh_mem B,
    hsmall] with N hlog hmem hN
  exact ⟨hlog, hmem.1, by linarith⟩

theorem gridLength_le {B N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) :
    (gridLength B N : ℝ) ≤ 3 * (Real.log (N : ℝ)) ^ (B + 1) := by
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hratio : Real.log (N : ℝ) / boundaryLogMesh B N =
      (Real.log (N : ℝ)) ^ (B + 1) := by
    unfold boundaryLogMesh
    simp only [one_div,div_eq_mul_inv,inv_inv]
    rw [pow_succ]
    ring
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ Real.log (N : ℝ) / boundaryLogMesh B N + 1 by
      rw [hratio]; positivity)).le
  have hp : 1 ≤ (Real.log (N : ℝ)) ^ (B + 1) := one_le_pow₀ hlog
  change (Nat.ceil _ : ℝ) ≤ _
  rw [hratio] at hceil
  linarith

theorem chosen_chart_count_le {B N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) :
    (((Finset.range (gridLength B N)).product
      (Finset.range (gridLength B N))).card : ℝ) ≤
      9 * (Real.log (N : ℝ)) ^ (2 * (B + 1)) := by
  have h := pow_le_pow_left₀ (Nat.cast_nonneg (gridLength B N))
    (gridLength_le hlog) 2
  simpa only [Finset.card_product, Finset.card_range, Nat.cast_mul,
    mul_pow, ← pow_mul, Nat.mul_comm (B + 1) 2, show (3 : ℝ)^2 = 9 by norm_num,
    pow_two] using h

/-- Exact global-to-local logarithmic transport at the complete scale. -/
theorem log_target_le_local {N : ℕ} {x beta : ℝ}
    (hN : 0 < N) (hbeta : 0 < beta) (hx : (N : ℝ)^beta ≤ x) :
    Real.log (N : ℝ) ≤ Real.log x / beta := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.log_le_log (Real.rpow_pos_of_pos hNp beta) hx
  rw [Real.log_rpow hNp] at h
  exact (le_div_iff₀ hbeta).mpr (by nlinarith)

/-- The scalar norm requested by Q15 is an output for the chosen mesh.
The explicit W is fixed before N and before every occupied chart. -/
theorem chosen_mesh_profile_budget {B N : ℕ} {D beta x : ℝ}
    (hD : 0 ≤ D) (hbeta : 0 < beta) (hN : 0 < N)
    (hlogN : 1 ≤ Real.log (N : ℝ)) (hlogx : 1 ≤ Real.log x)
    (hx : (N : ℝ)^beta ≤ x) :
    1 + 2*D / boundaryLogMesh B N ≤
      (1 + 2*D / beta^B) * (Real.log x)^B := by
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hpower : (Real.log (N : ℝ))^B ≤ (Real.log x)^B / beta^B := by
    simpa only [div_pow] using pow_le_pow_left₀ hlogN0
      (log_target_le_local hN hbeta hx) B
  have hxpow : 1 ≤ (Real.log x)^B := one_le_pow₀ hlogx
  calc
    _ = 1 + 2*D*(Real.log (N : ℝ))^B := by
      unfold boundaryLogMesh
      simp only [one_div,div_eq_mul_inv,inv_inv]
    _ ≤ (Real.log x)^B + 2*D*((Real.log x)^B/beta^B) :=
      add_le_add hxpow (mul_le_mul_of_nonneg_left hpower (by positivity))
    _ = _ := by ring

/-- Actual clipped-head Abel norms, including empty or reversed clips.
The bound is supplied from the concrete hat rather than a norm premise. -/
theorem exists_actual_head_Abel_budget :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ δ : ℝ, 0 < δ →
      ∀ (N : ℕ) (t : ℕ × ℕ) (c j : ℕ),
      profileAbelNorm (complexWeight δ j)
        (clipLo N t c (lower δ j)) (clipHi N t c (lower δ j)) ≤ 1+2*D/δ := by
  obtain ⟨D,hD,hbudget⟩ := exists_complexWeight_Abel_budget
  refine ⟨D,hD,?_⟩
  intro δ hδ N t c j
  by_cases huv : clipLo N t c (lower δ j) ≤ clipHi N t c (lower δ j)
  · exact hbudget δ hδ j (lower δ j) _ _ (lower_pos δ j)
      (le_max_left _ _) huv (min_le_left _ _)
  · have hempty : Ioc (clipLo N t c (lower δ j))
        (clipHi N t c (lower δ j)) = ∅ :=
      Set.Ioc_eq_empty_of_le (le_of_not_ge huv)
    unfold profileAbelNorm
    rw [hempty, MeasureTheory.integral_empty, add_zero]
    exact (complexWeight_norm_le_one _ _ _).trans
      (by have := div_nonneg (show 0 ≤ 2*D by linarith) hδ.le; linarith)

/-- Sum of the actual head profiles over both original grid indices. -/
def headChartProfileCost (B N : ℕ) (t : ℕ × ℕ) (c : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (gridLength B N),
    ∑ _l ∈ Finset.range (gridLength B N),
      profileAbelNorm (complexWeight (boundaryLogMesh B N) j)
        (clipLo N t c (lower (boundaryLogMesh B N) j))
        (clipHi N t c (lower (boundaryLogMesh B N) j))

theorem exists_all_head_chart_profile_cost :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ B N : ℕ, 1 ≤ Real.log (N : ℝ) →
      ∀ t : ℕ × ℕ, ∀ c : ℕ,
      headChartProfileCost B N t c ≤
        9*(1+2*D)*(Real.log (N : ℝ))^(3*B+2) := by
  obtain ⟨D,hD,hactual⟩ := exists_actual_head_Abel_budget
  refine ⟨D,hD,?_⟩
  intro B N hlog t c
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hδ : 0 < boundaryLogMesh B N := by unfold boundaryLogMesh; positivity
  have hcost : 1+2*D/boundaryLogMesh B N ≤
      (1+2*D)*(Real.log (N : ℝ))^B := by
    unfold boundaryLogMesh
    simp only [one_div,div_eq_mul_inv,inv_inv]
    have hp : 1 ≤ (Real.log (N : ℝ))^B := one_le_pow₀ hlog
    nlinarith
  have hcard : (gridLength B N : ℝ)^2 ≤
      9*(Real.log (N : ℝ))^(2*(B+1)) := by
    simpa only [Finset.card_product,Finset.card_range,Nat.cast_mul,pow_two] using
      chosen_chart_count_le (B:=B) hlog
  calc
    _ ≤ ∑ _j ∈ Finset.range (gridLength B N),
          ∑ _l ∈ Finset.range (gridLength B N),
            (1+2*D)*(Real.log (N : ℝ))^B := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro l hl
      exact (hactual _ hδ N t c j).trans hcost
    _ = (gridLength B N : ℝ)^2*((1+2*D)*(Real.log (N : ℝ))^B) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      ring
    _ ≤ (9*(Real.log (N : ℝ))^(2*(B+1)))*
        ((1+2*D)*(Real.log (N : ℝ))^B) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [show 3*B+2=2*(B+1)+B by omega,pow_add]
      ring

/-- Literal mother occurrences, with repeated words counted repeatedly. -/
def originalMotherProfileCost (B N : ℕ) (t : ℕ × ℕ) : ℝ :=
  (originalMotherOccurrences.map (fun cs =>
    match cs with
    | [] => 0
    | c::_ => headChartProfileCost B N t c)).sum

theorem exists_original_mother_profile_cost :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ B N : ℕ, 1 ≤ Real.log (N : ℝ) →
      ∀ t : ℕ × ℕ,
      originalMotherProfileCost B N t ≤
        (originalMotherOccurrences.length : ℝ)*9*(1+2*D)*
          (Real.log (N : ℝ))^(3*B+2) := by
  obtain ⟨D,hD,hchart⟩ := exists_all_head_chart_profile_cost
  refine ⟨D,hD,?_⟩
  intro B N hlog t
  let C := 9*(1+2*D)*(Real.log (N : ℝ))^(3*B+2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlist : ∀ L : List (List ℕ),
      (L.map (fun cs => match cs with
        | [] => (0 : ℝ)
        | c::_ => headChartProfileCost B N t c)).sum ≤ (L.length : ℝ)*C := by
    intro L
    induction L with
    | nil => simp
    | cons cs L ih =>
      have hcs : (match cs with
          | [] => (0 : ℝ)
          | c::_ => headChartProfileCost B N t c) ≤ C := by
        cases cs with
        | nil => exact hC
        | cons c cs => exact hchart B N hlog t c
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith
  exact (hlist originalMotherOccurrences).trans_eq (by dsimp [C]; ring)

/-- The actual hat in the additive logarithmic (Euler/Mellin) variable. -/
def logHat (δ : ℝ) (j : ℕ) (u : ℝ) : ℝ := weight δ j (Real.exp u)

theorem logHat_eq_steps {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    logHat δ j = fun u =>
      P4B.smoothGateUpperStep δ (u-δ*(j : ℝ)) -
        P4B.smoothGateUpperStep δ (u-δ*((j : ℝ)+1)) := by
  funext u
  simp only [logHat,weight,Real.log_exp,hat,P4B.smoothGateUpperStep]
  have h₁ : u/δ-(j : ℝ)+1 = 1+(u-δ*(j : ℝ))/δ := by
    field_simp [hδ.ne']
    ring
  have h₂ : u/δ-(j : ℝ) = 1+(u-δ*((j : ℝ)+1))/δ := by
    field_simp [hδ.ne']
    ring
  rw [h₁,h₂]

/-- All orders for the very same hats. The derivative order is fixed
before width, label and argument, and hence before N. -/
theorem exists_logHat_derivative_budget (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ j : ℕ, ∀ u : ℝ,
      |iteratedDeriv k (logHat δ j) u| ≤ C/δ^k := by
  obtain ⟨C,hC,hbudget⟩ := P4B.exists_smoothGateUpperStep_derivative_budget k
  refine ⟨2*C,by linarith,?_⟩
  intro δ hδ j u
  have hshift (a : ℝ) :
      iteratedDeriv k (fun y => P4B.smoothGateUpperStep δ (y-a)) u =
        iteratedDeriv k (P4B.smoothGateUpperStep δ) (u-a) := by
    simpa only [one_pow,one_mul,sub_eq_add_neg,add_comm] using
      P4B.iteratedDeriv_comp_real_affine k (P4B.smoothGateUpperStep δ)
        (P4B.contDiff_smoothGateUpperStep δ) (-a) 1 u
  have hf (a : ℝ) :
      ContDiffAt ℝ k (fun y => P4B.smoothGateUpperStep δ (y-a)) u :=
    ((P4B.contDiff_smoothGateUpperStep δ).comp
      (contDiff_id.sub contDiff_const)).contDiffAt
  rw [logHat_eq_steps hδ]
  change |iteratedDeriv k ((fun y => P4B.smoothGateUpperStep δ (y-δ*(j : ℝ))) -
    (fun y => P4B.smoothGateUpperStep δ (y-δ*((j : ℝ)+1)))) u| ≤ _
  rw [iteratedDeriv_sub (hf _) (hf _),hshift,hshift]
  exact (abs_sub _ _).trans
    ((add_le_add (hbudget δ hδ _) (hbudget δ hδ _)).trans_eq (by ring))

theorem exists_chosen_logHat_derivative_budget (k B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 1 ≤ Real.log (N : ℝ) →
      ∀ j : ℕ, ∀ u : ℝ,
      |iteratedDeriv k (logHat (boundaryLogMesh B N) j) u| ≤
        C*(Real.log (N : ℝ))^(B*k) := by
  obtain ⟨C,hC,hbudget⟩ := exists_logHat_derivative_budget k
  refine ⟨C,hC,?_⟩
  intro N hlog j u
  have hδ : 0 < boundaryLogMesh B N := by unfold boundaryLogMesh; positivity
  apply (hbudget _ hδ j u).trans_eq
  unfold boundaryLogMesh
  simp only [one_div,inv_pow,div_eq_mul_inv,inv_inv]
  rw [← pow_mul]

end
end ImbalancedChen.P2GammaChosenLogGridBudget
