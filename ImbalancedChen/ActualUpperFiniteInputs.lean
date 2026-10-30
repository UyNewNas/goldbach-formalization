import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.RealHalfProductMassSplit
import ImbalancedChen.EnlargedSelbergCap

/-! Uncompiled verbatim finite coefficient/gate extraction candidate. -/
namespace ImbalancedChen
noncomputable section
open Filter Topology

/-- A positive exponent gap pays the natural ceiling at the manuscript's
literal lower product cutoff `2 * N^(1-kappa)`. -/
theorem eventually_manuscript_sieve_gate
    {b kappa theta : ℝ} (hb : 0 < b) (htheta : 0 ≤ theta)
    (hgap : theta < (1 - kappa) * (b / (1 + b))) :
    ∀ᶠ N : ℕ in atTop,
      0 < manuscriptHalfProductCutoff kappa N ∧
        (Nat.ceil ((N : ℝ) ^ theta) : ℝ) ≤
          (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) := by
  have halpha : 0 ≤ b / (1 + b) := div_nonneg hb.le (by linarith)
  filter_upwards [eventually_floor_rpow_add_one_le_rpow htheta hgap,
    eventually_ge_atTop (1 : ℕ)] with N hround hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hpow : 0 < (N : ℝ) ^ (1 - kappa) := Real.rpow_pos_of_pos hNpos _
  refine ⟨mul_pos (by norm_num) hpow, ?_⟩
  calc
    (Nat.ceil ((N : ℝ) ^ theta) : ℝ) ≤
        (Nat.floor ((N : ℝ) ^ theta) : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one ((N : ℝ) ^ theta)
    _ ≤ (N : ℝ) ^ ((1 - kappa) * (b / (1 + b))) := hround
    _ = ((N : ℝ) ^ (1 - kappa)) ^ (b / (1 + b)) :=
      Real.rpow_mul hNpos.le _ _
    _ ≤ (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) := by
      apply Real.rpow_le_rpow hpow.le _ halpha
      change (N : ℝ) ^ (1 - kappa) ≤ 2 * (N : ℝ) ^ (1 - kappa)
      linarith

/-- The exact finite modulus set of the attached coefficient. -/
def attachedUpperModuli (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  actualSmallRoughModuli (retain N) N (cap N)
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))

/-- The same coefficient is used for the majorant, density and error. -/
def attachedUpperCoefficient (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool)
    (cap : ℕ → ℕ) (N d : ℕ) : ℝ :=
  actualSmallRoughRho (retain N) N (cap N)
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
    ((N : ℝ) ^ (nu * epsilon)) d

end
end ImbalancedChen
