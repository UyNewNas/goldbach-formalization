import ImbalancedChen.ActualExtendedThirdWholeCellActions
import ImbalancedChen.ActualDwellSelectedRemainder

/-!
# Moving-residue parameters for the actual selected pair

The spectral exponent is the manuscript's fixed 7/32.  The residue
exponent is 1+3κ.  The pair parameter is the already chosen constant at
the original coarse-cell representative.  Its whole-cell gate and endpoint
margins pay the moving-residue critical interval and the actual integer
initial square gate, at the inflated source level θ-2δ.

The original support is supplied only at the actual policy level λ.
Its inflation to θ-2δ, the selected remainder budget, and the deterministic
greedy factors are derived here.  The C≥1 branch is explicit.  The separate
full-vector C<1 repair and its three analytic monomial estimates, fixed
box slot partitions, and a same-policy arithmetic mean are not conclusions.
-/

namespace ImbalancedChen

noncomputable section

open Set
open VariableEnvelope

/-- The literal three-term selected-subproduct endpoint at spectral 7/32. -/
def actualSelectedSubproductV (α s : ℝ) : ℝ :=
  min ((1 + s) / 2) (min ((32 - 34 * s) / 39)
    (1 - 7 * α / 64 - 3 * s / 2))

/-- The two original upper bounds for the selected logarithmic product. -/
def actualSelectedSubproductUpper (α θ : ℝ) : ℝ :=
  min ((32 - 39 * θ) / 34) ((2 - 2 * θ - 7 * α / 32) / 3)

theorem actualSelectedSubproductV_one (s : ℝ) :
    actualSelectedSubproductV 1 s = v s := by
  unfold actualSelectedSubproductV v A C
  congr 2 <;> ring

/-- Exact inversion of the manuscript's critical interval, retaining both
upper constraints.  This is valid for every real residue exponent. -/
theorem actualSelectedSubproduct_critical_iff (α θ s : ℝ) :
    θ ≤ actualSelectedSubproductV α s ↔
      2 * θ - 1 ≤ s ∧ s ≤ actualSelectedSubproductUpper α θ := by
  simp only [actualSelectedSubproductV, actualSelectedSubproductUpper,
    le_min_iff]
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨by linarith, by linarith, by linarith⟩

/-- The actual α=1+3κ loss is paid from the existing e/4 endpoint margin.
The same θ retains an e/8 surplus after the perturbation. -/
theorem actualSelectedSubproductV_residue_margin {e κ θ s : ℝ}
    (he : 0 ≤ e) (hκ : κ ≤ e / 4) (hθ : θ + e / 4 ≤ v s) :
    θ + e / 8 ≤ actualSelectedSubproductV (1 + 3 * κ) s := by
  have ha := hθ.trans (min_le_left _ _)
  have hb := hθ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc := hθ.trans ((min_le_right _ _).trans (min_le_right _ _))
  change θ + e / 4 ≤ A s at ha
  change θ + e / 4 ≤ (32 - 34 * s) / 39 at hb
  change θ + e / 4 ≤ C s at hc
  unfold actualSelectedSubproductV
  refine le_min ?_ (le_min ?_ ?_)
  · dsimp [A] at ha
    linarith
  · linarith
  · dsimp [C] at hc
    linarith

/-- These coordinates are computed from the actual integer slots. -/
def actualSelectedPrimeCoordinates (x : ℝ) (p : Fin 3 → ℕ) : Fin 3 → ℝ :=
  fun i => Real.log (p i : ℝ) / Real.log x

theorem rpow_actualSelectedPrimeCoordinates (x : ℝ) (hx : 1 < x)
    (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i) (i : Fin 3) :
    x ^ actualSelectedPrimeCoordinates x p i = (p i : ℝ) := by
  have hpi : (0 : ℝ) < p i := by exact_mod_cast hp i
  unfold actualSelectedPrimeCoordinates
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx),
    mul_div_cancel₀ _ (Real.log_pos hx).ne', Real.exp_log hpi]

/-- `false` is p₁p₃, and `true` is p₂p₃, matching winning indices 6 and 7. -/
def actualSelectedPairProduct (yz : Bool) (p : Fin 3 → ℕ) : ℕ :=
  if yz then p 1 * p 2 else p 0 * p 2

def actualSelectedPairRemainingPrime (yz : Bool) (p : Fin 3 → ℕ) : ℕ :=
  if yz then p 0 else p 1

private theorem actualSelectedPairProduct_rpow (x : ℝ) (hx : 1 < x)
    (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i) (yz : Bool) :
    x ^ (if yz then actualSelectedPrimeCoordinates x p 1 + actualSelectedPrimeCoordinates x p 2
      else actualSelectedPrimeCoordinates x p 0 + actualSelectedPrimeCoordinates x p 2) =
      (actualSelectedPairProduct yz p : ℝ) := by
  cases yz <;> simp [actualSelectedPairProduct,
    Real.rpow_add (zero_lt_one.trans hx), rpow_actualSelectedPrimeCoordinates x hx p hp]

private theorem actualSelectedPairGate_rpow (x : ℝ) (hx : 1 < x)
    (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i) (yz : Bool) :
    (actualSelectedPairProduct yz p : ℝ) *
        (actualSelectedPairRemainingPrime yz p : ℝ) ^ 2 =
      x ^ (if yz then 2 * actualSelectedPrimeCoordinates x p 0 +
          actualSelectedPrimeCoordinates x p 1 + actualSelectedPrimeCoordinates x p 2
        else actualSelectedPrimeCoordinates x p 0 +
          2 * actualSelectedPrimeCoordinates x p 1 + actualSelectedPrimeCoordinates x p 2) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hpow := rpow_actualSelectedPrimeCoordinates x hx p hp
  cases yz
  · change ((p 0 * p 2 : ℕ) : ℝ) * (p 1 : ℝ) ^ 2 = _
    rw [Nat.cast_mul, ← hpow 0, ← hpow 1, ← hpow 2,
      ← Real.rpow_mul_natCast hxpos.le, ← Real.rpow_add hxpos,
      ← Real.rpow_add hxpos]
    congr 1
    ring
  · change ((p 1 * p 2 : ℕ) : ℝ) * (p 0 : ℝ) ^ 2 = _
    rw [Nat.cast_mul, ← hpow 0, ← hpow 1, ← hpow 2,
      ← Real.rpow_mul_natCast hxpos.le, ← Real.rpow_add hxpos,
      ← Real.rpow_add hxpos]
    congr 1
    ring

/-- All arithmetic premises for this actual chosen pair are paid from its
whole-cell margins and the original policy support.  In particular callers
do not supply a remainder-square predicate or an extra pair gate. -/
theorem actualExtendedThirdSelectedPair_arithmeticInputs {e κ δ : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hκ : κ ≤ e / 4) (hδ : δ ≤ e / 32)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (x : ℝ) (hx : 1 < x) (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i)
    (hs : actualSelectedPrimeCoordinates x p ∈ actualExtendedThirdPhysicalCell m j)
    (tail : List ℕ)
    (hsupport : actualDwellSupport (x ^ actualExtendedThirdPhysicalLevel e m j)
      (p 0 :: p 1 :: p 2 :: tail)) :
    let θ := actualExtendedThirdPairParameter e m j t yz
    actualDwellSupport (x ^ (θ - 2 * δ)) (p 0 :: p 1 :: p 2 :: tail) ∧
      (actualSelectedPairProduct yz p : ℝ) *
        (actualSelectedPairRemainingPrime yz p : ℝ) ^ 2 < x ^ (θ - 2 * δ) ∧
      x ^ (2 * θ - 1) ≤ (actualSelectedPairProduct yz p : ℝ) ∧
      (actualSelectedPairProduct yz p : ℝ) ≤
        x ^ actualSelectedSubproductUpper (1 + 3 * κ) θ := by
  obtain ⟨_, _, hλ, hcell⟩ := actualExtendedThirdSelectedPair_wholeCell
    he0 he hmesh hfull ht yz hk
  obtain ⟨hgate, hend⟩ := hcell _ hs
  have hpert := actualSelectedSubproductV_residue_margin he0.le hκ hend
  have hcrit := (actualSelectedSubproduct_critical_iff _ _ _).mp
    (show actualExtendedThirdPairParameter e m j t yz ≤
      actualSelectedSubproductV (1 + 3 * κ)
        (if yz then actualSelectedPrimeCoordinates x p 1 + actualSelectedPrimeCoordinates x p 2
          else actualSelectedPrimeCoordinates x p 0 + actualSelectedPrimeCoordinates x p 2) by
      linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (hsupport i hi).trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  · rw [actualSelectedPairGate_rpow x hx p hp yz]
    apply Real.rpow_lt_rpow_of_exponent_lt hx
    linarith
  · rw [← actualSelectedPairProduct_rpow x hx p hp yz]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hcrit.1
  · rw [← actualSelectedPairProduct_rpow x hx p hp yz]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hcrit.2

/-- The chosen pair and the actual prefer-left factors consume those paid
premises.  The source product, selected pair, parameter, and cell are the
same as in the original policy; only the source support level is inflated. -/
theorem actualExtendedThirdSelectedPair_allocate {e κ δ A : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hκ : κ ≤ e / 4) (hδ : δ ≤ e / 32)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (x : ℝ) (hx : 1 < x) (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i)
    (hs : actualSelectedPrimeCoordinates x p ∈ actualExtendedThirdPhysicalCell m j)
    (tail : List ℕ)
    (hsupport : actualDwellSupport (x ^ actualExtendedThirdPhysicalLevel e m j)
      (p 0 :: p 1 :: p 2 :: tail)) (hA : 1 ≤ A)
    (hC : 1 ≤ x ^ (actualExtendedThirdPairParameter e m j t yz - 2 * δ) /
      (A * (actualSelectedPairProduct yz p : ℝ))) :
    let θ := actualExtendedThirdPairParameter e m j t yz
    let b₀ := actualSelectedPairProduct yz p
    let ac := actualTwoCapacityFactors A (actualSelectedPairRemainingPrime yz p :: tail)
    ac.1 * b₀ * ac.2 = (p 0 :: p 1 :: p 2 :: tail).prod ∧
      (ac.1 : ℝ) ≤ A ∧ (ac.2 : ℝ) ≤ x ^ (θ - 2 * δ) / (A * b₀) := by
  obtain ⟨hsupport', hgate, _, _⟩ := actualExtendedThirdSelectedPair_arithmeticInputs
    he0 he hκ hδ hmesh hfull ht yz hk x hx p hp hs tail hsupport
  cases yz
  · apply actualDwell_selected_p1p3_allocate hA (p 0) (p 1) (p 2) tail
      (hp 0) (hp 2) hsupport' ?_ hC
    calc
      (p 0 : ℝ) * (p 1 : ℝ) ^ 2 * p 2 =
          ((p 0 * p 2 : ℕ) : ℝ) * (p 1 : ℝ) ^ 2 := by rw [Nat.cast_mul]; ring
      _ ≤ _ := hgate.le
  · apply actualDwell_selected_p2p3_allocate hA (p 0) (p 1) (p 2) tail
      (hp 1) (hp 2) hsupport' ?_ hC
    calc
      (p 0 : ℝ) ^ 2 * p 1 * p 2 =
          ((p 1 * p 2 : ℕ) : ℝ) * (p 0 : ℝ) ^ 2 := by rw [Nat.cast_mul]; ring
      _ ≤ _ := hgate.le

end

end ImbalancedChen
