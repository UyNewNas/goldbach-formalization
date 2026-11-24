import ImbalancedChen.P2Winner9Row22Arithmetic
import Mathlib.Algebra.GCDMonoid.Finset

/-! Exact common denominators for the original rational vertex arrays. -/

namespace ImbalancedChen.P2Winner9RationalSimplexData

open ImbalancedChen.P2Winner9CurvatureExactMomentFloor (gapTotal)
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly (SimplexData)
open ImbalancedChen.P2Winner9Row22Arithmetic
  (RationalVertices VertexNormalization rawGap rawP rawY rawDeviation)

/-- The rational vertex arrays and their source positivity bounds. -/
structure Input where
  gaps : Fin 9 → ℚ
  p : Fin 9 → ℚ
  deviations : Fin 10 → Fin 9 → ℚ
  upper : ℚ
  maxima : Fin 10 → ℚ
  jensen : ℚ
  gaps_nonneg : ∀ i, 0 ≤ gaps i
  gaps_pos : 0 < ∑ i, gaps i
  upper_pos : 0 < upper
  p_le_upper : ∀ i, p i ≤ upper
  maxima_pos : ∀ j, 0 < maxima j
  jensen_nonneg : 0 ≤ jensen

private def commonDen {ι : Type*} [Fintype ι] (a : ι → ℚ) : ℕ :=
  Finset.univ.lcm (fun i => (a i).den)

private theorem commonDen_pos {ι : Type*} [Fintype ι] (a : ι → ℚ) :
    0 < commonDen a :=
  Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun i _ => (a i).den_ne_zero))

private theorem den_dvd_commonDen {ι : Type*} [Fintype ι] (a : ι → ℚ) (i : ι) :
    (a i).den ∣ commonDen a :=
  Finset.dvd_lcm (Finset.mem_univ i)

/-- Positive gap scale used to retain the original gap vertices. -/
def gapDen (a : Input) : ℕ := commonDen a.gaps

private def pDevDen (a : Input) : ℕ :=
  Nat.lcm (commonDen a.p) (commonDen (fun ij : Fin 10 × Fin 9 => a.deviations ij.1 ij.2))

/-- One positive scale for all P, deviation and upper-bound entries. -/
def scale (a : Input) : ℕ :=
  Nat.lcm (Nat.lcm a.upper.den (commonDen a.maxima)) (pDevDen a)

theorem scale_pos (a : Input) : 0 < scale a := by
  unfold scale pDevDen
  exact Nat.lcm_pos (Nat.lcm_pos a.upper.pos (commonDen_pos _))
    (Nat.lcm_pos (commonDen_pos _) (commonDen_pos _))

private theorem den_upper_dvd_scale (a : Input) : a.upper.den ∣ scale a :=
  (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _)

private theorem den_maxima_dvd_scale (a : Input) (j : Fin 10) :
    (a.maxima j).den ∣ scale a :=
  (den_dvd_commonDen _ _).trans ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _))

private theorem den_p_dvd_scale (a : Input) (i : Fin 9) : (a.p i).den ∣ scale a :=
  (den_dvd_commonDen _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _))

private theorem den_dev_dvd_scale (a : Input) (j : Fin 10) (i : Fin 9) :
    (a.deviations j i).den ∣ scale a :=
  (den_dvd_commonDen (fun ij : Fin 10 × Fin 9 => a.deviations ij.1 ij.2) (j, i)).trans
    ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _))

private def scaledInt (q : ℚ) (s : ℕ) : ℤ := q.num * (s / q.den : ℕ)

private theorem scaledInt_cast (q : ℚ) {s : ℕ} (hd : q.den ∣ s) :
    (scaledInt q s : ℚ) = q * (s : ℚ) := by
  obtain ⟨t, rfl⟩ := hd
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [scaledInt, Nat.mul_div_cancel_left t q.pos, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  calc
    _ = (((q.num : ℚ) / (q.den : ℚ)) * (q.den : ℚ)) * (t : ℚ) := by
      rw [div_mul_cancel₀ _ hden]
    _ = _ := by rw [q.num_div_den, mul_assoc]

private def scaledNat (q : ℚ) (s : ℕ) : ℕ := (scaledInt q s).toNat

private theorem scaledNat_cast (q : ℚ) (hq : 0 ≤ q) {s : ℕ} (hd : q.den ∣ s) :
    (scaledNat q s : ℚ) = q * (s : ℚ) := by
  have hn : 0 ≤ scaledInt q s := by
    exact_mod_cast (show 0 ≤ (scaledInt q s : ℚ) from
      scaledInt_cast q hd ▸ mul_nonneg hq (by positivity))
  rw [scaledNat, ← Int.cast_natCast, Int.toNat_of_nonneg hn, scaledInt_cast q hd]

private def yInt (a : Input) (i : Fin 9) : ℤ :=
  scaledInt a.upper (scale a) - scaledInt (a.p i) (scale a)

private theorem yInt_cast (a : Input) (i : Fin 9) :
    (yInt a i : ℚ) = (a.upper - a.p i) * (scale a : ℚ) := by
  rw [yInt, Int.cast_sub, scaledInt_cast _ (den_upper_dvd_scale a),
    scaledInt_cast _ (den_p_dvd_scale a i), sub_mul]

private theorem yNat_cast (a : Input) (i : Fin 9) :
    ((yInt a i).toNat : ℚ) = (a.upper - a.p i) * (scale a : ℚ) := by
  have hn : 0 ≤ yInt a i := by
    exact_mod_cast (show 0 ≤ (yInt a i : ℚ) from
      yInt_cast a i ▸ mul_nonneg (sub_nonneg.mpr (a.p_le_upper i)) (by positivity))
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, yInt_cast]

private theorem scaledGap_cast (a : Input) (i : Fin 9) :
    (scaledNat (a.gaps i) (gapDen a) : ℚ) = a.gaps i * (gapDen a : ℚ) :=
  scaledNat_cast _ (a.gaps_nonneg i) (den_dvd_commonDen _ _)

private theorem scaledGapSum_pos (a : Input) :
    0 < gapTotal (fun i => scaledNat (a.gaps i) (gapDen a)) := by
  have hgd : (0 : ℚ) < (gapDen a : ℚ) := by exact_mod_cast commonDen_pos a.gaps
  have hg : (0 : ℚ) < (gapTotal (fun i => scaledNat (a.gaps i) (gapDen a)) : ℚ) := by
    simp only [gapTotal, Nat.cast_sum, scaledGap_cast, ← Finset.sum_mul]
    exact mul_pos a.gaps_pos hgd
  exact_mod_cast hg

private theorem scaledNat_pos (q : ℚ) (hq : 0 < q) {s : ℕ} (hs : 0 < s) (hd : q.den ∣ s) :
    0 < scaledNat q s := by
  have hscale : (0 : ℚ) < (s : ℚ) := by exact_mod_cast hs
  have h : (0 : ℚ) < (scaledNat q s : ℚ) := by
    rw [scaledNat_cast q hq.le hd]
    exact mul_pos hq hscale
  exact_mod_cast h

/-- Executable typed source input with exact integer scales. -/
def toSimplexData (a : Input) : SimplexData where
  gaps i := scaledNat (a.gaps i) (gapDen a)
  y i := (yInt a i).toNat
  L := scale a
  U := scaledNat a.upper (scale a)
  deviations j i := scaledInt (a.deviations j i) (scale a)
  maxima j := scaledNat (a.maxima j) (scale a)
  jensenNum := a.jensen.num.toNat
  jensenDen := a.jensen.den
  gapsPos := scaledGapSum_pos a
  LPos := scale_pos a
  UPos := scaledNat_pos _ a.upper_pos (scale_pos a) (den_upper_dvd_scale a)
  maximaPos j := scaledNat_pos _ (a.maxima_pos j) (scale_pos a) (den_maxima_dvd_scale a j)
  jensenDenPos := a.jensen.pos

theorem gapDen_pos (a : Input) : 0 < gapDen a := commonDen_pos _

theorem gaps_eq (a : Input) (i : Fin 9) :
    a.gaps i = ((toSimplexData a).gaps i : ℚ) / (gapDen a : ℚ) := by
  have hgd : (gapDen a : ℚ) ≠ 0 := by exact_mod_cast (gapDen_pos a).ne'
  change a.gaps i = (scaledNat (a.gaps i) (gapDen a) : ℚ) / (gapDen a : ℚ)
  rw [scaledGap_cast, mul_div_cancel_right₀ _ hgd]

theorem upper_eq (a : Input) :
    a.upper = ((toSimplexData a).U : ℚ) / ((toSimplexData a).L : ℚ) := by
  have hs : (scale a : ℚ) ≠ 0 := by exact_mod_cast (scale_pos a).ne'
  change a.upper = (scaledNat a.upper (scale a) : ℚ) / (scale a : ℚ)
  rw [scaledNat_cast _ a.upper_pos.le (den_upper_dvd_scale a), mul_div_cancel_right₀ _ hs]

theorem maxima_eq (a : Input) (j : Fin 10) :
    a.maxima j = ((toSimplexData a).maxima j : ℚ) / ((toSimplexData a).L : ℚ) := by
  have hs : (scale a : ℚ) ≠ 0 := by exact_mod_cast (scale_pos a).ne'
  change a.maxima j = (scaledNat (a.maxima j) (scale a) : ℚ) / (scale a : ℚ)
  rw [scaledNat_cast _ (a.maxima_pos j).le (den_maxima_dvd_scale a j), mul_div_cancel_right₀ _ hs]

theorem deviations_eq (a : Input) (j : Fin 10) (i : Fin 9) :
    a.deviations j i = ((toSimplexData a).deviations j i : ℚ) / ((toSimplexData a).L : ℚ) := by
  have hs : (scale a : ℚ) ≠ 0 := by exact_mod_cast (scale_pos a).ne'
  change a.deviations j i = (scaledInt (a.deviations j i) (scale a) : ℚ) / (scale a : ℚ)
  rw [scaledInt_cast _ (den_dev_dvd_scale a j i), mul_div_cancel_right₀ _ hs]

theorem y_eq (a : Input) (i : Fin 9) :
    1 - a.p i / a.upper = ((toSimplexData a).y i : ℚ) / ((toSimplexData a).U : ℚ) := by
  have hs : (scale a : ℚ) ≠ 0 := by exact_mod_cast (scale_pos a).ne'
  change 1 - a.p i / a.upper =
    ((yInt a i).toNat : ℚ) / (scaledNat a.upper (scale a) : ℚ)
  rw [yNat_cast, scaledNat_cast _ a.upper_pos.le (den_upper_dvd_scale a),
    mul_div_mul_right _ _ hs, sub_div, div_self a.upper_pos.ne']

theorem jensen_eq (a : Input) :
    a.jensen = ((toSimplexData a).jensenNum : ℚ) / ((toSimplexData a).jensenDen : ℚ) := by
  change a.jensen = (a.jensen.num.toNat : ℚ) / (a.jensen.den : ℚ)
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr a.jensen_nonneg),
    Rat.num_div_den]

/-- Adapt the original rational physical arrays without rechecking any
moment or floor. Bounds on P and positivity are the only hypotheses. -/
def ofRawVertices (v : RationalVertices) (means : Fin 10 → ℚ) (upper : ℚ)
    (maxima : Fin 10 → ℚ) (jensen : ℚ) (hgap : ∀ i, 0 ≤ rawGap v i)
    (hgapSum : 0 < ∑ i, rawGap v i) (hupper : 0 < upper)
    (hp : ∀ i, rawP v means i ≤ upper) (hmaxima : ∀ j, 0 < maxima j)
    (hjensen : 0 ≤ jensen) : Input where
  gaps := rawGap v
  p := rawP v means
  deviations j i := rawDeviation v means i j
  upper := upper
  maxima := maxima
  jensen := jensen
  gaps_nonneg := hgap
  gaps_pos := hgapSum
  upper_pos := hupper
  p_le_upper := hp
  maxima_pos := hmaxima
  jensen_nonneg := hjensen

theorem ofRawVertices_normalization (v : RationalVertices) (means : Fin 10 → ℚ) (upper : ℚ)
    (maxima : Fin 10 → ℚ) (jensen : ℚ) (hgap : ∀ i, 0 ≤ rawGap v i)
    (hgapSum : 0 < ∑ i, rawGap v i) (hupper : 0 < upper)
    (hp : ∀ i, rawP v means i ≤ upper) (hmaxima : ∀ j, 0 < maxima j)
    (hjensen : 0 ≤ jensen) :
    let a := ofRawVertices v means upper maxima jensen hgap hgapSum hupper hp hmaxima hjensen
    VertexNormalization v means upper (toSimplexData a) (gapDen a) := by
  let a := ofRawVertices v means upper maxima jensen hgap hgapSum hupper hp hmaxima hjensen
  change VertexNormalization v means upper (toSimplexData a) (gapDen a)
  exact ⟨gapDen_pos a, fun i => ⟨gaps_eq a i, y_eq a i, fun j => deviations_eq a j i⟩⟩

end ImbalancedChen.P2Winner9RationalSimplexData
