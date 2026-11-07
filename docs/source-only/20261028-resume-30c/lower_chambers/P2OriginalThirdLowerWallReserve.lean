import ImbalancedChen.P2OriginalStrictWLocalRationalCover
import ImbalancedChen.AffinePrimeWallReserve
import ImbalancedChen.P1ActualMovingAffineWallUnion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual third lower order/gate/winner boundaries are a finite family of
proved nonzero linear forms at the original heights. Distinct masks are
used for same-side tent ties; identical expressions are kept as structural
inherit chambers and are never declared null. Lebesgue nullity and the
actual arithmetic strip reserve are separate conclusions.
-/

namespace ImbalancedChen.P2OriginalThirdLowerWallReserve

noncomputable section
open scoped Classical BigOperators Topology
open Set MeasureTheory Filter
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerOrderedWBranch
open P2OriginalStrictWLocalRationalCover

abbrev LinearForm := Point →L[ℝ] ℝ

def coord (i : Fin 3) : LinearForm := ContinuousLinearMap.proj i

def maskSum (I : ProperMask) : LinearForm := ∑ i ∈ I.val, coord i

@[simp] theorem coord_apply (i : Fin 3) (x : Point) : coord i x = x i := rfl

@[simp] theorem maskSum_apply (I : ProperMask) (x : Point) :
    maskSum I x = ∑ i ∈ I.val, x i := by simp [maskSum]

private theorem maskSum_single (I : ProperMask) (i : Fin 3) :
    maskSum I (Pi.single i (1 : ℝ)) = if i ∈ I.val then 1 else 0 := by
  simp [maskSum_apply, Pi.single_apply]

private theorem scaled_mask_ne_zero (I : ProperMask) (c : ℝ) (hc : c ≠ 0) :
    c • maskSum I ≠ 0 := by
  obtain ⟨i, hi⟩ := I.property
  intro h
  have he := congrArg (fun L : LinearForm => L (Pi.single i (1 : ℝ))) h
  have hz : c = 0 := by simpa [maskSum_single, hi] using he
  exact hc hz

-- Ordinary lower cutoff, order, original first-square/second-cube,
-- inherited/W equality and activation equality. The actual rho appears
-- only in heights; no ideal-parent substitution is made.
def basicForm : Fin 9 → LinearForm :=
  ![coord 2, coord 0, coord 0, coord 1 - coord 2, coord 0 - coord 1,
    2 • coord 0, coord 0 + 3 • coord 1,
    (3 / 8 : ℝ) • coord 2, (1 / 2 : ℝ) • coord 0 + (3 / 8 : ℝ) • coord 2]

def basicHeight (S : CompactStart) (rho : ℝ) : Fin 9 → ℝ :=
  ![S.epsilon, startCutoff S.start, mu, 0, 0,
    baselineCap rho, baselineCap rho,
    Lambda - baselineCap rho, Lambda - 1 / 2]

theorem basicForm_ne_zero (j : Fin 9) : basicForm j ≠ 0 := by
  intro hz
  have he := congrArg (fun L : LinearForm => L ![(1 : ℝ), 2, 3]) hz
  fin_cases j <;> norm_num [basicForm, coord] at he

-- Fin5 labels: W=left tent, W=right tent, tent bend,
-- inherited=left tent, inherited=right tent.
def maskForm (j : Fin 5) (I : ProperMask) : LinearForm :=
  ![(1 / 2 : ℝ) • maskSum I + (3 / 8 : ℝ) • coord 2,
    (-3 / 2 : ℝ) • maskSum I + (3 / 8 : ℝ) • coord 2,
    maskSum I, (1 / 2 : ℝ) • maskSum I, (-3 / 2 : ℝ) • maskSum I] j

def maskHeight (rho : ℝ) (j : Fin 5) : ℝ :=
  ![Lambda - 1 / 2, Lambda - 57 / 64, mu,
    baselineCap rho - 1 / 2, baselineCap rho - 57 / 64] j

theorem maskForm_ne_zero (j : Fin 5) (I : ProperMask) : maskForm j I ≠ 0 := by
  fin_cases j
  · intro hz
    have he := congrArg (fun L : LinearForm => L (Pi.single 2 (1 : ℝ))) hz
    by_cases h2 : (2 : Fin 3) ∈ I.val <;>
      norm_num [maskForm, maskSum_single, h2, coord, Pi.single_apply] at he
  · intro hz
    have he := congrArg (fun L : LinearForm => L (Pi.single 2 (1 : ℝ))) hz
    by_cases h2 : (2 : Fin 3) ∈ I.val <;>
      norm_num [maskForm, maskSum_single, h2, coord, Pi.single_apply] at he
  · simpa [maskForm] using scaled_mask_ne_zero I 1 (by norm_num)
  · simpa [maskForm] using scaled_mask_ne_zero I (1 / 2) (by norm_num)
  · simpa [maskForm] using scaled_mask_ne_zero I (-3 / 2) (by norm_num)

-- A left tent on I and a right tent on J tie at this positive-slope form.
def crossForm (I J : ProperMask) : LinearForm :=
  (1 / 2 : ℝ) • maskSum I + (3 / 2 : ℝ) • maskSum J

theorem crossForm_ne_zero (I J : ProperMask) : crossForm I J ≠ 0 := by
  obtain ⟨i, hi⟩ := I.property
  intro hz
  have he := congrArg (fun L : LinearForm => L (Pi.single i (1 : ℝ))) hz
  by_cases hj : i ∈ J.val <;>
    norm_num [crossForm, maskSum_single, hi, hj] at he

abbrev DistinctMasks := {p : ProperMask × ProperMask // p.1.val ≠ p.2.val}

def sameSideForm (p : DistinctMasks) : LinearForm := maskSum p.val.1 - maskSum p.val.2

theorem sameSideForm_ne_zero (p : DistinctMasks) : sameSideForm p ≠ 0 := by
  intro hz
  apply p.property
  apply Finset.ext
  intro i
  have he := congrArg (fun L : LinearForm => L (Pi.single i (1 : ℝ))) hz
  by_cases hi : i ∈ p.val.1.val <;> by_cases hj : i ∈ p.val.2.val <;>
    simp [sameSideForm, maskSum_single, hi, hj] at he ⊢

abbrev WallIndex := Fin 9 ⊕ (Fin 5 × ProperMask) ⊕
  (ProperMask × ProperMask) ⊕ DistinctMasks

def wallForm : WallIndex → LinearForm
  | .inl j => basicForm j
  | .inr (.inl p) => maskForm p.1 p.2
  | .inr (.inr (.inl p)) => crossForm p.1 p.2
  | .inr (.inr (.inr p)) => sameSideForm p

def wallHeight (S : CompactStart) (rho : ℝ) : WallIndex → ℝ
  | .inl j => basicHeight S rho j
  | .inr (.inl p) => maskHeight rho p.1
  | .inr (.inr (.inl _)) => 25 / 64
  | .inr (.inr (.inr _)) => 0

theorem wallForm_ne_zero (j : WallIndex) : wallForm j ≠ 0 := by
  rcases j with j | j
  · exact basicForm_ne_zero j
  · rcases j with p | j
    · exact maskForm_ne_zero p.1 p.2
    · rcases j with p | p
      · exact crossForm_ne_zero p.1 p.2
      · exact sameSideForm_ne_zero p

def actualWalls (S : CompactStart) (rho : ℝ) : Set Point :=
  {x | ∃ j : WallIndex, wallForm j x = wallHeight S rho j}

def basicEqualities (S : CompactStart) (rho : ℝ) (x : Point) : Fin 9 → Prop :=
  ![x 2 = S.epsilon, x 0 = (startCutoff S.start : ℝ), x 0 = mu,
    x 1 = x 2, x 0 = x 1, 2 * x 0 = baselineCap rho,
    x 0 + 3 * x 1 = baselineCap rho,
    B (x 2) = baselineCap rho, B (x 2) = A (x 0)]

theorem basic_equalities_iff (S : CompactStart) (rho : ℝ)
    (x : Point) (j : Fin 9) :
    basicEqualities S rho x j ↔ basicForm j x = basicHeight S rho j := by
  fin_cases j <;>
    simp [basicEqualities, basicForm, basicHeight, A, B] <;>
    constructor <;> intro h <;> linarith

theorem basic_equality_mem_actualWalls (S : CompactStart) (rho : ℝ)
    (x : Point) (j : Fin 9) (hj : basicEqualities S rho x j) :
    x ∈ actualWalls S rho :=
  ⟨.inl j, (basic_equalities_iff S rho x j).mp hj⟩

-- The nonlinear min equality is covered by the two actual affine pieces.
-- Neither tent side is treated as globally dominant.
theorem W_tent_equality_mem_actualWalls (S : CompactStart) (rho : ℝ)
    (x : Point) (I : ProperMask)
    (h : B (x 2) = v (∑ i ∈ I.val, x i)) : x ∈ actualWalls S rho := by
  let s := ∑ i ∈ I.val, x i
  by_cases hAC : A s ≤ C s
  · have he : B (x 2) = A s := by simpa [v, s, min_eq_left hAC] using h
    refine ⟨.inr (.inl (0, I)), ?_⟩
    simp [wallForm, wallHeight, maskForm, maskHeight, s]
    dsimp [A, B] at he
    linarith
  · have hCA : C s ≤ A s := le_of_lt (lt_of_not_ge hAC)
    have he : B (x 2) = C s := by simpa [v, s, min_eq_right hCA] using h
    refine ⟨.inr (.inl (1, I)), ?_⟩
    simp [wallForm, wallHeight, maskForm, maskHeight, s]
    dsimp [B, C] at he
    linarith

theorem actualWalls_volume_zero (S : CompactStart) (rho : ℝ) :
    volume (actualWalls S rho) = 0 := by
  have hwall : ∀ j : WallIndex,
      volume {x : Point | wallForm j x = wallHeight S rho j} = 0 := fun j =>
    affinePrimeWall_volume_zero (wallForm j) (wallForm_ne_zero j) (wallHeight S rho j)
  have heq : actualWalls S rho =
      ⋃ j : WallIndex, {x : Point | wallForm j x = wallHeight S rho j} := by
    ext x
    simp [actualWalls]
  rw [heq]
  exact measure_iUnion_null hwall

theorem restricted_actualWalls_volume_zero (S : CompactStart) (rho : ℝ)
    (K : Set Point) : volume (K ∩ actualWalls S rho) = 0 :=
  measure_mono_null Set.inter_subset_right (actualWalls_volume_zero S rho)

-- Convert the concrete finite source index to the existing reserve API.
-- This is a data reindexing, not an assumed small-mass result.
def finiteForms : Fin (Fintype.card WallIndex) → LinearForm :=
  fun j => wallForm ((Fintype.equivFin WallIndex).symm j)

def finiteHeights (S : CompactStart) (rho : ℝ) :
    Fin (Fintype.card WallIndex) → ℝ :=
  fun j => wallHeight S rho ((Fintype.equivFin WallIndex).symm j)

theorem finiteForms_ne_zero (j : Fin (Fintype.card WallIndex)) :
    finiteForms j ≠ 0 := wallForm_ne_zero _

theorem actualWalls_iff_finite (S : CompactStart) (rho : ℝ) (x : Point) :
    x ∈ actualWalls S rho ↔
      ∃ j : Fin (Fintype.card WallIndex), finiteForms j x = finiteHeights S rho j := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨Fintype.equivFin WallIndex j, ?_⟩
    simpa only [finiteForms, finiteHeights, Equiv.symm_apply_apply] using hj
  · rintro ⟨j, hj⟩
    exact ⟨(Fintype.equivFin WallIndex).symm j, hj⟩

theorem actualWalls_subset_positive_strip (S : CompactStart) (rho delta : ℝ)
    (hdelta : 0 ≤ delta) :
    actualWalls S rho ⊆ primeAffineWallStrip finiteForms (finiteHeights S rho) delta := by
  intro x hx
  obtain ⟨j, hj⟩ := (actualWalls_iff_finite S rho x).mp hx
  refine ⟨j, ?_⟩
  rw [hj]
  simpa using hdelta

-- The carrier remains actualPrimeBoxTuples, with its target-linked prime
-- exclusions. Exact-wall atoms are retained and counted explicitly.
def actualLowerExactWallMass (S : CompactStart) (rho : ℝ)
    (N : ℕ) (a b : Fin 3 → ℝ) : ℝ :=
  ∑ p ∈ (actualPrimeBoxTuples N a b).filter
    (fun p => actualPrimeTupleLog N p ∈ actualWalls S rho),
      P1ActualMovingAffineWallMass.tupleWeight p

theorem actualLowerExactWallMass_eq_unionMass (S : CompactStart) (rho : ℝ)
    (N : ℕ) (a b : Fin 3 → ℝ) :
    actualLowerExactWallMass S rho N a b =
      P1ActualMovingAffineWallUnion.unionMass N a b finiteForms (finiteHeights S rho) := by
  unfold actualLowerExactWallMass P1ActualMovingAffineWallUnion.unionMass
    P1ActualMovingAffineWallUnion.unionTuples P1ActualMovingAffineWallUnion.OnWallUnion
  simp only [actualWalls_iff_finite]

-- Real-null walls can carry prime atoms. The original finite arithmetic
-- mass is controlled by the existing true PNT/Mertens strip theorem:
-- select a positive width first, then one target threshold, with the same
-- target-deleted prime carrier and reciprocal-totient tuple weights.
theorem exists_actual_lower_wall_strip_reserve (S : CompactStart) (rho : ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        actualPrimeAffineWallStripMass N (fun _ : Fin 3 => a) (fun _ => b)
          finiteForms (finiteHeights S rho) delta < eta := by
  exact exists_actualPrimeAffineWallStrip_mass_lt ha hab
    finiteForms (finiteHeights S rho) finiteForms_ne_zero eta heta

theorem actual_exact_wall_mass_tends_zero (S : CompactStart) (rho : ℝ)
    (a b : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) :
    Tendsto (fun N : ℕ => P1ActualMovingAffineWallUnion.unionMass
      N a b finiteForms (finiteHeights S rho)) atTop (𝓝 0) := by
  exact P1ActualMovingAffineWallUnion.tendsto_unionMass_moving a b ha hab
    finiteForms finiteForms_ne_zero (fun _ => finiteHeights S rho)

theorem actual_lower_exact_wall_mass_tends_zero (S : CompactStart) (rho : ℝ)
    (a b : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) :
    Tendsto (fun N : ℕ => actualLowerExactWallMass S rho N a b)
      atTop (𝓝 0) := by
  simp only [actualLowerExactWallMass_eq_unionMass]
  exact actual_exact_wall_mass_tends_zero S rho a b ha hab

end
end ImbalancedChen.P2OriginalThirdLowerWallReserve
