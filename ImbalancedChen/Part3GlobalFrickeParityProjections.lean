import ImbalancedChen.Part3GlobalFrickeFriedrichsIntertwining

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

Literal (Id +/- actualFricke)/2 on the original global quotient L2 and
the original completed energy space. Algebraic involution and the derived
self-adjoint pairing identity prove complementary idempotence, adjoint
symmetry, orthogonality and exact norm splitting. Their ranges are exactly
the CLOSED actual +/- eigenspaces. These are global Hilbert projections,
not pointwise Eisenstein channels or a spectral-completeness assertion.
-/

noncomputable section

namespace ImbalancedChen.Part3.InvolutiveHilbertProjection20261026b

open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def plus (W : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ H + W)

def minus (W : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ H - W)

theorem plus_apply (W : H →L[ℂ] H) (f : H) : plus W f = (1 / 2 : ℂ) • (f + W f) := rfl
theorem minus_apply (W : H →L[ℂ] H) (f : H) : minus W f = (1 / 2 : ℂ) • (f - W f) := rfl

theorem plus_eigen (W : H →L[ℂ] H) (hW : Function.Involutive W) (f : H) :
    W (plus W f) = plus W f := by
  rw [plus_apply, map_smul, map_add, hW f, add_comm (W f) f]

theorem minus_eigen (W : H →L[ℂ] H) (hW : Function.Involutive W) (f : H) :
    W (minus W f) = -minus W f := by
  rw [minus_apply, map_smul, map_sub, hW f, ← smul_neg, neg_sub]

theorem plus_of_eigen (W : H →L[ℂ] H) {f : H} (hf : W f = f) : plus W f = f := by
  rw [plus_apply, hf, ← two_smul ℂ f, smul_smul]
  norm_num

theorem minus_of_eigen (W : H →L[ℂ] H) {f : H} (hf : W f = -f) : minus W f = f := by
  rw [minus_apply, hf, sub_neg_eq_add, ← two_smul ℂ f, smul_smul]
  norm_num

theorem plus_add_minus (W : H →L[ℂ] H) (f : H) : plus W f + minus W f = f := by
  rw [plus_apply, minus_apply, ← smul_add]
  have h : (f + W f) + (f - W f) = f + f := by abel
  rw [h, ← two_smul ℂ f, smul_smul]
  norm_num

theorem plus_idempotent (W : H →L[ℂ] H) (hW : Function.Involutive W) :
    IsIdempotentElem (plus W) := by
  ext f
  exact plus_of_eigen W (plus_eigen W hW f)

theorem minus_idempotent (W : H →L[ℂ] H) (hW : Function.Involutive W) :
    IsIdempotentElem (minus W) := by
  ext f
  exact minus_of_eigen W (minus_eigen W hW f)

theorem projections_orthogonal (W : H →L[ℂ] H) (hW : Function.Involutive W)
    (hS : ∀ f g : H, inner ℂ (W f) g = inner ℂ f (W g)) (f g : H) :
    inner ℂ (plus W f) (minus W g) = 0 := by
  have h := hS (plus W f) (minus W g)
  rw [plus_eigen W hW, minus_eigen W hW, inner_neg_right] at h
  have hz : inner ℂ (plus W f) (minus W g) + inner ℂ (plus W f) (minus W g) = 0 :=
    eq_neg_iff_add_eq_zero.mp h
  have htwo : (2 : ℂ) * inner ℂ (plus W f) (minus W g) = 0 := by
    rw [two_mul]
    exact hz
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem plus_selfAdjoint (W : H →L[ℂ] H)
    (hS : ∀ f g : H, inner ℂ (W f) g = inner ℂ f (W g)) : IsSelfAdjoint (plus W) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hc : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num [Complex.star_def]
  change inner ℂ (plus W f) g = inner ℂ f (plus W g)
  simp only [plus_apply, inner_smul_left, inner_add_left, inner_smul_right, inner_add_right, hc, hS f g]

theorem minus_selfAdjoint (W : H →L[ℂ] H)
    (hS : ∀ f g : H, inner ℂ (W f) g = inner ℂ f (W g)) : IsSelfAdjoint (minus W) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hc : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num [Complex.star_def]
  change inner ℂ (minus W f) g = inner ℂ f (minus W g)
  simp only [minus_apply, inner_smul_left, inner_sub_left, inner_smul_right, inner_sub_right, hc, hS f g]

def plusSpace (W : H →L[ℂ] H) : Submodule ℂ H := (W - ContinuousLinearMap.id ℂ H).ker
def minusSpace (W : H →L[ℂ] H) : Submodule ℂ H := (W + ContinuousLinearMap.id ℂ H).ker

theorem plusSpace_closed (W : H →L[ℂ] H) : IsClosed (plusSpace W : Set H) := by
  change IsClosed {f : H | W f - f = 0}
  exact isClosed_eq (W.continuous.sub continuous_id) continuous_const

theorem minusSpace_closed (W : H →L[ℂ] H) : IsClosed (minusSpace W : Set H) := by
  change IsClosed {f : H | W f + f = 0}
  exact isClosed_eq (W.continuous.add continuous_id) continuous_const

theorem plus_range (W : H →L[ℂ] H) (hW : Function.Involutive W) :
    (plus W).range = plusSpace W := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact sub_eq_zero.mpr (plus_eigen W hW g)
  · intro hf
    refine ⟨f, plus_of_eigen W ?_⟩
    exact sub_eq_zero.mp hf

theorem minus_range (W : H →L[ℂ] H) (hW : Function.Involutive W) :
    (minus W).range = minusSpace W := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact eq_neg_iff_add_eq_zero.mp (minus_eigen W hW g)
  · intro hf
    exact ⟨f, minus_of_eigen W (eq_neg_iff_add_eq_zero.mpr hf)⟩

theorem norm_sq_split (W : H →L[ℂ] H) (hW : Function.Involutive W)
    (hS : ∀ f g : H, inner ℂ (W f) g = inner ℂ f (W g)) (f : H) :
    ‖f‖ ^ 2 = ‖plus W f‖ ^ 2 + ‖minus W f‖ ^ 2 := by
  calc
    _ = ‖plus W f + minus W f‖ ^ 2 := congrArg (fun x : H => ‖x‖ ^ 2) (plus_add_minus W f).symm
    _ = _ := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (projections_orthogonal W hW hS f f)

end ImbalancedChen.Part3.InvolutiveHilbertProjection20261026b

namespace ImbalancedChen.Part3.GlobalFrickeParityProjections20261026b

open Set MeasureTheory
open ImbalancedChen.Part3.InvolutiveHilbertProjection20261026b
open ImbalancedChen.Part3.ActualHeckeSecondL220261026b
open ImbalancedChen.Part3.GlobalFrickeHilbertInvolution20261026b
open ImbalancedChen.Part3.GlobalFrickeClosedEnergyAction20261026b
open ImbalancedChen.Part3.GlobalFrickeFriedrichsIntertwining20261026b
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a

def frickePlus (N : ℕ) [NeZero N] (hN : 0 < N) : QuotientL2 N →L[ℂ] QuotientL2 N :=
  plus (frickeL2 N hN).toContinuousLinearMap

def frickeMinus (N : ℕ) [NeZero N] (hN : 0 < N) : QuotientL2 N →L[ℂ] QuotientL2 N :=
  minus (frickeL2 N hN).toContinuousLinearMap

def energyPlus (N : ℕ) [NeZero N] (hN : 0 < N) : EnergyCompletion N →L[ℂ] EnergyCompletion N :=
  plus (energyFricke N hN)

def energyMinus (N : ℕ) [NeZero N] (hN : 0 < N) : EnergyCompletion N →L[ℂ] EnergyCompletion N :=
  minus (energyFricke N hN)

theorem fricke_parity_orthogonal (N : ℕ) [NeZero N] (hN : 0 < N) (f g : QuotientL2 N) :
    inner ℂ (frickePlus N hN f) (frickeMinus N hN g) = 0 :=
  projections_orthogonal _ (frickeL2_involutive N hN) (frickeL2_inner_flip N hN) f g

theorem frickePlus_idempotent (N : ℕ) [NeZero N] (hN : 0 < N) : IsIdempotentElem (frickePlus N hN) :=
  plus_idempotent _ (frickeL2_involutive N hN)

theorem frickeMinus_idempotent (N : ℕ) [NeZero N] (hN : 0 < N) : IsIdempotentElem (frickeMinus N hN) :=
  minus_idempotent _ (frickeL2_involutive N hN)

theorem frickePlus_selfAdjoint (N : ℕ) [NeZero N] (hN : 0 < N) : IsSelfAdjoint (frickePlus N hN) :=
  plus_selfAdjoint _ (frickeL2_inner_flip N hN)

theorem frickeMinus_selfAdjoint (N : ℕ) [NeZero N] (hN : 0 < N) : IsSelfAdjoint (frickeMinus N hN) :=
  minus_selfAdjoint _ (frickeL2_inner_flip N hN)

theorem frickePlus_range_closed (N : ℕ) [NeZero N] (hN : 0 < N) :
    IsClosed ((frickePlus N hN).range : Set (QuotientL2 N)) := by
  rw [frickePlus, plus_range _ (frickeL2_involutive N hN)]
  exact plusSpace_closed _

theorem frickeMinus_range_closed (N : ℕ) [NeZero N] (hN : 0 < N) :
    IsClosed ((frickeMinus N hN).range : Set (QuotientL2 N)) := by
  rw [frickeMinus, minus_range _ (frickeL2_involutive N hN)]
  exact minusSpace_closed _

theorem fricke_mass_split (N : ℕ) [NeZero N] (hN : 0 < N) (f : QuotientL2 N) :
    ‖f‖ ^ 2 = ‖frickePlus N hN f‖ ^ 2 + ‖frickeMinus N hN f‖ ^ 2 :=
  norm_sq_split _ (frickeL2_involutive N hN) (frickeL2_inner_flip N hN) f

end ImbalancedChen.Part3.GlobalFrickeParityProjections20261026b
