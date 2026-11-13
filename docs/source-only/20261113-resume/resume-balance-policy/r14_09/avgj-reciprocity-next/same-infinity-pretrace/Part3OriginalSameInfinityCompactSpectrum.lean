import ImbalancedChen.Part3OriginalProjectedContinuousCovariance
import ImbalancedChen.Part3OriginalInfinitySwitchedGeometry
import ImbalancedChen.Part3OriginalSwitchedMellinRows
import Batteries.Tactic.OpenPrivate

/-! Same-infinity spectral resolution at two genuine compact dilated probes.
Both indices and both finite coefficient rows are independent inputs to the
same automorphic quotient. The two native Eisenstein coordinates use false. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityCompactSpectrum20261113
noncomputable section
open MeasureTheory Matrix
open scoped MatrixGroups BigOperators
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open AllNormalizedCuspAnnihilator20261026b ActualFullCuspResolvent20261026b
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualCuspDenominatorClasses20261110 ActualContinuousPoincarePairing20261110 ActualOrdinaryContinuousModes20261110
open ActualYoungFormalClass20261110 ActualContinuousClassFourier20261110
open OriginalContinuousPoincarePackets20261110 OriginalContinuousCuspGram20261110 OriginalContinuousClassRemoval20261110
open OriginalCuspidalPoincareTrace20261110 OriginalResidualPoincarePackets20261110
open ActualMarkedContinuousCoordinates20261112 ActualMarkedHorocycleSupport20261112
open ActualContinuousResolution20261112 ActualContinuousPhysicalComplement20261112 OriginalProjectedContinuousCovariance20261112
open OriginalMarkedWeakAdjoint20261112 ActualInfinityCuspAnnihilator20261026b
open private packet_projection from ImbalancedChen.Part3OriginalResidualPoincarePackets
open private integrated_native from ImbalancedChen.Part3OriginalMarkedWeakAdjoint
open private projected_inner from ImbalancedChen.Part3OriginalProjectedContinuousCovariance

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def vector (q : ℕ) [NeZero q] (S : Finset ℕ) (w : ℕ → ℂ) (f : ℕ → ℤ)
    (pos : ∀ n ∈ S, f n ≠ 0) (ψ : HeightSeed) : QuotientL2 q :=
  (packet_L2 q false S w f pos ψ.toFun ψ.continuous ψ.compact ψ.positive).toLp (packet q false S w f ψ.toFun)

def discrete (q : ℕ) [NeZero q] (S : Finset ℕ) (w : ℕ → ℂ) (f : ℕ → ℤ)
    (ψ : HeightSeed) (i : actualCuspBasisIndex q (NeZero.pos q)) : ℂ :=
  orderProbe 1 ψ.toFun (basisOrder q (NeZero.pos q) i)*markedRow S w f (basisR q (NeZero.pos q) i 1)

def continuousCoord (q : ℕ) [NeZero q] (S : Finset ℕ) (w : ℕ → ℂ) (f : ℕ → ℤ)
    (ψ : HeightSeed) (t : ℝ) (a : Parameters q) : ℂ :=
  radialProbe 1 ψ.toFun t*markedRow S w f (fun n => nativeR a false n t)

private theorem discrete_coord (q : ℕ) [NeZero q] (S : Finset ℕ) (w : ℕ → ℂ) (f : ℕ → ℤ)
    (pos : ∀ n ∈ S, f n ≠ 0) (ψ : HeightSeed) (i : actualCuspBasisIndex q (NeZero.pos q)) :
    inner ℂ (vector q S w f pos ψ) (actualCuspHilbertBasis q (NeZero.pos q) i : QuotientL2 q) =
      discrete q S w f ψ i :=
  basis_packet_inner q i false S w f pos ψ.toFun ψ.continuous ψ.compact ψ.positive

/-- Both compact packets live in the identity frame at the same level.
The full Maass spectrum and the entire native continuous spectrum include
their actual radial transforms. No Parseval or residual premise is supplied. -/
theorem compact_spectrum (q : ℕ) [NeZero q] (S T : Finset ℕ) (u v : ℕ→ℂ) (f g : ℕ→ℤ)
    (su : ∀ n ∈ S, f n ≠ 0) (tv : ∀ n ∈ T, g n ≠ 0) (ψ φ : HeightSeed) :
    let F := fun i => discrete q S u f ψ i * star (discrete q T v g φ i)
    let E := fun t => nativeProduct q (continuousCoord q T v g φ t) (continuousCoord q S u f ψ t)
    Summable F ∧ Integrable E ∧ inner ℂ (vector q S u f su ψ) (vector q T v g tv φ) =
      (∑' i, F i)+(∫ t : ℝ, E t) := by
  classical
  let N := NeZero.pos q
  let X := packet q false S u f ψ.toFun
  let Y := packet q false T v g φ.toFun
  let x := vector q S u f su ψ
  let y := vector q T v g tv φ
  let D := allFrameCuspSubspace q N
  let B := actualCuspHilbertBasis q N
  let F := fun i => discrete q S u f ψ i * star (discrete q T v g φ i)
  let E := fun t => nativeProduct q (continuousCoord q T v g φ t) (continuousCoord q S u f ψ t)
  have hx := packet_L2 q false S u f su ψ.toFun ψ.continuous ψ.compact ψ.positive
  have hy := packet_L2 q false T v g tv φ.toFun φ.continuous φ.compact φ.positive
  have rx := packet_projection q false S u f su ψ.toFun ψ.continuous ψ.compact ψ.positive
  have ry := packet_projection q false T v g tv φ.toFun φ.continuous φ.compact φ.positive
  have cx := marked_support q false S u f su ψ.toFun ψ.continuous ψ.compact ψ.positive
  have cy := marked_support q false T v g tv φ.toFun φ.continuous φ.compact φ.positive
  have H : HasSum F (inner ℂ (project q x) (project q y)) := by
    convert B.hasSum_inner_mul_inner (project q x) (project q y) using 1
    ext i
    change _ = inner ℂ (D.orthogonalProjectionOnto x) (B i)*inner ℂ (B i) (D.orthogonalProjectionOnto y)
    rw [D.inner_orthogonalProjectionOnto_eq_of_mem_right,D.inner_orthogonalProjectionOnto_eq_of_mem_left,
      ←inner_conj_symm (B i : QuotientL2 q) y]
    change _ = inner ℂ (vector q S u f su ψ) (B i : QuotientL2 q) *
      star (inner ℂ (vector q T v g tv φ) (B i : QuotientL2 q))
    rw [discrete_coord,discrete_coord]
  have J := integrated_native q hy hx cy cx ry rx
  have eq : (fun t => nativeProduct q (fun a => spectrum q Y a t) (fun a => spectrum q X a t)) = E := by
    funext t
    have ex (a) := (packet_spectrum q false S u f su ψ.toFun ψ.continuous ψ.compact ψ.positive a t).2
    have ey (a) := (packet_spectrum q false T v g tv φ.toFun φ.continuous φ.compact φ.positive a t).2
    simp only [X,Y,ex,ey,E,continuousCoord]
  change Integrable (fun t => nativeProduct q (fun a => spectrum q Y a t) (fun a => spectrum q X a t)) ∧
    inner ℂ x (nativeSynthesis q (fun a => analysis q a y))=
      ∫ t : ℝ, nativeProduct q (fun a => spectrum q Y a t) (fun a => spectrum q X a t) at J
  rw [eq] at J
  have I : inner ℂ ((centeredSpace q).starProjection x) ((centeredSpace q).starProjection y)=∫ t : ℝ,E t := by
    rw [←projected_inner (centeredSpace q) x y,←nativeSynthesis_analysis_eq_projection]
    exact J.2
  refine ⟨H.summable,J.1,?_⟩
  have G := spatial_orthogonal_gram q x y
  dsimp only at G
  change (ℂ ∙ constantL2 q).starProjection x=0 at rx
  rw [rx,inner_zero_left,zero_add,←continuous_projection_gram,I] at G
  change inner ℂ x y=(∑' i,F i)+(∫ t : ℝ,E t)
  rw [H.tsum_eq]
  exact G

open MediumGlobalDyadicOwnership20261028 ActualIntervalGeometricSumSourceOnly OriginalSwitchedMellinRows20261113

def nativeWeight (ω t : ℝ) (m : ℕ) := phaseAt ω m*wave (m:ℝ) t

private theorem dyadic_nonzero (j : ℕ) (m : ℕ) (h : m∈dyadicWindow j) : (m:ℤ)≠0 := by
  have hm := (mem_Ico.mp h).1
  exact_mod_cast (lt_of_lt_of_le (pow_pos (by norm_num : 0<(2:ℕ)) j) hm).ne'

/-- The common-phase native Maass row in an actual Mellin-twisted
dyadic packet. The packet uses R; the existing native row uses rhoK=2R. -/
theorem native_discrete_twist (q : ℕ+) (j : ℕ) (ω t : ℝ) (ψ : HeightSeed)
    (i : actualCuspBasisIndex q.val q.property) :
    2*discrete q.val (dyadicWindow j) (nativeWeight ω t) (fun m => (m:ℤ)) ψ i =
      orderProbe 1 ψ.toFun (basisOrder q.val q.property i)*
        twistedRow (dyadicWindow j) (nativeRow q i ω) t := by
  classical
  unfold discrete markedRow twistedRow nativeWeight nativeRow
  rw [mul_left_comm,Finset.mul_sum (dyadicWindow j) _ (2:ℂ)]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [basisR_eq_half_native q.val q.property i (1 : SL(2,ℤ)) (dyadic_nonzero j m hm)]
  ring

/-- Explicit native compact packets for the two equal positive integer
windows and the same additive phase at the given level. The separate
Mellin frequencies allow both signs of the switched half-frequency. -/
theorem native_compact_spectrum (q : ℕ) [NeZero q] (j : ℕ) (ω s t : ℝ) (ψ φ : HeightSeed) :
    let S := dyadicWindow j
    let u := nativeWeight ω s
    let v := nativeWeight ω t
    let f := fun m : ℕ => (m:ℤ)
    let F := fun i => discrete q S u f ψ i * star (discrete q S v f φ i)
    let E := fun h => nativeProduct q (continuousCoord q S v f φ h) (continuousCoord q S u f ψ h)
    Summable F ∧ Integrable E ∧ inner ℂ (vector q S u f (dyadic_nonzero j) ψ)
      (vector q S v f (dyadic_nonzero j) φ)=(∑' i,F i)+(∫ h : ℝ,E h) :=
  compact_spectrum q (dyadicWindow j) (dyadicWindow j) (nativeWeight ω s) (nativeWeight ω t)
    _ _ (dyadic_nonzero j) (dyadic_nonzero j) ψ φ

end
end ImbalancedChen.Part3.OriginalSameInfinityCompactSpectrum20261113
