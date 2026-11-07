import ImbalancedChen.Part3ActualHeckeSecondCoverMeasure
import ImbalancedChen.Part3ActualHeckeForgetL2

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Actual native L2 pullback by the second correspondence projection. It is
constructed by the proved canonical Fricke isometries and the proved
first-cover pullback. Its representative is genuinely F∘secondProjection,
its norm is sqrt(p+1) times the original, and normalization gives an
actual complex-linear isometric embedding. No second norm premise.
-/

namespace ImbalancedChen.Part3.ActualHeckeSecondL220261026b
noncomputable section
open Set MeasureTheory
open ActualFrickeQuotientMeasure20261026b ActualHeckeSecondCoverMeasure20261026b
open ActualHeckeSecondProjection20261026b ActualHeckeForgetCoverMeasure20261026b
open ActualHeckeForgetL220261026b Gamma0QuotientCellPushforward20261025a

def frickeL2 (N : ℕ) [NeZero N] (hN : 0 < N) :
    Lp ℂ 2 (carrierPushforward N) →ₗᵢ[ℂ] Lp ℂ 2 (carrierPushforward N) :=
  Lp.compMeasurePreservingₗᵢ ℂ (quotientFricke N hN)
    ⟨quotientFricke_measurable N hN, quotientFricke_map_measure N hN⟩

theorem frickeL2_coe (N : ℕ) [NeZero N] (hN : 0 < N) (F : Lp ℂ 2 (carrierPushforward N)) :
    (frickeL2 N hN F : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] F ∘ quotientFricke N hN :=
  Lp.coeFn_compMeasurePreserving F ⟨quotientFricke_measurable N hN, quotientFricke_map_measure N hN⟩

variable (N p : ℕ) [NeZero N] [NeZero (N*p)]
  (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)

theorem secondProjection_measurePreserving :
    MeasurePreserving (secondProjection N p hp hpN) (carrierPushforward (N*p))
      ((p+1 : ℝ≥0∞) • carrierPushforward N) :=
  ⟨secondProjection_measurable N p hp hpN, secondProjection_map_measure N p hN hp hpN⟩

theorem secondProjection_memLp {U : Gamma0OrbitSpace N → ℂ}
    (hU : MemLp U 2 (carrierPushforward N)) :
    MemLp (U ∘ secondProjection N p hp hpN) 2 (carrierPushforward (N*p)) :=
  (hU.smul_measure (by simp : (p+1 : ℝ≥0∞) ≠ ∞)).comp_measurePreserving
    (secondProjection_measurePreserving N p hN hp hpN)

def rawSecondPullbackLinear :
    Lp ℂ 2 (carrierPushforward N) →ₗ[ℂ] Lp ℂ 2 (carrierPushforward (N*p)) :=
  (frickeL2 (N*p) (Nat.mul_pos hN hp.pos)).toLinearMap.comp
    ((rawPullbackLinear N p hp hpN).comp (frickeL2 N hN).toLinearMap)

/-- The native composed linear map is the ACTUAL second-projection
pullback almost everywhere, not an abstract isometry with an unnamed action. -/
theorem rawSecondPullback_coe (F : Lp ℂ 2 (carrierPushforward N)) :
    (rawSecondPullbackLinear N p hN hp hpN F : Gamma0OrbitSpace (N*p) → ℂ) =ᵐ[carrierPushforward (N*p)]
      F ∘ secondProjection N p hp hpN := by
  have hFrPres : MeasurePreserving (quotientFricke (N*p) (Nat.mul_pos hN hp.pos))
      (carrierPushforward (N*p)) (carrierPushforward (N*p)) :=
    ⟨quotientFricke_measurable _ _, quotientFricke_map_measure _ _⟩
  have houter := frickeL2_coe (N*p) (Nat.mul_pos hN hp.pos)
    (rawPullback N p hp hpN (frickeL2 N hN F))
  have hmid := hFrPres.quasiMeasurePreserving.ae_eq_comp
    (rawPullback_coe N p hp hpN (frickeL2 N hN F))
  have hin := hFrPres.quasiMeasurePreserving.ae_eq_comp
    ((forgetPrimeLevel_quasiMeasurePreserving N p hp hpN).ae_eq_comp (frickeL2_coe N hN F))
  filter_upwards [houter,hmid,hin] with q houter hmid hin
  change _ = F (secondProjection N p hp hpN q)
  calc
    _ = rawPullback N p hp hpN (frickeL2 N hN F)
        (quotientFricke (N*p) (Nat.mul_pos hN hp.pos) q) := houter
    _ = frickeL2 N hN F (forgetPrimeLevel N p
        (quotientFricke (N*p) (Nat.mul_pos hN hp.pos) q)) := hmid
    _ = F (quotientFricke N hN (forgetPrimeLevel N p
        (quotientFricke (N*p) (Nat.mul_pos hN hp.pos) q))) := hin
    _ = _ := congrArg F (congrFun (secondProjection_fricke_factor N p hN hp hpN).symm q)

theorem rawSecondPullback_norm (F : Lp ℂ 2 (carrierPushforward N)) :
    ‖rawSecondPullbackLinear N p hN hp hpN F‖ = Real.sqrt (p+1 : ℝ)*‖F‖ := by
  change ‖frickeL2 (N*p) (Nat.mul_pos hN hp.pos) (rawPullback N p hp hpN (frickeL2 N hN F))‖ = _
  rw [(frickeL2 (N*p) (Nat.mul_pos hN hp.pos)).norm_map,
    rawPullback_norm N p hp hpN, (frickeL2 N hN).norm_map]

def normalizedSecondPullback :
    Lp ℂ 2 (carrierPushforward N) →ₗᵢ[ℂ] Lp ℂ 2 (carrierPushforward (N*p)) :=
  (frickeL2 (N*p) (Nat.mul_pos hN hp.pos)).comp
    ((normalizedPullback N p hp hpN).comp (frickeL2 N hN))

theorem normalizedSecondPullback_eq_smul (F : Lp ℂ 2 (carrierPushforward N)) :
    normalizedSecondPullback N p hN hp hpN F =
      (Real.sqrt (p+1 : ℝ) : ℂ)⁻¹ • rawSecondPullbackLinear N p hN hp hpN F :=
  (frickeL2 (N*p) (Nat.mul_pos hN hp.pos)).map_smul _ _

theorem normalizedSecondPullback_coe (F : Lp ℂ 2 (carrierPushforward N)) :
    (normalizedSecondPullback N p hN hp hpN F : Gamma0OrbitSpace (N*p) → ℂ) =ᵐ[carrierPushforward (N*p)]
      fun q => (Real.sqrt (p+1 : ℝ) : ℂ)⁻¹ * F (secondProjection N p hp hpN q) := by
  rw [normalizedSecondPullback_eq_smul]
  filter_upwards [Lp.coeFn_smul (Real.sqrt (p+1 : ℝ) : ℂ)⁻¹
    (rawSecondPullbackLinear N p hN hp hpN F), rawSecondPullback_coe N p hN hp hpN F] with q hq hF
  simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] using hq.trans
    (congrArg (fun z : ℂ => (Real.sqrt (p+1 : ℝ) : ℂ)⁻¹ • z) hF)

end
end ImbalancedChen.Part3.ActualHeckeSecondL220261026b
