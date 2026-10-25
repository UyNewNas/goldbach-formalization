import ImbalancedChen.Part3RadialClosedHilbertFormRiesz
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual equivalence of the positive-shift radial form domains. The ambient
PiLp2 map multiplies only the zeroth coordinate by mu/kappa. It maps each
literal core vector (kappa*f,f',exp*f) to (mu*f,f',exp*f), then maps the
actual closed spans by continuity. Its inverse is the reverse scaling.
The physical, derivative and exponential coordinates are preserved.
No equality/equivalence of the completed domains is an assumption.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open Set

def radialEnergyScale (c : ℂ) : RadialEnergyHilbert →L[ℂ] RadialEnergyHilbert where
  toFun p := WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then c • p 0 else p i)
  map_add' := by
    intro p q
    ext i
    by_cases hi : i = 0 <;> simp [hi, smul_add]
  map_smul' := by
    intro a p
    ext i
    by_cases hi : i = 0
    · simp only [hi, if_pos rfl, Pi.smul_apply, smul_smul]
      congr 1
      ring
    · simp [hi]
  cont := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => RadialL2)).comp
    apply continuous_pi
    intro i
    by_cases hi : i = 0
    · simpa only [hi, if_pos rfl] using
        (continuous_const.smul (PiLp.continuous_apply 2 (fun _ : Fin 3 => RadialL2) 0))
    · simpa only [hi, if_false] using
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => RadialL2) i)

theorem radialEnergyScale_comp (c d : ℂ) (p : RadialEnergyHilbert) :
    radialEnergyScale c (radialEnergyScale d p) = radialEnergyScale (c * d) p := by
  ext i
  by_cases hi : i = 0 <;> simp [radialEnergyScale, hi, smul_smul]

theorem radialEnergyScale_one (p : RadialEnergyHilbert) : radialEnergyScale 1 p = p := by
  ext i
  by_cases hi : i = 0 <;> simp [radialEnergyScale, hi]

theorem radialEnergyScale_core (kappa mu : ℝ) (hkappa : 0 < kappa) (T : RadialTest) :
    radialEnergyScale (mu / kappa : ℂ) (radialEnergyCoreVector kappa T) =
      radialEnergyCoreVector mu T := by
  have hc : (mu / kappa : ℂ) * (kappa : ℂ) = mu := by
    have hk : (kappa : ℂ) ≠ 0 := by exact_mod_cast hkappa.ne'
    field_simp [hk]
  ext i
  fin_cases i
  · change (mu / kappa : ℂ) • ((kappa : ℂ) • radialCoreL2 T) =
      (mu : ℂ) • radialCoreL2 T
    rw [smul_smul, hc]
  · rfl
  · rfl

theorem radialEnergyScale_maps_closedDomain (kappa mu : ℝ) (hkappa : 0 < kappa)
    {p : RadialEnergyHilbert} (hp : p ∈ radialClosedEnergyDomain kappa) :
    radialEnergyScale (mu / kappa : ℂ) p ∈ radialClosedEnergyDomain mu := by
  let S := (radialClosedEnergyDomain mu).comap
    (radialEnergyScale (mu / kappa : ℂ)).toLinearMap
  have hS : IsClosed (S : Set RadialEnergyHilbert) :=
    (radialEnergyCoreSpan mu).isClosed_topologicalClosure.preimage
      (radialEnergyScale (mu / kappa : ℂ)).continuous
  have hspan : radialEnergyCoreSpan kappa ≤ S := by
    apply Submodule.span_le.2
    rintro _ ⟨T, rfl⟩
    change radialEnergyScale (mu / kappa : ℂ) (radialEnergyCoreVector kappa T) ∈
      radialClosedEnergyDomain mu
    rw [radialEnergyScale_core kappa mu hkappa T]
    exact (radialEnergyCoreSpan mu).le_topologicalClosure (Submodule.subset_span ⟨T, rfl⟩)
  exact (radialEnergyCoreSpan kappa).topologicalClosure_minimal hspan hS hp

def radialShiftFormTransport (kappa mu : ℝ) (hkappa : 0 < kappa) :
    radialClosedEnergyDomain kappa →L[ℂ] radialClosedEnergyDomain mu :=
  ((radialEnergyScale (mu / kappa : ℂ)).comp
    (radialClosedEnergyDomain kappa).subtypeL).codRestrict
      (radialClosedEnergyDomain mu) (fun p => radialEnergyScale_maps_closedDomain kappa mu hkappa p.2)

theorem radialShiftFormTransport_inverse (kappa mu : ℝ)
    (hkappa : 0 < kappa) (hmu : 0 < mu) (p : radialClosedEnergyDomain kappa) :
    radialShiftFormTransport mu kappa hmu (radialShiftFormTransport kappa mu hkappa p) = p := by
  apply Subtype.ext
  change radialEnergyScale (kappa / mu : ℂ)
    (radialEnergyScale (mu / kappa : ℂ) p) = p
  rw [radialEnergyScale_comp]
  have hc : (kappa / mu : ℂ) * (mu / kappa : ℂ) = 1 := by
    have hk : (kappa : ℂ) ≠ 0 := by exact_mod_cast hkappa.ne'
    have hm : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu.ne'
    field_simp [hk, hm]
  rw [hc, radialEnergyScale_one]

def radialShiftFormEquiv (kappa mu : ℝ) (hkappa : 0 < kappa) (hmu : 0 < mu) :
    radialClosedEnergyDomain kappa ≃L[ℂ] radialClosedEnergyDomain mu where
  toLinearEquiv :=
    { toFun := radialShiftFormTransport kappa mu hkappa
      invFun := radialShiftFormTransport mu kappa hmu
      map_add' := (radialShiftFormTransport kappa mu hkappa).map_add
      map_smul' := (radialShiftFormTransport kappa mu hkappa).map_smul
      left_inv := radialShiftFormTransport_inverse kappa mu hkappa hmu
      right_inv := radialShiftFormTransport_inverse mu kappa hmu hkappa }
  continuous_toFun := (radialShiftFormTransport kappa mu hkappa).continuous
  continuous_invFun := (radialShiftFormTransport mu kappa hmu).continuous

theorem radialShiftFormTransport_physical (kappa mu : ℝ)
    (hkappa : 0 < kappa) (hmu : 0 < mu) (p : radialClosedEnergyDomain kappa) :
    radialPhysicalEmbedding mu (radialShiftFormTransport kappa mu hkappa p) =
      radialPhysicalEmbedding kappa p := by
  change (mu⁻¹ : ℂ) • ((mu / kappa : ℂ) • (p : RadialEnergyHilbert) 0) =
    (kappa⁻¹ : ℂ) • (p : RadialEnergyHilbert) 0
  rw [smul_smul]
  have hc : (mu⁻¹ : ℂ) * (mu / kappa : ℂ) = (kappa⁻¹ : ℂ) := by
    have hk : (kappa : ℂ) ≠ 0 := by exact_mod_cast hkappa.ne'
    have hm : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu.ne'
    push_cast
    field_simp [hk, hm]
  rw [hc]

theorem radialShiftFormTransport_derivative (kappa mu : ℝ) (hkappa : 0 < kappa)
    (p : radialClosedEnergyDomain kappa) :
    radialClosedDerivative mu (radialShiftFormTransport kappa mu hkappa p) =
      radialClosedDerivative kappa p := rfl

theorem radialShiftFormTransport_exponential (kappa mu : ℝ) (hkappa : 0 < kappa)
    (p : radialClosedEnergyDomain kappa) :
    radialClosedExponential mu (radialShiftFormTransport kappa mu hkappa p) =
      radialClosedExponential kappa p := rfl

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
