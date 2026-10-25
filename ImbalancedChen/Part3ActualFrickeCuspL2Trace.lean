import ImbalancedChen.Part3ActualFrickeCuspPhase
import ImbalancedChen.Part3CuspTranslationL2Isometry

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual fixed-height original-sigmaOne and literal Fricke traces are
realized as normalized-Haar L2 classes, and the former is exactly the
existing cuspTranslateL2 applied to the latter. The previous generic
translation isometry is reused, not rebuilt. This binds its norm and
inner-product identities to the actual Gamma0 traces. Trace MemLp is an
explicit analytic input; no global Maass trace theorem or K normalization
is manufactured from quotient L2 membership.
-/

namespace ImbalancedChen.Part3.ActualFrickeCuspL2Trace20261025a
noncomputable section
open MeasureTheory AddCircle Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups ModularGroup UpperHalfPlane
open ActualFrickeCuspPhase20261025a
open P3CuspTranslationFourierPhaseSourceOnly

section ActualTrace
variable (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
  (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
  (y : ℝ) (hy : 0 < y)

theorem sigmaOne_memLp_of_fricke
    (htrace : MemLp (frickeSection N hN F hF y hy) 2 AddCircle.haarAddCircle) :
    MemLp (sigmaOneSection N hN F hF y hy) 2 AddCircle.haarAddCircle := by
  rw [sigmaOneSection_eq_translated_frickeSection]
  simpa only [translated, P3CuspTranslationL2IsometrySourceOnly.shift, Function.comp_def] using
    htrace.comp_measurePreserving
      (P3CuspTranslationL2IsometrySourceOnly.shift_measurePreserving (cuspShift N))

def frickeTraceL2 (htrace : MemLp (frickeSection N hN F hF y hy) 2 AddCircle.haarAddCircle) :
    P3CuspTranslationL2IsometrySourceOnly.CircleL2 :=
  htrace.toLp (frickeSection N hN F hF y hy)

def sigmaOneTraceL2 (htrace : MemLp (frickeSection N hN F hF y hy) 2 AddCircle.haarAddCircle) :
    P3CuspTranslationL2IsometrySourceOnly.CircleL2 :=
  (sigmaOne_memLp_of_fricke N hN F hF y hy htrace).toLp (sigmaOneSection N hN F hF y hy)

theorem frickeTraceL2_ae
    (htrace : MemLp (frickeSection N hN F hF y hy) 2 AddCircle.haarAddCircle) :
    (frickeTraceL2 N hN F hF y hy htrace : UnitAddCircle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      frickeSection N hN F hF y hy := htrace.coeFn_toLp

theorem sigmaOneTraceL2_ae
    (htrace : MemLp (frickeSection N hN F hF y hy) 2 AddCircle.haarAddCircle) :
    (sigmaOneTraceL2 N hN F hF y hy htrace : UnitAddCircle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      sigmaOneSection N hN F hF y hy :=
  (sigmaOne_memLp_of_fricke N hN F hF y hy htrace).coeFn_toLp

/-- The actual trace classes, with their actual pointwise representatives,
are related by the already existing normalized-Haar L2 isometry. -/
theorem sigmaOneTraceL2_eq_cuspTranslate
    (htrace : MemLp (frickeSection N hN F hF y hy) 2 AddCircle.haarAddCircle) :
    sigmaOneTraceL2 N hN F hF y hy htrace =
      P3CuspTranslationL2IsometrySourceOnly.cuspTranslateL2 N
        (frickeTraceL2 N hN F hF y hy htrace) := by
  apply Lp.ext
  have hshift :=
    (P3CuspTranslationL2IsometrySourceOnly.shift_measurePreserving (cuspShift N)).quasiMeasurePreserving.ae_eq_comp
      (frickeTraceL2_ae N hN F hF y hy htrace)
  calc
    (sigmaOneTraceL2 N hN F hF y hy htrace : UnitAddCircle → ℂ) =ᵐ[AddCircle.haarAddCircle]
        sigmaOneSection N hN F hF y hy := sigmaOneTraceL2_ae N hN F hF y hy htrace
    _ =ᵐ[AddCircle.haarAddCircle] fun x => frickeSection N hN F hF y hy (x + cuspShift N) :=
      Filter.Eventually.of_forall (congrFun
        (sigmaOneSection_eq_translated_frickeSection N hN F hF y hy))
    _ =ᵐ[AddCircle.haarAddCircle] fun x => (frickeTraceL2 N hN F hF y hy htrace) (x + cuspShift N) :=
      hshift.symm
    _ =ᵐ[AddCircle.haarAddCircle]
        (P3CuspTranslationL2IsometrySourceOnly.cuspTranslateL2 N
          (frickeTraceL2 N hN F hF y hy htrace) : UnitAddCircle → ℂ) :=
      (P3CuspTranslationL2IsometrySourceOnly.cuspTranslateL2_ae N _).symm

theorem actual_trace_norm_eq
    (htrace : MemLp (frickeSection N hN F hF y hy) 2 AddCircle.haarAddCircle) :
    ‖sigmaOneTraceL2 N hN F hF y hy htrace‖ = ‖frickeTraceL2 N hN F hF y hy htrace‖ := by
  rw [sigmaOneTraceL2_eq_cuspTranslate]
  exact P3CuspTranslationL2IsometrySourceOnly.cuspTranslateL2_norm N _

end ActualTrace

theorem actual_trace_inner_eq (N : ℕ) (hN : 0 < N) (F G : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (hG : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, G (g • z) = G z)
    (y : ℝ) (hy : 0 < y)
    (htraceF : MemLp (frickeSection N hN F hF y hy) 2 AddCircle.haarAddCircle)
    (htraceG : MemLp (frickeSection N hN G hG y hy) 2 AddCircle.haarAddCircle) :
    inner ℂ (sigmaOneTraceL2 N hN F hF y hy htraceF) (sigmaOneTraceL2 N hN G hG y hy htraceG) =
      inner ℂ (frickeTraceL2 N hN F hF y hy htraceF) (frickeTraceL2 N hN G hG y hy htraceG) := by
  rw [sigmaOneTraceL2_eq_cuspTranslate, sigmaOneTraceL2_eq_cuspTranslate]
  exact P3CuspTranslationL2IsometrySourceOnly.cuspTranslateL2_inner N _ _

end
end ImbalancedChen.Part3.ActualFrickeCuspL2Trace20261025a
