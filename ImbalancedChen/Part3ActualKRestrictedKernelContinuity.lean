import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit, 2026-10-24.
The physical interval lies in a fixed positive half-line. Joint continuity
of the actual imaginary-order K integral and the compact-open exponential law
give continuity in spectral height in the genuine C(P.region, ℂ) topology.
Because the domain is compact, this is the actual supremum-norm topology.
-/

namespace ImbalancedChen.Part3.ActualKRestrictedKernelContinuity20261024z

noncomputable section

open Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly

variable {ι : Type*}

/-- The real argument of every restricted kernel lies in the same positive
half-line, independently of spectral height. -/
private theorem region_lower (P : PacketData ι) (q : P.region) :
    P.Y0 / 16 ≤ (q : ℝ) := by
  exact q.property.1

private theorem region_pos (P : PacketData ι) (q : P.region) :
    0 < (q : ℝ) := by
  have ha : 0 < P.Y0 / 16 := by
    have h := P.Y0_pos
    positivity
  exact lt_of_lt_of_le ha (region_lower P q)

/-- Joint continuity of the actual K/q values on the physical region. -/
theorem restrictedKKernel_joint_continuous (P : PacketData ι) :
    Continuous (fun p : ℝ × P.region => restrictedKKernel P p.1 p.2) := by
  have ha : 0 < P.Y0 / 16 := by
    have h := P.Y0_pos
    positivity
  have hq : Continuous (fun p : ℝ × P.region =>
      (⟨(p.2 : ℝ), region_lower P p.2⟩ : Ici (P.Y0 / 16))) :=
    (continuous_subtype_val.comp continuous_snd).subtype_mk
      (fun p => region_lower P p.2)
  have hp : Continuous (fun p : ℝ × P.region =>
      (p.1, (⟨(p.2 : ℝ), region_lower P p.2⟩ : Ici (P.Y0 / 16)))) :=
    continuous_fst.prodMk hq
  have hK : Continuous (fun p : ℝ × P.region =>
      (imaginaryOrderK p.1 (p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((imaginaryOrderK_joint_continuous (P.Y0 / 16) ha).comp hp)
  have hden : Continuous (fun p : ℝ × P.region => ((p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)
  have hdiv : Continuous (fun p : ℝ × P.region =>
      (imaginaryOrderK p.1 (p.2 : ℝ) : ℂ) / ((p.2 : ℝ) : ℂ)) :=
    hK.div hden (fun p => Complex.ofReal_ne_zero.mpr (region_pos P p.2).ne')
  have he : (fun p : ℝ × P.region => restrictedKKernel P p.1 p.2) =
      (fun p : ℝ × P.region =>
        (imaginaryOrderK p.1 (p.2 : ℝ) : ℂ) / ((p.2 : ℝ) : ℂ)) := by
    funext p
    exact restrictedKKernel_eq P p.1 p.2
  rw [he]
  exact hdiv

/-- Continuity is in the actual supremum norm of C(P.region, ℂ), not merely
pointwise in q. The compact-open exponential law proves this directly from
joint continuity; P.region already has its compact-space instance. -/
theorem restrictedKKernel_continuous (P : PacketData ι) :
    Continuous (restrictedKKernel P : ℝ → C(P.region, ℂ)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact restrictedKKernel_joint_continuous P

/-- On every fixed compact height interval, the actual family is uniformly
continuous in the C(P.region, ℂ) supremum norm. -/
theorem restrictedKKernel_uniformContinuousOn_compact_height
    (P : PacketData ι) (T : ℝ) :
    UniformContinuousOn (restrictedKKernel P : ℝ → C(P.region, ℂ))
      (Icc (-T) T) := by
  exact (isCompact_Icc : IsCompact (Icc (-T) T)).uniformContinuousOn_of_continuous
    (restrictedKKernel_continuous P).continuousOn

end
end ImbalancedChen.Part3.ActualKRestrictedKernelContinuity20261024z
