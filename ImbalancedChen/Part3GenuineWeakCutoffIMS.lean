import ImbalancedChen.Part3LocalGradientH1WeakTesting

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact weak IMS for a real compact cutoff and a genuine local H1 solution.
The cutoff-square test is constructed by the preceding H1 theorem. All
complex polarization and all L1 obligations are paid here. No IMS,
energy-smallness, or H1-test-closure membership is assumed.
-/
namespace ImbalancedChen.Part3.GenuineWeakCutoffIMS20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a CompactC2JetCutoffEstimate20261026a
open WeakH1ProductMollifierDerivative20261026a
open LocalWeakH1CutoffProduct20261026b LocalGradientH1WeakTesting20261026b
open LocalH1Tests20261026b LocalH1SecondOrderWeakPDEExtension20261026b
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a

def complexCutoff (χ : Plane → ℝ) (p : Plane) : ℂ := χ p

private theorem scalar_IMS (r : ℝ) (g d : ℂ) :
    ‖(r : ℂ) * g + d‖ ^ 2 =
      (star ((r : ℂ) * (r : ℂ) * g + 2 * (r : ℂ) * d) * g).re + ‖d‖ ^ 2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.star_def,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.ofNat_re,Complex.ofNat_im,
    Complex.conj_re,Complex.conj_im]
  ring

private theorem scalar_mass (r v : ℝ) (z : ℂ) :
    (star ((r : ℂ) * (r : ℂ) * z) * ((v : ℂ) * z)).re = r^2 * v * ‖z‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.star_def,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  ring

/-- All three energy integrands in IMS are L1. In particular the mass
integral is justified by the actual L2 mass coefficient, even when no
separate global bound or measurability of the potential is supplied. -/
theorem weak_IMS_energy_integrable
    (F m : Plane → ℂ) (V χ : Plane → ℝ)
    (hF : MemLp F 2 volume) (hm : MemLp m 2 volume)
    (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hmass : ∀ p ∈ tsupport χ, m p = (V p : ℂ) * F p) :
    Integrable (fun p => ‖productDerivative (complexCutoff χ) F gx ex p‖^2 +
      ‖productDerivative (complexCutoff χ) F gy ey p‖^2) volume ∧
    Integrable (fun p => (χ p)^2 * V p * ‖F p‖^2) volume ∧
    Integrable (fun p => (‖directional ex (complexCutoff χ) p‖^2 +
      ‖directional ey (complexCutoff χ) p‖^2) * ‖F p‖^2) volume := by
  let C := complexCutoff χ
  have hC : ContDiff ℝ ∞ C := Complex.ofRealCLM.contDiff.comp hχ
  have hCc : HasCompactSupport C := hχc.comp_left (g := Complex.ofReal) (by simp)
  have hGs (v : Plane) (g : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) :=
    productDerivative_memLp hC hCc hF (Lp.memLp g) v
  have hIG (v : Plane) (g : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) :
      Integrable (fun p => ‖productDerivative C F g v p‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (hGs v g).aestronglyMeasurable).mp (hGs v g)
  have hDs (v : Plane) := compact_multiplier_memLp (directional_smooth v hC).continuous
    (directional_compact v hCc) hF
  have hID (v : Plane) : Integrable (fun p => ‖directional v C p * F p‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (hDs v).aestronglyMeasurable).mp (hDs v)
  have hiM : Integrable (fun p => star (C p * C p * F p) * m p) volume :=
    MemLp.integrable_mul (p := 2) (q := 2)
      (compact_multiplier_memLp (hC.mul hC).continuous hCc.mul_right hF).star hm
  refine ⟨(hIG ex gx).add (hIG ey gy),hiM.re.congr ?_,((hID ex).add (hID ey)).congr ?_⟩
  · exact Eventually.of_forall fun p => by
      by_cases hp : p ∈ tsupport χ
      · rw [hmass p hp]
        exact scalar_mass (χ p) (V p) (F p)
      · have hz := image_eq_zero_of_notMem_tsupport hp
        simp [C,complexCutoff,hz]
  · exact Eventually.of_forall fun p => by
      simp only [norm_mul,mul_pow]
      ring
/-- Exact IMS from the literal cutoff-square weak equation. Its
hypothesis is a first-order PDE test identity, not an energy identity. -/
theorem weak_IMS_of_cutoff_square_identity
    (F m : Plane → ℂ) (V χ : Plane → ℝ)
    (hF : MemLp F 2 volume) (hm : MemLp m 2 volume)
    (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hmass : ∀ p ∈ tsupport χ, m p = (V p : ℂ) * F p)
    (htest :
      (∫ p, star (productDerivative (fun q => complexCutoff χ q * complexCutoff χ q) F gx ex p) * gx p) +
      (∫ p, star (productDerivative (fun q => complexCutoff χ q * complexCutoff χ q) F gy ey p) * gy p) +
      (∫ p, star (complexCutoff χ p * complexCutoff χ p * F p) * m p) = 0) :
    (∫ p, ‖productDerivative (complexCutoff χ) F gx ex p‖^2 +
      ‖productDerivative (complexCutoff χ) F gy ey p‖^2) +
      (∫ p, (χ p)^2 * V p * ‖F p‖^2) =
    ∫ p, (‖directional ex (complexCutoff χ) p‖^2 +
      ‖directional ey (complexCutoff χ) p‖^2) * ‖F p‖^2 := by
  let C := complexCutoff χ
  have hC : ContDiff ℝ ∞ C := Complex.ofRealCLM.contDiff.comp hχ
  have hCc : HasCompactSupport C := hχc.comp_left (g := Complex.ofReal) (by simp)
  let d (v : Plane) (p : Plane) := directional v C p * F p
  let G (v : Plane) (g : Plane → ℂ) := productDerivative C F g v
  let T (v : Plane) (g : Plane → ℂ) := productDerivative (fun p => C p * C p) F g v
  have hd (v : Plane) : MemLp (d v) 2 volume :=
    compact_multiplier_memLp (directional_smooth v hC).continuous (directional_compact v hCc) hF
  have hG (v : Plane) (g : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) : MemLp (G v g) 2 volume :=
    productDerivative_memLp hC hCc hF (Lp.memLp g) v
  have hT (v : Plane) (g : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) : MemLp (T v g) 2 volume :=
    productDerivative_memLp (hC.mul hC) hCc.mul_right hF (Lp.memLp g) v
  have hid (v : Plane) : Integrable (fun p => ‖d v p‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (hd v).aestronglyMeasurable).mp (hd v)
  have hiG (v : Plane) (g : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) :
      Integrable (fun p => ‖G v g p‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (hG v g).aestronglyMeasurable).mp (hG v g)
  have hiT (v : Plane) (g : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) :
      Integrable (fun p => star (T v g p) * g p) volume :=
    MemLp.integrable_mul (p := 2) (q := 2) (hT v g).star (Lp.memLp g)
  have hiM : Integrable (fun p => star (C p * C p * F p) * m p) volume :=
    MemLp.integrable_mul (p := 2) (q := 2)
      (compact_multiplier_memLp (hC.mul hC).continuous hCc.mul_right hF).star hm
  have hpoint (v : Plane) (g : Plane → ℂ) (p : Plane) :
      ‖G v g p‖^2 = (star (T v g p) * g p).re + ‖d v p‖^2 := by
    have hTv : T v g p = C p * C p * g p + 2 * C p * d v p := by
      dsimp [T,productDerivative]
      rw [directional_mul v hC hC]
      dsimp [d]
      ring
    rw [hTv]
    have hGv : G v g p = C p * g p + d v p := by dsimp [G,productDerivative,d]; ring
    rw [hGv]
    exact scalar_IMS (χ p) (g p) (d v p)
  have henergy (v : Plane) (g : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) :
      (∫ p, ‖G v g p‖^2) = (∫ p, star (T v g p) * g p).re + ∫ p, ‖d v p‖^2 := by
    calc
      _ = ∫ p, (star (T v g p) * g p).re + ‖d v p‖^2 :=
        integral_congr_ae (Eventually.of_forall (hpoint v g))
      _ = _ := by rw [integral_add (hiT v g).re (hid v),integral_re (hiT v g)]
  have hmasspoint (p : Plane) :
      (star (C p * C p * F p) * m p).re = (χ p)^2 * V p * ‖F p‖^2 := by
    by_cases hp : p ∈ tsupport χ
    · rw [hmass p hp]
      exact scalar_mass (χ p) (V p) (F p)
    · have hz := image_eq_zero_of_notMem_tsupport hp
      simp only [C,complexCutoff,hz,Complex.ofReal_zero,zero_mul,star_zero,
        Complex.zero_re,zero_pow (by norm_num : 2 ≠ 0)]
  have hmassIntegral : (∫ p, (χ p)^2 * V p * ‖F p‖^2) =
      (∫ p, star (C p * C p * F p) * m p).re := by
    rw [← integral_re hiM]
    exact integral_congr_ae (Eventually.of_forall fun p => (hmasspoint p).symm)
  have herror : (∫ p, (‖directional ex C p‖^2 + ‖directional ey C p‖^2) * ‖F p‖^2) =
      (∫ p, ‖d ex p‖^2) + (∫ p, ‖d ey p‖^2) := by
    calc
      _ = ∫ p, ‖d ex p‖^2 + ‖d ey p‖^2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by simp only [d,norm_mul,mul_pow]; ring
      _ = _ := integral_add (hid ex) (hid ey)
  have hre : (∫ p, star (T ex gx p) * gx p).re +
      (∫ p, star (T ey gy p) * gy p).re +
      (∫ p, star (C p * C p * F p) * m p).re = 0 := by
    simpa only [Complex.add_re,Complex.zero_re] using congrArg Complex.re htest
  rw [integral_add (hiG ex gx) (hiG ey gy),hmassIntegral,herror]
  linarith [henergy ex gx,henergy ey gy]

/-- True weak IMS: its cutoff-square test is DERIVED from local H1 and
smooth transposed PDE data through the constructed same-chart density. -/
theorem local_gradient_weak_IMS {Ω : Set Plane}
    (N : ℕ) (F m : Plane → ℂ) (V χ : Plane → ℝ)
    (hF : MemLp F 2 volume) (hm : MemLp m 2 volume)
    (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hgrad : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * F p)))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hmass : ∀ p ∈ tsupport χ, m p = (V p : ℂ) * F p)
    (uL uR vL vR : ℝ) (hvL : 0 < vL) (hu : uL < uR) (hv : vL < vR)
    (hUΩ : openRect uL uR vL vR ⊆ Ω)
    (hχU : tsupport χ ⊆ openRect uL uR vL vR)
    (hU : ∀ z : UpperHalfPlane, z.re ∈ Ioo uL uR → z.im ∈ Ioo vL vR → z ∈ reducedCarrier N)
    (hPDE : ∀ G : Plane → ℂ, ContDiff ℝ ∞ G → HasCompactSupport G →
      tsupport G ⊆ openRect uL uR vL vR → secondOrderEquation F m G) :
    (∫ p, ‖productDerivative (complexCutoff χ) F gx ex p‖^2 +
      ‖productDerivative (complexCutoff χ) F gy ey p‖^2) +
      (∫ p, (χ p)^2 * V p * ‖F p‖^2) =
    ∫ p, (‖directional ex (complexCutoff χ) p‖^2 +
      ‖directional ey (complexCutoff χ) p‖^2) * ‖F p‖^2 := by
  have hC : ContDiff ℝ ∞ (complexCutoff χ) := Complex.ofRealCLM.contDiff.comp hχ
  have hCc : HasCompactSupport (complexCutoff χ) := hχc.comp_left (g := Complex.ofReal) (by simp)
  have hCU : tsupport (complexCutoff χ) ⊆ openRect uL uR vL vR :=
    (tsupport_comp_subset (g := Complex.ofReal) (by simp) χ).trans hχU
  exact weak_IMS_of_cutoff_square_identity F m V χ hF hm gx gy hχ hχc hmass
    (local_gradient_cutoff_square_test N F m (complexCutoff χ) hF hm gx gy hgrad
      hC hCc uL uR vL vR hvL hu hv hUΩ hCU hU hPDE)

end
end ImbalancedChen.Part3.GenuineWeakCutoffIMS20261026b

