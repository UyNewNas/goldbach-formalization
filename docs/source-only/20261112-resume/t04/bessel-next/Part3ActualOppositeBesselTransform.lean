import ImbalancedChen.Part3ActualOppositeBruhatMass
import ImbalancedChen.Part3OriginalMarkedArithmeticTrace
import ImbalancedChen.Part3ActualGreenResolventJump

/-! The actual K transform of the marked physical opposite-sign test.
The factor eight follows from the Bruhat Jacobians and from the two
Whittaker Fourier probes, each of which contains 2 sqrt(y). -/
namespace ImbalancedChen.Part3.ActualOppositeBesselTransform20261112

noncomputable section
open Set Filter MeasureTheory Complex
open ActualOppositeBruhatCoordinates20261112 ActualOppositeBruhatMass20261112
open ActualOppositeKProduct20261112 ActualMarkedBruhatTest20261112
open ComplexOrderKBridgeSourceOnly ActualGreenResolventJumpSourceOnly
open ActualContinuousPoincarePairing20261110 ActualOrdinaryContinuousModes20261110
open ActualCriticalCuspEvaluation20261110 OriginalContinuousPoincarePackets20261110
open CompactCuspGeometricFubini20261025a OriginalMarkedArithmeticTrace20261112

def kTransform (ν : ℂ) (Φ : ℝ → ℂ) : ℂ :=
  ∫ q,complexOrderK (2*ν) q*Φ q/(q : ℂ) ∂posMeasure

def oppositeWeight (Φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  8*(Real.cosh (Real.pi*t) : ℂ)*kTransform ((t : ℂ)*I) Φ

private def coefficient (ν : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (amp a : ℂ)*f a*complexOrderK ν (2*Real.pi*a)

private theorem k_conj (ν : ℂ) (a : ℝ) : star (complexOrderK (star ν) a)=complexOrderK ν a := by
  rw [complexOrderK,complexOrderK,← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    simp only [complexOrderIntegrand,Complex.star_def,map_mul,Complex.conj_ofReal,← Complex.cosh_conj,
      map_mul,Complex.conj_conj])

private theorem probe (ν : ℂ) (ψ : ℝ → ℂ) :
    orderProbe 1 ψ ν=2*∫ a,coefficient ν (fun y => star (ψ y)) a ∂posMeasure := by
  rw [orderProbe,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun a => by
    simp only [orderRadial,Int.cast_one,abs_one,mul_one,Complex.real_smul,coefficient,amp,Complex.ofReal_mul]
    ring)

private theorem probe_left (ν : ℂ) (ψ : ℝ → ℂ) :
    star (orderProbe 1 ψ (star ν))=2*∫ a,coefficient ν ψ a ∂posMeasure := by
  rw [probe,star_mul',star_ofNat,← integral_conj]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    change star (coefficient (star ν) (fun a => star (ψ a)) y)=coefficient ν ψ y
    have ar : star (amp y : ℂ)=(amp y : ℂ) := Complex.conj_ofReal _
    simp only [coefficient,star_mul',ar,star_star,k_conj])

private theorem row_integral (ν : ℂ) (ψ φ : ℝ → ℂ) {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    (∫ v : ℝ,transformed ν ψ φ a v b) =
      (1/2 : ℂ)*(coefficient ν ψ a*coefficient ν (fun y => star (φ y)) b) := by
  let A := 2*Real.pi*a
  let B := 2*Real.pi*b
  have hA : 0<A := by dsimp [A]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have sq : 2*Real.sqrt (A*B)=4*Real.pi*Real.sqrt (a*b) := by
    have E : A*B=(2*Real.pi)^2*(a*b) := by dsimp [A,B]; ring
    rw [E,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
    ring
  have J := (opposite_product ν hA hB).2
  dsimp only at J
  rw [sq] at J
  unfold transformed
  rw [integral_const_mul,J]
  simp only [coefficient,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,A,B]
  ring

private theorem raw_slice (ν : ℂ) (ψ φ : ℝ → ℂ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (q : ℝ) :
    (∫ x : ℝ,∫ a,raw ν ψ φ a x q ∂posMeasure)=complexOrderK (2*ν) q*orbitTest (-1) ψ φ q/(q : ℂ) := by
  let K := orbitTestKernel (-1) ψ φ ((q/(4*Real.pi))^2)
  have S (x : ℝ) : (∫ a,star (K x a) ∂posMeasure)=star (∫ a : ℝ,K x a) := by
    rw [integral_conj]
    congr 1
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    apply ae_of_all
    intro a
    by_cases ha : a ∈ Ioi (0 : ℝ)
    · exact indicator_of_mem ha _ 
    · have za : ψ a=0 := by
        by_contra h
        exact ha (hpψ (subset_tsupport ψ h))
      simp only [indicator_of_notMem ha,K,orbitTestKernel,radialWeight,za,star_zero,mul_zero,zero_mul]
  change (∫ x : ℝ,∫ a,((4*Real.pi/q^2 : ℝ) : ℂ)*complexOrderK (2*ν) q*star (K x a) ∂posMeasure)=_
  simp_rw [integral_const_mul,S]
  rw [integral_conj,orbitTest]
  simp only [K,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_ofNat,div_eq_mul_inv,
    inv_pow]
  ring

/-- The equality holds for arbitrary complex order. In this version the
left probe has conjugate order, so its conjugation returns the same
kernel order that occurs at the right. -/
theorem induced_transform (ν : ℂ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun q => complexOrderK (2*ν) q*orbitTest (-1) ψ φ q/(q : ℂ)) posMeasure ∧
      8*kTransform ν (orbitTest (-1) ψ φ)=star (orderProbe 1 ψ (star ν))*orderProbe 1 φ ν := by
  let F := fun p : ℝ × ℝ × ℝ => raw ν ψ φ p.1 p.2.1 p.2.2
  have HF : Integrable F grid := raw_integrable ν ψ φ hψ hcψ hpψ hφ hcφ hpφ
  have HR : Integrable (F ∘ reversal) grid := HF.comp_measurePreserving reversal_preserves
  have HT := trans_integrable ν ψ φ hψ hcψ hpψ hφ hcφ hpφ
  have V (q : ℝ) : (∫ x : ℝ,∫ a,raw ν ψ φ a x q ∂posMeasure)=_ := raw_slice ν ψ φ hpψ q
  have aeR : (fun q => ∫ p : ℝ × ℝ,(F ∘ reversal) (q,p) ∂volume.prod posMeasure) =ᵐ[posMeasure]
      (fun q => complexOrderK (2*ν) q*orbitTest (-1) ψ φ q/(q : ℂ)) := by
    filter_upwards [HR.prod_right_ae] with q hq
    exact (integral_prod _ hq).trans (V q)
  refine ⟨HR.integral_prod_left.congr aeR,?_⟩
  have T : kTransform ν (orbitTest (-1) ψ φ) = (1/2 : ℂ)*
      ((∫ a,coefficient ν ψ a ∂posMeasure)*(∫ b,coefficient ν (fun y => star (φ y)) b ∂posMeasure)) := by
    calc
      _ = ∫ p,(F ∘ reversal) p ∂grid := by
        rw [integral_prod _ HR]
        exact integral_congr_ae aeR.symm
      _ = ∫ p,F p ∂grid := reversal_preserves.integral_comp' F
      _ = ∫ a,∫ v : ℝ,∫ b,transformed ν ψ φ a v b ∂posMeasure ∂volume ∂posMeasure := by
        rw [nested F HF]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact change_integral ν ψ φ ha
      _ = ∫ a,∫ b,(1/2 : ℂ)*(coefficient ν ψ a*coefficient ν (fun y => star (φ y)) b) ∂posMeasure ∂posMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi,HT.prod_right_ae] with a ha hi
        rw [integral_integral_swap (f := transformed ν ψ φ a) hi]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
        exact row_integral ν ψ φ ha hb
      _ = _ := by simp_rw [integral_const_mul,integral_mul_const]
  rw [T,probe_left,probe]
  ring

theorem probe_neg_order (ψ : ℝ → ℂ) (ν : ℂ) : orderProbe 1 ψ (-ν)=orderProbe 1 ψ ν := by
  simp only [orderProbe,orderRadial,complexOrderK_neg_order]

theorem induced_weight (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    oppositeWeight (orbitTest (-1) ψ φ) t=probeWeight ψ φ t := by
  let ν := (t : ℂ)*I
  have c : star ν= -ν := by simp [ν,Complex.star_def]
  have s : criticalPoint t-1/2=ν := by unfold ν criticalPoint; ring
  have H := (induced_transform ν ψ φ hψ hcψ hpψ hφ hcφ hpφ).2
  rw [c,probe_neg_order] at H
  change 8*(Real.cosh (Real.pi*t) : ℂ)*kTransform ν _ =
    (Real.cosh (Real.pi*t) : ℂ)*(star (orderProbe 1 ψ (criticalPoint t-1/2))*orderProbe 1 φ (criticalPoint t-1/2))
  rw [s,← H]
  ring

end
end ImbalancedChen.Part3.ActualOppositeBesselTransform20261112
