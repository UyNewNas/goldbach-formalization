import ImbalancedChen.Part3OriginalSameInfinityProbeEnergy
import ImbalancedChen.Part3OriginalSameInfinityScalarLimits

/-! Sum the compact scalar packet through the genuine Maass spectrum
and the full incoming-cusp integral in their physical normalization. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityTensorSpectrum20261113
noncomputable section
open Set Filter MeasureTheory Complex Finset
open scoped Topology BigOperators MatrixGroups
open OriginalSameInfinityProbeEnergy20261113 OriginalSameInfinityScalarTensor20261113
open OriginalSameInfinityCompactTrace20261113 OriginalPositiveTensorResolution20261112 (atom_real)
open OriginalSameInfinityScalarGeometry20261113
open RadialSchrodingerL2Form20261025a OriginalPositiveHeightTest20261112
open ActualPositiveTensorIntegral20261112 ActualPositiveTensorProbes20261112
open PrescribedLogTensorCoefficients20261112 (Modes) ActualPositiveScalarPacket20261112 (packet)
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualContinuousPoincarePairing20261110 OriginalContinuousCuspGram20261110
open ActualContinuousClassFourier20261110
open ActualCuspDenominatorClasses20261110 OriginalCuspidalPoincareTrace20261110
open private probe_basis from ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov
open private packetVector from ImbalancedChen.Part3OriginalInfinitySwitchedGeometry

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def disc (q m n : ℕ+) (i : actualCuspBasisIndex q.val (NeZero.pos q.val)) :=
  star (basisR q.val (NeZero.pos q.val) i 1 (m.val:ℤ))*basisR q.val (NeZero.pos q.val) i 1 (n.val:ℤ)
def cont (q m n : ℕ+) (t : ℝ) := nativeProduct q.val (fun a => nativeR a false (m.val:ℤ) t)
  (fun a => nativeR a false (n.val:ℤ) t)

def orderSum (q m n : ℕ+) (W : ℂ→ℂ) :=
  (∑' i,W (basisOrder q.val (NeZero.pos q.val) i)*disc q m n i)+(∫ t : ℝ,W ((t:ℂ)*I)*cont q m n t)

private theorem disc_factor (q m n : ℕ+) (v : Modes) (i : actualCuspBasisIndex q.val (NeZero.pos q.val)) :
    star (atom q m (left v) i)*atom q n (right v) i =
      probeProduct (basisOrder q.val (NeZero.pos q.val) i) v*disc q m n i := by
  simp only [probeProduct,probe_basis,atom,left,right,disc,star_mul']
  ring

private theorem cont_factor (q m n : ℕ+) (v : Modes) (t : ℝ) :
    star (eisenstein q m n (left v) (right v) t)=probeProduct ((t:ℂ)*I) v*cont q m n t := by
  simp only [eisenstein,cont,nativeProduct,atom_real,left,right,star_sum,Finset.mul_sum]
  apply sum_congr rfl
  intro a _
  simp only [star_div₀,star_mul',star_star,star_ofNat,Complex.star_def,Complex.conj_ofReal]
  ring

theorem compact_scalar (η H : RadialTest) (R : ℝ) (q m n : ℕ+) :
    pair q m n (height η H R)=orderSum q m n (packet η H R) := by
  classical
  let c := coeff η H R
  let D (v : Modes) (i : actualCuspBasisIndex q.val (NeZero.pos q.val)) :=
    c v*(star (atom q m (left v) i)*atom q n (right v) i)
  let G (v : Modes) (t : ℝ) := c v*star (eisenstein q m n (left v) (right v) t)
  have B := tensor_budget η H R q m n
  have E (v : Modes) := pair_energy q m n (left v) (right v)
  have D1 : Summable (fun p : Modes×actualCuspBasisIndex q.val (NeZero.pos q.val) => ‖D p.1 p.2‖) := by
    simp only [D,norm_mul,norm_star]
    apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
    refine ⟨fun v => (by simpa only [norm_mul,norm_star] using (E v).1.mul_left ‖c v‖),?_⟩
    simp_rw [tsum_mul_left]
    apply B.of_nonneg_of_le (fun _ => by positivity)
    intro v
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have nn := integral_nonneg (fun t => norm_nonneg (eisenstein q m n (left v) (right v) t))
    have raw := (E v).2.2
    simp only [norm_mul,norm_star] at raw
    linarith
  have ds : Summable (Function.uncurry D) := D1.of_norm
  have individual (i : actualCuspBasisIndex q.val (NeZero.pos q.val)) :
      (∑' v,D v i)=packet η H R (basisOrder q.val (NeZero.pos q.val) i)*disc q m n i := by
    simp only [D,disc_factor,←mul_assoc,tsum_mul_right,c]
    rw [(probes η H R _).tsum_eq]
  have discrete := ds.prod.hasSum
  rw [ds.tsum_comm.symm] at discrete
  simp_rw [individual] at discrete
  have GI (v : Modes) : Integrable (G v) :=
    (Complex.conjCLE.toContinuousLinearMap.integrable_comp (E v).2.1).const_mul (c v)
  have gr (v : Modes) : (∫ t,‖G v t‖)=‖c v‖*(∫ t,‖eisenstein q m n (left v) (right v) t‖) := by
    simp only [G,norm_mul,norm_star,integral_const_mul]
  have gs : Summable (fun v => ∫ t,‖G v t‖) := by
    apply B.of_nonneg_of_le (fun v => integral_nonneg fun _ => norm_nonneg _)
    intro v
    rw [gr]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have nn := tsum_nonneg (fun i => norm_nonneg (star (atom q m (left v) i)*atom q n (right v) i))
    linarith only [(E v).2.2,nn]
  have continuous := hasSum_integral_of_summable_integral_norm GI gs
  have line (t : ℝ) : (∑' v,G v t)=packet η H R ((t:ℂ)*I)*cont q m n t := by
    simp only [G,cont_factor,←mul_assoc,tsum_mul_right,c]
    rw [(probes η H R _).tsum_eq]
  simp_rw [line] at continuous
  apply (scalar_tensor η H R q m n).unique ((discrete.add continuous).congr_fun ?_)
  intro v
  have dcomp : star (∑' i,atom q m (left v) i*star (atom q n (right v) i))=
      ∑' i,star (atom q m (left v) i)*atom q n (right v) i := by
    rw [tsum_star]
    exact tsum_congr (fun i => by simp only [star_mul',star_star,mul_comm])
  have icomp : star (∫ t,eisenstein q m n (left v) (right v) t)=
      ∫ t,star (eisenstein q m n (left v) (right v) t) := by
    simp only [Complex.star_def,integral_conj]
  simp only [D,G,c,tsum_mul_left,integral_const_mul,star_add,dcomp,icomp,mul_add]

end
end ImbalancedChen.Part3.OriginalSameInfinityTensorSpectrum20261113
