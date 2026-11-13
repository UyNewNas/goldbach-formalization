import ImbalancedChen.Part3OriginalSameInfinityScalarTensor

/-! Spectral domination of the actual two identity packets with a
constant independent of the tensor character on each active height box. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityProbeEnergy20261113
noncomputable section
open Set Finset Complex MeasureTheory
open scoped BigOperators MatrixGroups
open OriginalSameInfinityScalarTensor20261113 (left right)
open OriginalSameInfinityCompactTrace20261113 OriginalSameInfinityCompactSpectrum20261113
open ActualInfinityCuspAnnihilator20261026b OriginalInfinitySwitchedGeometry20261113
open OriginalContinuousCuspGram20261110 ActualCuspDenominatorClasses20261110
open ActualContinuousClassFourier20261110
open ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110
open OriginalContinuousClassRemoval20261110 ActualFullCuspEigenbasis20261026b
open RadialSchrodingerL2Form20261025a OriginalPositiveHeightTest20261112
open ActualPositiveTensorIntegral20261112 PrescribedLogTensorCoefficients20261112 (Modes)
open PrescribedTensorPacketPrice20261112 (packet_budget) PrescribedTensorSeedNorm20261112 (price_growth)
open private positiveIndex singleton_vector from ImbalancedChen.Part3OriginalSameInfinityCompactTrace
open private packetVector from ImbalancedChen.Part3OriginalInfinitySwitchedGeometry
open private native_self_re from ImbalancedChen.Part3OriginalContinuousCuspGram
open private center_bound from ImbalancedChen.Part3ActualPositiveCompactTensor

local instance (n : ℕ+) : NeZero n.val := ⟨n.property.ne'⟩

def coord (q m : ℕ+) (ψ : HeightSeed) (t : ℝ) (a : Parameters q.val) :=
  radialProbe 1 ψ.toFun t*nativeR a false (m.val:ℤ) t

/-- Each self-energy is the exact sum of the discrete square and the
continuous square with all incoming cusps and the native 1/(4π). -/
theorem self_energy (q m : ℕ+) (ψ : HeightSeed) :
    Summable (fun i => ‖atom q m ψ i‖^2) ∧
    Integrable (fun t => nativeMass q.val (coord q m ψ t)) ∧
    (∑' i,‖atom q m ψ i‖^2)+(∫ t,nativeMass q.val (coord q m ψ t))=‖packetVector q m ψ‖^2 := by
  let S := ({m.val}:Finset ℕ)
  have T := compact_spectrum q.val S S (fun _ => 1) (fun _ => 1)
    (fun a => (a:ℤ)) (fun b => (b:ℤ)) (positiveIndex m) (positiveIndex m) ψ ψ
  simp only [S,singleton_vector,discrete,continuousCoord,markedRow,sum_singleton,one_mul] at T
  let F := fun i => atom q m ψ i*star (atom q m ψ i)
  let G := fun t => nativeProduct q.val (coord q m ψ t) (coord q m ψ t)
  change Summable F ∧ Integrable G ∧ inner ℂ (packetVector q m ψ) (packetVector q m ψ)=
    (∑' i,F i)+∫ t,G t at T
  have r (i) : (F i).re=‖atom q m ψ i‖^2 := by
    simp only [F,Complex.star_def,Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  have a : Summable (fun i => ‖atom q m ψ i‖^2) := by
    have v := summable_norm_iff.mpr T.1
    simpa only [F,norm_mul,norm_star,←sq] using v
  have b : Integrable (fun t => nativeMass q.val (coord q m ψ t)) :=
    T.2.1.re.congr (ae_of_all _ (fun t => native_self_re q.val _))
  have eq := congrArg Complex.re T.2.2
  simp only [inner_self_eq_norm_sq_to_K,←Complex.ofReal_pow,Complex.ofReal_re,Complex.add_re,
    Complex.re_tsum T.1,←integral_re T.2.1] at eq
  simp only [r,G,native_self_re] at eq
  exact ⟨a,b,eq.symm⟩

private theorem cross_re (q : ℕ+) (X Y : Parameters q.val→ℂ) :
    ‖nativeProduct q.val X Y‖ ≤ nativeMass q.val X+nativeMass q.val Y := by
  simp only [nativeProduct,nativeMass,←sum_add_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro a _
  rw [norm_div,norm_mul,norm_star,show (4*(Real.pi:ℂ))=((4*Real.pi:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_real,Real.norm_of_nonneg (by positivity),←add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith only [sq_nonneg (‖X a‖-‖Y a‖),sq_nonneg (‖X a‖+‖Y a‖)]

/-- One bound covers both spectral components of every active pair.
Only the square norms of the original spatial packets enter. -/
theorem pair_energy (q m n : ℕ+) (ψ φ : HeightSeed) :
    let D := fun i => star (atom q m ψ i)*atom q n φ i
    let G := eisenstein q m n ψ φ
    Summable (fun i => ‖D i‖) ∧ Integrable G ∧
      (∑' i,‖D i‖)+(∫ t,‖G t‖)≤‖packetVector q m ψ‖^2+‖packetVector q n φ‖^2 := by
  dsimp only
  obtain ⟨a,b,A⟩ := self_energy q m ψ
  obtain ⟨c,d,C⟩ := self_energy q n φ
  obtain ⟨_,T⟩ := same_infinity_compact_trace m n ψ φ
  have g := (T q).2.1
  have f (i) : ‖star (atom q m ψ i)*atom q n φ i‖≤‖atom q m ψ i‖^2+‖atom q n φ i‖^2 := by
    rw [norm_mul,norm_star]
    nlinarith only [sq_nonneg (‖atom q m ψ i‖-‖atom q n φ i‖),sq_nonneg (‖atom q m ψ i‖+‖atom q n φ i‖)]
  have S := (a.add c).of_nonneg_of_le (fun _ => norm_nonneg _) f
  have L := S.tsum_le_tsum f (a.add c)
  rw [a.tsum_add c] at L
  have M := integral_mono g.norm (d.add b) (fun t => cross_re q (coord q n φ t) (coord q m ψ t))
  rw [integral_add d b] at M
  exact ⟨S,g,by linarith only [A,C,L,M]⟩

theorem tensor_budget (η H : RadialTest) (R : ℝ) (q m n : ℕ+) :
    Summable (fun v : Modes => ‖coeff η H R v‖*(‖packetVector q m (left v)‖^2+
      ‖packetVector q n (right v)‖^2)) := by
  obtain ⟨B,_,centers⟩ := center_bound (log_compact η H R)
  obtain ⟨L,lp,l⟩ := packet_budget q.val false false {m.val} (fun _ => 1) (fun x => (x:ℤ)) (positiveIndex m)
  obtain ⟨M,mp,h⟩ := packet_budget q.val false true {n.val} (fun _ => 1) (fun x => (x:ℤ)) (positiveIndex n)
  apply ((coeff_summable η H R).mul_right ((L*(2*Real.exp B))^2+(M*(2*Real.exp B))^2)).of_nonneg_of_le
    (fun _ => by positivity)
  intro v
  by_cases zero : coeff η H R v=0
  · simp [zero]
  obtain ⟨x,y⟩ := centers v zero
  have X : ‖packetVector q m (left v)‖≤L*(2*Real.exp B) := by
    rw [←singleton_vector]
    exact (l v.1.1 v.2.1).trans (mul_le_mul_of_nonneg_left ((price_growth _).trans (by gcongr)) lp)
  have Y : ‖packetVector q n (right v)‖≤M*(2*Real.exp B) := by
    rw [←singleton_vector]
    exact (h v.1.2 v.2.2).trans (mul_le_mul_of_nonneg_left ((price_growth _).trans (by gcongr)) mp)
  exact mul_le_mul_of_nonneg_left (add_le_add (pow_le_pow_left₀ (norm_nonneg _) X 2)
    (pow_le_pow_left₀ (norm_nonneg _) Y 2)) (norm_nonneg _)

end
end ImbalancedChen.Part3.OriginalSameInfinityProbeEnergy20261113
