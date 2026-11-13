import ImbalancedChen.Part3OriginalPositiveTensorResolution
import ImbalancedChen.Part3ActualPositiveTensorGeometry
import ImbalancedChen.Part3OriginalPositiveOrbitModuli
import Mathlib.Data.PNat.Interval
import Batteries.Tactic.OpenPrivate

/-! The exact original positive pretrace at the genuine compact height
packet. The common finite cutoff below is fixed only for this packet. -/
namespace ImbalancedChen.Part3.OriginalPositiveCompactPretrace20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open PrescribedLogTensorWindows20261112 PrescribedLogTensorCoefficients20261112 (Modes)
open PrescribedLogTensorExpansion20261112 (productAt)
open ActualPositiveTensorIntegral20261112 ActualPositiveTensorProbes20261112 ActualPositiveTensorGeometry20261112
open OriginalPositiveTensorResolution20261112 OriginalPositiveScalarGeometry20261112
open OriginalPositiveHeightTest20261112 ActualPositiveScalarPacket20261112 RadialSchrodingerL2Form20261025a
open OriginalMarkedPacketLimits20261112
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalSignedTraceInput20261102 OriginalTwoZFourierAssembly20261102
open OriginalTwoZSourceAssembly20261102 OriginalNonzeroCuspOneSource20261102
open OriginalNativeCuspFunctionals20261102 OriginalContinuousPoincarePackets20261110 ActualFullCuspEigenbasis20261026b
open ActualCuspBasisWhittakerCoefficients20261102 OriginalCuspidalPoincareTrace20261110
open ActualMarkedGeometricSeries20261112 OriginalMarkedArithmeticTrace20261112 OriginalOppositeMarkedKuznetsov20261112
open private regular_density from ImbalancedChen.Part3OriginalMarkedArithmeticTrace
open private probe_basis from ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov
open private scale scale_pos from ImbalancedChen.Part3OriginalPositiveOrbitModuli

private theorem sum_moduli (η H : RadialTest) (R : ℝ) {z p : ℕ} (hz : 0<z) (hp : 0<p) {b : ℤ} (hb : 0<b) :
    HasSum (fun v : Modes => coeff η H R v*∑' d : ℕ+,modulusTerm (induced (productAt v)) z p b d)
      (∑' d : ℕ+,modulusTerm (induced (height η H R)) z p b d) := by
  obtain ⟨δ,dp,cut⟩ := small η H R
  have sq : 0<Real.sqrt (z:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hz)
  obtain ⟨A,hA⟩ := exists_nat_gt (scale p b/(Real.sqrt (z:ℝ)*δ))
  let U := Finset.Icc (1:ℕ+) (⟨A+1,Nat.succ_pos _⟩:ℕ+)
  have outside (d : ℕ+) (h : d∉U) : (A:ℝ)<((d:ℕ):ℝ) := by
    have h₀ : A<(d:ℕ) := by by_contra! e; exact h (Finset.mem_Icc.mpr ⟨d.property,e.trans (Nat.le_succ _)⟩)
    exact_mod_cast h₀
  let arg := fun d : ℕ+ => scale p b/traceModulus z d
  have support (d : ℕ+) (h : d∉U) := cut (arg d) (div_pos (scale_pos hp hb) (traceModulus_pos hz d.property)) (by
    have e := (div_lt_iff₀ (mul_pos sq dp)).mp (hA.trans (outside d h))
    apply (div_lt_iff₀ (traceModulus_pos hz d.property)).mpr
    simpa only [traceModulus,mul_comm,mul_left_comm,mul_assoc] using e)
  have point (d : ℕ+) : HasSum (fun v : Modes => coeff η H R v*modulusTerm (induced (productAt v)) z p b d)
      (modulusTerm (induced (height η H R)) z p b d) := by
    by_cases hd : z.Coprime (d:ℕ)
    · simp only [modulusTerm,dif_pos hd]
      exact ((orbit η H R (arg d)).mul_left _).congr_fun (fun v => by ring)
    · simp [modulusTerm,hd]
  have hzero (d : ℕ+) (hd : d∉U) :
      (∀ v : Modes,coeff η H R v*modulusTerm (induced (productAt v)) z p b d=0) ∧
        modulusTerm (induced (height η H R)) z p b d=0 := by
    by_cases h : z.Coprime (d:ℕ)
    · obtain ⟨C,K⟩ := support d hd
      simp only [modulusTerm,dif_pos h]
      refine ⟨fun v => ?_,?_⟩
      · rw [mul_left_comm,show coeff η H R v*induced (productAt v) (arg d)=0 from C v,mul_zero]
      · rw [show induced (height η H R) (arg d)=0 from K,mul_zero]
    · simp [modulusTerm,h]
  have t (v : Modes) : coeff η H R v*(∑' d : ℕ+,modulusTerm (induced (productAt v)) z p b d)=
      ∑ d∈U,coeff η H R v*modulusTerm (induced (productAt v)) z p b d := by
    rw [←tsum_mul_left]; exact tsum_eq_sum (fun d hd => (hzero d hd).1 v)
  simp_rw [t]
  rw [tsum_eq_sum (s:=U) (fun d hd => (hzero d hd).2)]
  exact hasSum_sum (fun d (_ : d∈U) => point d)

variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4→ℤ)
local instance nzLevel : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩

def marking (F : ℕ→ℤ→ℂ) : ℂ :=
  ∑ n∈nCarrier D k z.val,∑ p∈commonMBlock J j,(commonPoissonCompleted J j (ell 1)).weight p*
    traceBeta D r k upper negativeM ell z.val n*F p (traceIndex D k negativeM z.val n)

def pair (G : ℝ→ℝ→ℂ) (p : ℕ) (b : ℤ) :=
  diagonal G z.val p b+∑' d : ℕ+,modulusTerm (induced G) z.val p b d

local notation "mark" => marking D r k z upper negativeM J j ell
local notation "Zpair" => pair D k z

theorem compact_pretrace (ha : D.block.atom.residue≠0) (hs : traceNegative D k negativeM=false)
    (η H : RadialTest) (R : ℝ) :
    mark (Zpair (height η H R))=orderTotal D r k z upper negativeM J j ell (packet η H R) := by
  have geom (p : ℕ) (b : ℤ) (hp : 0<p) (hb : 0<b) :
      HasSum (fun v => coeff η H R v*Zpair (productAt v) p b) (Zpair (height η H R) p b) := by
    simpa only [pair,mul_add] using (diagonal_sum η H R z.val p b).add
      (sum_moduli η H R (levelCarrier_licensed D k z.property).1 hp hb)
  have G := hasSum_sum (fun n (hn : n∈nCarrier D k z.val) =>
    hasSum_sum (fun p (hp : p∈commonMBlock J j) => (geom p (traceIndex D k negativeM z.val n)
      (lt_of_lt_of_le (pow_pos (by norm_num : 0<(2:ℕ)) j) (Finset.mem_Ico.mp hp).1)
      (positive_row_index D k negativeM hn ha hs)).mul_left
      ((commonPoissonCompleted J j (ell 1)).weight p*traceBeta D r k upper negativeM ell z.val n)))
  have GS : HasSum (fun v => coeff η H R v*mark (Zpair (productAt v))) (mark (Zpair (height η H R))) :=
    G.congr_fun (fun v => by simp only [marking,Finset.mul_sum]; apply Finset.sum_congr rfl; intro n hn
                              apply Finset.sum_congr rfl; intro p hp; ring)
  have S := resolution D r k z ha upper negativeM J j ell η H R
  apply GS.unique (S.congr_fun ?_)
  intro v
  let ψ := pattern v.1.1 v.2.1; let φ := rightPattern v.1.2 v.2.2
  have p := pattern_test v.1.1 v.2.1; have f := right_test v.1.2 v.2.2
  have A := (original_marked_arithmetic_trace D r k z ha upper negativeM J j ell ψ φ p.1 p.2.1 p.2.2 f.1 f.2.1 f.2.2).2.2.2
  apply congrArg (fun w => coeff η H R v*w)
  calc
    mark (Zpair (productAt v)) = _ := by
      unfold marking; apply Finset.sum_congr rfl; intro n hn
      apply Finset.sum_congr rfl; intro x hx
      have xp := lt_of_lt_of_le (pow_pos (by norm_num : 0<(2:ℕ)) j) (Finset.mem_Ico.mp hx).1
      unfold pair productAt
      rw [diagonal_rank_one _ _ p.2.2 _ _ xp,rank_one_modulus _ _ p.2.2 _ _ (positive_row_index D k negativeM hn ha hs)]
    _ = _ := A
    _ = _ := by
      unfold orderTotal total
      congr 1
      · apply tsum_congr; intro i; simp only [probeProduct,probe_basis,dMark,ψ,φ]
      · apply integral_congr_ae; exact ae_of_all _ fun t => by rw [←regular_density,atom_real,cMark]

end
end ImbalancedChen.Part3.OriginalPositiveCompactPretrace20261112
