import ImbalancedChen.Part3OriginalPositiveOrbitLimits
import ImbalancedChen.Part3OriginalCrossCuspWeightTwoTail
import Mathlib.Analysis.Normed.Group.Tannery

/-! The two successive limits on the original Γ₀(z) infinity/one
geometric pair. Each sum is over all positive integer moduli d. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalPositiveHeightTest20261112 (original)
open OriginalPositiveRatioWindows20261112 (ratio)
open OriginalPositiveStrip20261112 (residual)
open ActualPositiveHolomorphicDiagonal20261112 (diagonalMoment)
open ActualMarkedGeometricSeries20261112 (geometricTerm)
open OriginalOppositeMarkedKuznetsov20261112 (modulusTerm)
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalTwoZSourceAssembly20261102 OriginalNonzeroCuspOneSource20261102
open ImbalancedChen.P3ZActualPrimaryShortEndpoint (signedY)
open FixedMarkTail (price price_nonneg majorant majorant_nonneg cusp_one_le summable_majorant_price)

theorem rank_one_modulus (ψ φ : ℝ→ℂ) (hpψ : tsupport ψ⊆Ioi (0:ℝ)) (z p : ℕ)
    {b : ℤ} (hb : 0<b) :
    modulusTerm (induced (fun a v => ψ a*star (φ v))) z p b=geometricTerm z p b ψ φ := by
  funext d
  simp only [modulusTerm,geometricTerm,Int.sign_eq_one_of_pos hb,rank_one ψ φ hpψ]

private def scale (p : ℕ) (b : ℤ) : ℝ := 4*Real.pi*Real.sqrt ((p:ℝ)*(b.natAbs:ℝ))
private def bound (z p : ℕ) (b : ℤ) (B : ℝ) (d : ℕ+) : ℝ :=
  (B*scale p b/(z:ℝ))*price (p:ℤ) 0 (d:ℕ)

private theorem scale_pos {p : ℕ} (hp : 0<p) {b : ℤ} (hb : 0<b) : 0<scale p b := by
  have h₁ : (0:ℝ)<p := by exact_mod_cast hp
  have h₂ : (0:ℝ)<b.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hb.ne'
  dsimp [scale]; positivity

private theorem bound_summable (z : ℕ) {p : ℕ} (hp : 0<p) (b : ℤ) (B : ℝ) :
    Summable (bound z p b B) := by
  have hp' : (p:ℤ)≠0 := by exact_mod_cast hp.ne'
  exact ((summable_majorant_price hp' (δ:=0) (by norm_num)).comp_injective
    PNat.coe_injective).mul_left _

private theorem modulus_price {Φ : ℝ→ℂ} {B : ℝ} (hB : 0≤B)
    (hΦ : ∀ q : ℝ,0<q → ‖Φ q‖≤B*q) {z p : ℕ} (hz : 0<z) (hp : 0<p)
    {b : ℤ} (hb : 0<b) (d : ℕ+) : ‖modulusTerm Φ z p b d‖≤bound z p b B d := by
  letI : NeZero (d:ℕ) := ⟨d.property.ne'⟩
  let C := traceModulus z d
  have hC : 0<C := traceModulus_pos hz d.property
  have hs := scale_pos hp hb
  have hzR : (0:ℝ)<z := by exact_mod_cast hz
  have hdR : (0:ℝ)<(d:ℕ) := by exact_mod_cast d.property
  have hp₀ := price_nonneg (p:ℤ) 0 (d:ℕ)
  by_cases hc : z.Coprime (d:ℕ)
  · rw [modulusTerm,dif_pos hc,norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg hC.le]
    change ‖cuspOneMatrixSum z d hc (p:ℤ) b‖/C * ‖Φ (scale p b/C)‖≤_
    have id : price (p:ℤ) 0 (d:ℕ)=majorant (p:ℤ) d/((d:ℕ):ℝ)^2 := by
      simp [price,d.property.ne',Real.rpow_neg hdR.le,Real.rpow_two,div_eq_mul_inv]
    calc
      _ ≤ majorant (p:ℤ) d/C*(B*(scale p b/C)) :=
        mul_le_mul (div_le_div_of_nonneg_right (cusp_one_le z d hz hc (p:ℤ) b) hC.le)
          (hΦ _ (div_pos hs hC)) (norm_nonneg _) (div_nonneg (majorant_nonneg _ _) hC.le)
      _ = B*scale p b*majorant (p:ℤ) d / (C^2) := by field_simp [hC.ne'] <;> ring
      _ = bound z p b B d := by
        rw [bound,id,show C^2=(z:ℝ)*((d:ℕ):ℝ)^2 by
          dsimp only [C,traceModulus]; rw [mul_pow,Real.sq_sqrt hzR.le]]
        field_simp [hzR.ne',hdR.ne'] <;> ring
  · rw [modulusTerm,dif_neg hc,norm_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg hB hs.le) hzR.le) hp₀

private theorem term_tendsto {ι : Type*} {L : Filter ι} {F : ι→ℝ→ℂ} {G : ℝ→ℂ}
    (pointwise : ∀ q : ℝ,0<q → Tendsto (fun i => F i q) L (𝓝 (G q)))
    {z p : ℕ} (hz : 0<z) (hp : 0<p) {b : ℤ} (hb : 0<b) (d : ℕ+) :
    Tendsto (fun i => modulusTerm (F i) z p b d) L (𝓝 (modulusTerm G z p b d)) := by
  by_cases hc : z.Coprime (d:ℕ)
  · simp only [modulusTerm,dif_pos hc]
    exact (pointwise _ (div_pos (scale_pos hp hb) (traceModulus_pos hz d.property))).const_mul _
  · simp only [modulusTerm,dif_neg hc]
    exact tendsto_const_nhds

theorem original_moduli_absolute (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y)
    {z p : ℕ} (hz : 0<z) (hp : 0<p) {b : ℤ} (hb : 0<b) :
    (∀ n R,Summable (fun d : ℕ+ => ‖modulusTerm (induced (original ell hY R n)) z p b d‖)) ∧
    (∀ n,Summable (fun d : ℕ+ => ‖modulusTerm (response (ratio ell hY n)) z p b d‖)) ∧
    Summable (fun d : ℕ+ => ‖modulusTerm (residual ell Y) z p b d‖) := by
  obtain ⟨B,B₀,A,V,G⟩ := joint_price ell hY
  have absSum (Φ : ℝ→ℂ) (hΦ : ∀ q>0,‖Φ q‖≤B*q) :
      Summable (fun d : ℕ+ => ‖modulusTerm Φ z p b d‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (modulus_price B₀ hΦ hz hp hb)
      (bound_summable z hp b B)
  exact ⟨fun n R => absSum _ (A n R),fun n => absSum _ (V n),absSum _ G⟩

theorem modulus_height_limit (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (n : ℕ)
    {z p : ℕ} (hz : 0<z) (hp : 0<p) {b : ℤ} (hb : 0<b) :
    Tendsto (fun R : ℝ => ∑' d : ℕ+,modulusTerm (induced (original ell hY R n)) z p b d) atTop
      (𝓝 (∑' d : ℕ+,modulusTerm (response (ratio ell hY n)) z p b d)) := by
  obtain ⟨B,B₀,A,_,_⟩ := joint_price ell hY
  apply tendsto_tsum_of_dominated_convergence (bound_summable z hp b B)
    (term_tendsto (fun _ hq => original_pointwise ell hY n hq) hz hp hb)
  exact Eventually.of_forall (fun R => modulus_price B₀ (A n R) hz hp hb)

theorem modulus_window_limit (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y)
    {z p : ℕ} (hz : 0<z) (hp : 0<p) {b : ℤ} (hb : 0<b) :
    Tendsto (fun n => ∑' d : ℕ+,modulusTerm (response (ratio ell hY n)) z p b d) atTop
      (𝓝 (∑' d : ℕ+,modulusTerm (residual ell Y) z p b d)) := by
  obtain ⟨B,B₀,_,V,_⟩ := joint_price ell hY
  apply tendsto_tsum_of_dominated_convergence (bound_summable z hp b B)
    (term_tendsto (fun _ hq => response_limit ell hY hq.le) hz hp hb)
  exact Eventually.of_forall (fun n => modulus_price B₀ (V n) hz hp hb)

def windowPair (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (n z p : ℕ) (b : ℤ) : ℂ :=
  (if z=1 ∧ (p:ℤ)=b then (ratio ell hY n).function 0/2 else 0)+
    ∑' d : ℕ+,modulusTerm (response (ratio ell hY n)) z p b d

def residualPair (ell : D4→ℤ) (Y : ℝ) (z p : ℕ) (b : ℤ) : ℂ :=
  (if z=1 ∧ (p:ℤ)=b then diagonalMoment 0 (spectralTest ell Y)/(2*(Real.pi:ℂ)) else 0)+
    ∑' d : ℕ+,modulusTerm (residual ell Y) z p b d

theorem geometric_pair_limits (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y)
    {z p : ℕ} (hz : 0<z) (hp : 0<p) {b : ℤ} (hb : 0<b) :
    (∀ n,Tendsto (fun R : ℝ => diagonal (original ell hY R n) z p b+
        ∑' d : ℕ+,modulusTerm (induced (original ell hY R n)) z p b d) atTop
        (𝓝 (windowPair ell hY n z p b))) ∧
      Tendsto (fun n => windowPair ell hY n z p b) atTop (𝓝 (residualPair ell Y z p b)) := by
  constructor
  · intro n
    simp only [original_diagonal,windowPair]
    exact (modulus_height_limit ell hY n hz hp hb).const_add _
  · exact (original_diagonal_limit ell hY z p b).add (modulus_window_limit ell hY hz hp hb)

/-- The positive sign in the original source is decided before the marks
or the modulus are chosen, from the residue, Poisson sign and primary sign. -/
theorem positive_row_index (D : OriginalData) (k : BlockKey) (negativeM : Bool)
    {z n : ℕ} (hn : n∈nCarrier D k z) (ha : D.block.atom.residue≠0)
    (hs : traceNegative D k negativeM=false) : 0<traceIndex D k negativeM z n := by
  have H := traceIndex_natAbs_pos D k negativeM z hn ha
  rw [traceIndex_natAbs] at H
  rw [traceIndex_eq_signedY,hs,signedY]
  simpa using (show (0:ℤ)<↑(D.block.atom.residue.natAbs*(k.1*n)) by exact_mod_cast H)

theorem original_positive_row (D : OriginalData) (k : BlockKey) (z : Row D k)
    (negativeM : Bool) (ha : D.block.atom.residue≠0) (hs : traceNegative D k negativeM=false)
    {m p J j : ℕ} (hm : m∈nCarrier D k z.val) (hp : p∈commonMBlock J j)
    (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    let b := traceIndex D k negativeM z.val m
    (∀ n,Tendsto (fun R : ℝ => diagonal (original ell hY R n) z.val p b+
        ∑' d : ℕ+,modulusTerm (induced (original ell hY R n)) z.val p b d) atTop
        (𝓝 (windowPair ell hY n z.val p b))) ∧
      Tendsto (fun n => windowPair ell hY n z.val p b) atTop (𝓝 (residualPair ell Y z.val p b)) := by
  have pos : 0<p := lt_of_lt_of_le (pow_pos (by norm_num : (0:ℕ)<2) j) (Finset.mem_Ico.mp hp).1
  exact geometric_pair_limits ell hY (levelCarrier_licensed D k z.property).1 pos
    (positive_row_index D k negativeM hm ha hs)

end ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
end
