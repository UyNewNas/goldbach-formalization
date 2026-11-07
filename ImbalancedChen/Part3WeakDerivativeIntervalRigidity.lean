import ImbalancedChen.Part3WeakGradientCompactPrimitive

/-! SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.
One-dimensional weak derivative rigidity on an arbitrary nonempty open interval.
The constant is a genuine normalized-bump average. The proof uses the constructed
compact primitive and the pinned smooth-test fundamental lemma. -/
namespace ImbalancedChen.Part3.WeakDerivativeIntervalRigidity20261026a
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff
open ImbalancedChen.Part3.WeakGradientCompactPrimitive20261026a

/-- Genuine smooth normalized bump strictly inside the interval. -/
theorem exists_normalized_interval_bump {a b : ℝ} (hab : a < b) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Ioo a b ∧ (∫ x, β x) = 1 := by
  let φ : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  refine ⟨φ.normed volume, φ.contDiff_normed, φ.hasCompactSupport_normed, ?_, φ.integral_normed⟩
  rw [φ.tsupport_normed_eq]
  intro x hx
  have hd : |x - (a + b) / 2| ≤ (b - a) / 4 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, φ] using hx
  have h := abs_le.mp hd
  constructor <;> linarith

/-- Compact tests supported in the local integrability region have genuine
integrable pairings, with no integrability assumption outside that region. -/
theorem integrable_local_test_smul {U : Set ℝ} {f : ℝ → ℂ}
    (hf : LocallyIntegrableOn f U) {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) :
    Integrable (fun x => g x • f x) := by
  have hfi : Integrable ((tsupport g).indicator f) := by
    rw [integrable_indicator_iff hc.measurableSet]
    exact hf.integrableOn_compact_subset hs hc
  have hprod := hfi.smul_of_top_right (hg.memLp_top_of_hasCompactSupport hc volume)
  apply hprod.congr
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ tsupport g
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]

/-- Zero-mean decomposition relative to an actual normalized compact bump
turns the weak derivative equation into a formula for every smooth test. -/
theorem weak_derivative_test_pairing {a b : ℝ} {f : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioo a b))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ x, deriv ψ x • f x) = 0)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβs : tsupport β ⊆ Ioo a b) (hβi : (∫ x, β x) = 1)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ Ioo a b) :
    (∫ x, g x • f x) = (∫ x, g x) • (∫ x, β x • f x) := by
  let C : ℝ := ∫ x, g x
  let h : ℝ → ℝ := fun x => g x - C * β x
  have hhd : ContDiff ℝ ∞ h := hg.sub (contDiff_const.mul hβ)
  have hhc : HasCompactSupport h := hgc.sub hβc.mul_left
  have hhsupport : support h ⊆ tsupport g ∪ tsupport β := by
    intro x hx
    by_contra hnot
    have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport (fun hgx => hnot (Or.inl hgx))
    have hβ0 : β x = 0 := image_eq_zero_of_notMem_tsupport (fun hβx => hnot (Or.inr hβx))
    exact hx (by simp [h, hg0, hβ0])
  have hhs : tsupport h ⊆ Ioo a b :=
    (closure_minimal hhsupport ((isClosed_tsupport g).union (isClosed_tsupport β))).trans
      (union_subset hgs hβs)
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hβint : Integrable β := hβ.continuous.integrable_of_hasCompactSupport hβc
  have hhmean : (∫ x, h x) = 0 := by
    dsimp [h]
    rw [integral_sub hgi (hβint.const_mul C), integral_const_mul, hβi]
    simp [C]
  have hz := integral_zero_mean_test_eq_zero hweak hhd hhc hhs hhmean
  have hgf := integrable_local_test_smul hf hg.continuous hgc hgs
  have hβf := integrable_local_test_smul hf hβ.continuous hβc hβs
  have hfun : (fun x => h x • f x) =
      (fun x => g x • f x - C • (β x • f x)) := by
    funext x
    simp only [h, sub_smul, mul_smul]
  rw [hfun, integral_sub hgf (hβf.smul C), integral_smul] at hz
  exact sub_eq_zero.mp hz

/-- A locally integrable function with zero distributional derivative is
a.e. one constant on the whole interval, not merely on each compact subset. -/
theorem ae_eq_const_of_zero_weak_derivative {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioo a b))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ x, deriv ψ x • f x) = 0) :
    ∃ c : ℂ, ∀ᵐ x, x ∈ Ioo a b → f x = c := by
  obtain ⟨β, hβ, hβc, hβs, hβi⟩ := exists_normalized_interval_bump hab
  let c : ℂ := ∫ x, β x • f x
  have hfc : LocallyIntegrableOn (fun x => f x - c) (Ioo a b) :=
    hf.sub (locallyIntegrableOn_const c)
  have hz : ∀ᵐ x, x ∈ Ioo a b → f x - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfc
    intro g hg hgc hgs
    have hgf := integrable_local_test_smul hf hg.continuous hgc hgs
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
    have hpair := weak_derivative_test_pairing hf hweak hβ hβc hβs hβi hg hgc hgs
    simp only [smul_sub]
    rw [integral_sub hgf (hgi.smul_const c), integral_smul_const, hpair]
    simp only [c, sub_self]
  refine ⟨c, ?_⟩
  filter_upwards [hz] with x hx
  intro hxin
  exact sub_eq_zero.mp (hx hxin)

end
end ImbalancedChen.Part3.WeakDerivativeIntervalRigidity20261026a