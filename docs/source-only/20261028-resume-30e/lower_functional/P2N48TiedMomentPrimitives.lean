import ImbalancedChen.P2N48TermOneAllPatternClosedVolumes
import ImbalancedChen.Certificates.PairedFibreIntegral

/-! SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
Real weighted tied-block moments for the ORIGINAL distinguished z slot.
The three source cases are (r,s)=(0,1),(1,0),(1,1), with factorials 1.
Both the genuine ordered integrals and their signed source J combinations
are proved here. No row endpoint, Z enclosure or numerical result is input.
-/
namespace ImbalancedChen.P2N48TiedMomentPrimitives
noncomputable section
open Set MeasureTheory
open scoped Interval
open ImbalancedChen.OriginalThirdTriangleMomentsSourceOnly
open P2N48GenericTwoThreeTieVolumes

/-- The distinguished squared reciprocal is kept on z, not symmetrized. -/
def zwKernel (p : XY) : ℝ := (1/p.1^2)*(1/p.2)
def uzKernel (p : XY) : ℝ := (1/p.1)*(1/p.2^2)
def tripleKernel (p : Triple) : ℝ := (1/p.1)*(1/p.2.1^2)*(1/p.2.2)

def moment01 (a b : ℝ) : ℝ := 1/a-(1+Real.log (b/a))/b
def moment10 (a b : ℝ) : ℝ := (Real.log (b/a)-1)/a+1/b
def moment11 (a b : ℝ) : ℝ := (Real.log (b/a)-2)/a+(Real.log (b/a)+2)/b

theorem reciprocal_Icc {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, 1/x)=Real.log (b/a) := by
  rw [integral_Icc_eq_integral_Ioc, ←intervalIntegral.integral_of_le hab]
  exact integral_one_div_of_pos ha (ha.trans_le hab)

theorem reciprocalSquared_Icc {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, 1/x^2)=1/a-1/b := by
  have hc : ContinuousOn (fun x : ℝ => 1/x^2) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (ha.trans_le hx.1).ne')
  have hd : ∀ x∈uIcc a b, HasDerivAt (fun y : ℝ => -(1/y)) (1/x^2) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have h := ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x)
      (ha.trans_le hx.1).ne').neg
    apply h.congr_deriv
    dsimp
    ring
  rw [integral_Icc_eq_integral_Ioc, ←intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hab)]
  ring

theorem zwKernel_continuous {a b : ℝ} (ha : 0<a) :
    ContinuousOn zwKernel (xySquare a b) :=
  (continuousOn_const.div (continuous_fst.continuousOn.pow 2)
    (fun p hp => pow_ne_zero 2 (ha.trans_le hp.1.1).ne')).mul
    (continuousOn_const.div continuous_snd.continuousOn
      (fun p hp => (ha.trans_le hp.2.1).ne'))

theorem uzKernel_continuous {a b : ℝ} (ha : 0<a) :
    ContinuousOn uzKernel (xySquare a b) :=
  (continuousOn_const.div continuous_fst.continuousOn
    (fun p hp => (ha.trans_le hp.1.1).ne')).mul
    (continuousOn_const.div (continuous_snd.continuousOn.pow 2)
      (fun p hp => pow_ne_zero 2 (ha.trans_le hp.2.1).ne'))

/-- Actual triangular w<=z integral; inner log arises by real Fubini. -/
theorem zwTriangle_moment {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xyTriangle a b, zwKernel p)=moment01 a b := by
  rw [integral_xyTriangle_nested a b (zwKernel_continuous ha)]
  have hinner : (∫ z in Icc a b, ∫ w in Icc a z, zwKernel (z,w)) =
      ∫ z in Icc a b, Real.log (z/a)/z^2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro z hz
    rw [zwKernel, integral_const_mul, reciprocal_Icc ha hz.1]
    ring
  rw [hinner, integral_Icc_eq_integral_Ioc, ←intervalIntegral.integral_of_le hab]
  exact Certificates.pairedFibreIntegral_eq ha hab

/-- Actual triangular z<=u integral; the z factor is squared. -/
theorem uzTriangle_moment {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xyTriangle a b, uzKernel p)=moment10 a b := by
  rw [integral_xyTriangle_nested a b (uzKernel_continuous ha)]
  have hinner : (∫ u in Icc a b, ∫ z in Icc a u, uzKernel (u,z)) =
      ∫ u in Icc a b, (1/a)*(1/u)-1/u^2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    rw [uzKernel, integral_const_mul, reciprocalSquared_Icc ha hu.1]
    field_simp [(ha.trans_le hu.1).ne'] <;> ring
  have h1 : IntegrableOn (fun u : ℝ => 1/u) (Icc a b) :=
    (continuousOn_const.div continuousOn_id
      (fun u hu => (ha.trans_le hu.1).ne')).integrableOn_Icc
  have h2 : IntegrableOn (fun u : ℝ => 1/u^2) (Icc a b) :=
    (continuousOn_const.div (continuousOn_id.pow 2)
      (fun u hu => pow_ne_zero 2 (ha.trans_le hu.1).ne')).integrableOn_Icc
  rw [hinner, integral_sub (h1.const_mul (1/a)) h2, integral_const_mul,
    reciprocal_Icc ha hab, reciprocalSquared_Icc ha hab]
  unfold moment10
  ring

/-- Genuine weighted triple Fubini, not a constant-density volume theorem. -/
theorem triple_weighted_nested {a b : ℝ} (ha : 0<a) :
    (∫ p in tripleSorted a b, tripleKernel p)=
      ∫ u in Icc a b, (1/u)*(∫ q in xyTriangle a u, zwKernel q) := by
  have hc : ContinuousOn tripleKernel (tripleCube a b) := by
    have h0 : ContinuousOn (fun p : Triple => 1/p.1) (tripleCube a b) :=
      continuousOn_const.div continuous_fst.continuousOn
        (fun p hp => (ha.trans_le hp.1.1).ne')
    have h1 : ContinuousOn (fun p : Triple => 1/p.2.1^2) (tripleCube a b) :=
      continuousOn_const.div ((continuous_fst.comp continuous_snd).continuousOn.pow 2)
        (fun p hp => pow_ne_zero 2 (ha.trans_le hp.2.1.1).ne')
    have h2 : ContinuousOn (fun p : Triple => 1/p.2.2) (tripleCube a b) :=
      continuousOn_const.div (continuous_snd.comp continuous_snd).continuousOn
        (fun p hp => (ha.trans_le hp.2.2.1).ne')
    exact (h0.mul h1).mul h2
  have hCube := hc.integrableOn_compact
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hF : (∫ p in tripleSorted a b, tripleKernel p)=
      ∫ u in Icc a b, ∫ q in Icc a b ×ˢ Icc a b,
        tripleOrder.indicator tripleKernel (u,q) := by
    calc
      _=∫ p in tripleCube a b, tripleOrder.indicator tripleKernel p := by
        rw [setIntegral_indicator measurableSet_tripleOrder]
        rfl
      _=_ := by
        rw [tripleCube, Measure.volume_eq_prod]
        exact setIntegral_prod _ (by
          simpa only [tripleCube, Measure.volume_eq_prod] using
            hCube.indicator measurableSet_tripleOrder)
  rw [hF]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  have hpoint : (fun q : XY => tripleOrder.indicator tripleKernel (u,q))=
      {q : XY | q.2≤q.1 ∧ q.1≤u}.indicator (fun q => (1/u)*zwKernel q) := by
    funext q
    by_cases h : q.2≤q.1 ∧ q.1≤u <;>
      simp [tripleOrder, tripleKernel, zwKernel, h, mul_assoc]
  have hset : (Icc a b ×ˢ Icc a b) ∩ {q : XY | q.2≤q.1 ∧ q.1≤u}=
      xyTriangle a u := by
    ext q
    simp only [mem_inter_iff, mem_prod, mem_Icc, mem_setOf_eq, xyTriangle, xySquare]
    constructor
    · rintro ⟨⟨h0,h1⟩,ho,hup⟩
      exact ⟨⟨⟨h0.1,hup⟩,⟨h1.1,ho.trans hup⟩⟩,ho⟩
    · rintro ⟨⟨h0,h1⟩,ho⟩
      exact ⟨⟨⟨h0.1,h0.2.trans hu.2⟩,⟨h1.1,h1.2.trans hu.2⟩⟩,ho,h0.2⟩
  rw [hpoint, setIntegral_indicator
    ((isClosed_le continuous_snd continuous_fst).inter
      (isClosed_le continuous_fst continuous_const)).measurableSet,
    hset, integral_const_mul]

/-- The outer primitive retains both logarithms from the ordered fibres. -/
theorem tripleTriangle_moment {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in tripleSorted a b, tripleKernel p)=moment11 a b := by
  rw [triple_weighted_nested ha]
  have hinner : (∫ u in Icc a b, (1/u)*(∫ q in xyTriangle a u, zwKernel q))=
      ∫ u in Icc a b, (1/u)*moment01 a u := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    rw [zwTriangle_moment ha hu.1]
  rw [hinner]
  let F : ℝ→ℝ := fun u => Real.log (u/a)/a+(Real.log (u/a)+2)/u
  have hc : ContinuousOn (fun u : ℝ => (1/u)*moment01 a u) (Icc a b) := by
    have hn : ∀ u∈Icc a b, u≠0 := fun u hu => (ha.trans_le hu.1).ne'
    have hlog : ContinuousOn (fun u : ℝ => Real.log (u/a)) (Icc a b) :=
      (continuousOn_id.div_const a).log (fun u hu => div_ne_zero (hn u hu) ha.ne')
    exact (continuousOn_const.div continuousOn_id hn).mul
      (continuousOn_const.sub ((continuousOn_const.add hlog).div continuousOn_id hn))
  have hd : ∀ u∈uIcc a b, HasDerivAt F ((1/u)*moment01 a u) u := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    have hu0 := (ha.trans_le hu.1).ne'
    have hlog : HasDerivAt (fun x : ℝ => Real.log (x/a)) (1/u) u := by
      have h := ((hasDerivAt_id u).div_const a).log (div_ne_zero hu0 ha.ne')
      apply h.congr_deriv
      field_simp [ha.ne', hu0] <;> ring
    have h := (hlog.div_const a).add
      ((hlog.add_const 2).div (hasDerivAt_id u) hu0)
    apply h.congr_deriv
    dsimp [moment01]
    field_simp [ha.ne', hu0] <;> ring
  rw [integral_Icc_eq_integral_Ioc, ←intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hab)]
  dsimp [F, moment11]
  rw [div_self ha.ne', Real.log_one]
  ring

/-- The source's signed incomplete exponential moments, for m<=3. -/
def J0 (a b : ℝ) : ℝ := 1-a/b
def J1 (a b : ℝ) : ℝ := 1-(a/b)*(1+Real.log (b/a))
def J2 (a b : ℝ) : ℝ := 2-(a/b)*(Real.log (b/a)^2+2*Real.log (b/a)+2)

theorem original_rs01_formula {a b : ℝ} (ha : a≠0) (hb : b≠0) :
    (1/a)*J1 a b=moment01 a b := by
  unfold J1 moment01
  field_simp [ha,hb] <;> ring

theorem original_rs10_formula {a b : ℝ} (ha : a≠0) (hb : b≠0) :
    (1/a)*(Real.log (b/a)*J0 a b-J1 a b)=moment10 a b := by
  unfold J0 J1 moment10
  field_simp [ha,hb] <;> ring

theorem original_rs11_formula {a b : ℝ} (ha : a≠0) (hb : b≠0) :
    (1/a)*(Real.log (b/a)*J1 a b-J2 a b)=moment11 a b := by
  unfold J1 J2 moment11
  field_simp [ha,hb] <;> ring

/-- Actual r=0,s=1 source block, with its signed J1 term. -/
theorem zwTriangle_original_rs {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xyTriangle a b,zwKernel p)=(1/a)*J1 a b := by
  rw [zwTriangle_moment ha hab,original_rs01_formula ha.ne' (ha.trans_le hab).ne']

/-- Actual r=1,s=0 source block: subtract J1, do not add it. -/
theorem uzTriangle_original_rs {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xyTriangle a b,uzKernel p)=
      (1/a)*(Real.log (b/a)*J0 a b-J1 a b) := by
  rw [uzTriangle_moment ha hab,original_rs10_formula ha.ne' (ha.trans_le hab).ne']

/-- Actual r=1,s=1 source block: L*J1-J2, not a volume divided by 3!. -/
theorem tripleTriangle_original_rs {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in tripleSorted a b,tripleKernel p)=
      (1/a)*(Real.log (b/a)*J1 a b-J2 a b) := by
  rw [tripleTriangle_moment ha hab,original_rs11_formula ha.ne' (ha.trans_le hab).ne']

end
end ImbalancedChen.P2N48TiedMomentPrimitives
