import ImbalancedChen.Part3OriginalAbelKernel
import ImbalancedChen.Part3OriginalFullModulusTestJets
import ImbalancedChen.Part3CompactCoordinateFourier

/-! Product profile for the original period-64 cutoff and phase. -/
namespace ImbalancedChen.Part3.OriginalPrescribedAbelProfile
noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology Convolution
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)
open OriginalFullModulusTestJets20261102 (spectralTest_tsupport_strict)
open OriginalAbelKernel

def lo (Y : ℝ) := (Y/(64*Real.pi))^2
def hi (Y : ℝ) := (4*Y/Real.pi)^2

def F (ell : D4→ℤ) (Y p : ℝ) : ℂ :=
  spectralTest ell Y (4*Real.pi*Real.sqrt p)/(Real.sqrt p:ℂ)
def f (ell : D4→ℤ) (Y : ℝ) := inverse (F ell Y)
def h (ell : D4→ℤ) (Y p : ℝ) : ℂ := ((p*Real.sqrt p:ℝ):ℂ)*f ell Y p

theorem lo_pos {Y : ℝ} (hY : 0<Y) : 0<lo Y := by unfold lo; positivity

private lemma F_ne {ell : D4→ℤ} {Y p : ℝ} (hY : 0<Y) (hp : F ell Y p≠0) :
    lo Y<p ∧ p<hi Y := by
  have h0 : 0<p := by
    by_contra! hn
    simp [F,Real.sqrt_eq_zero_of_nonpos hn] at hp
  have hphi : spectralTest ell Y (4*Real.pi*Real.sqrt p)≠0 :=
    fun h => hp (by simp [F,h])
  obtain ⟨hl,hu⟩ := spectralTest_tsupport_strict ell hY (subset_tsupport _ hphi)
  have bl : Y/(64*Real.pi)<Real.sqrt p := by
    apply (div_lt_iff₀ (by positivity)).mpr; nlinarith
  have bu : Real.sqrt p<4*Y/Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).mpr; nlinarith
  exact ⟨(sq_lt_sq' (by positivity : -(Real.sqrt p)<Y/(64*Real.pi)) bl).trans_eq
    (Real.sq_sqrt h0.le), (Real.sq_sqrt h0.le).symm.trans_lt
    (sq_lt_sq' (by positivity : -(4*Y/Real.pi)<Real.sqrt p) bu)⟩

theorem F_support (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    tsupport (F ell Y) ⊆ Icc (lo Y) (hi Y) :=
  closure_minimal (fun _ hp => ⟨(F_ne hY hp).1.le,(F_ne hY hp).2.le⟩) isClosed_Icc

theorem F_smooth (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : ContDiff ℝ ∞ (F ell Y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hpos : 0<p
  · have sq : ContDiffAt ℝ ∞ Real.sqrt p := Real.contDiffAt_sqrt hpos.ne'
    have num := (spectralTest_contDiff ell Y).contDiffAt.comp p
      ((contDiffAt_const (c := 4*Real.pi)).mul sq)
    have den := Complex.ofRealCLM.contDiff.contDiffAt.comp p sq
    simpa only [F,div_eq_mul_inv,Function.comp_def] using
      num.mul (den.inv (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'))
  · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds (lt_of_le_of_lt (le_of_not_gt hpos) (lo_pos hY))] with x hx
    by_contra hn
    exact (F_ne hY hn).1.not_ge hx.le

theorem F_compact (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : HasCompactSupport (F ell Y) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (F_support ell hY)

theorem inverse_exact (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (k : ℝ) :
    A (f ell Y) k=F ell Y k := invert (F_smooth ell hY) (F_compact ell hY) k

private abbrev dJet (ell : D4→ℤ) (Y : ℝ) (j : ℕ) := iteratedDeriv j (D (F ell Y))

theorem f_smooth (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : ContDiff ℝ ∞ (f ell Y) :=
  contDiff_const.mul ((D_compact (F_compact ell hY)).contDiff_convolution_right
    (lsmul ℝ ℝ) K_integrable.locallyIntegrable (D_smooth (F_smooth ell hY)))

private lemma dj_support (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (j : ℕ) :
    tsupport (dJet ell Y j) ⊆ Icc (lo Y) (hi Y) := by
  refine (P3CompactCoordinateSourceOnly.jet_tsupport_subset _ _).trans ?_
  exact (tsupport_add _ _).trans (union_subset (tsupport_deriv_subset.trans (F_support ell hY))
    (F_support ell hY))

theorem smooth_jet {G : ℝ→ℂ} (hG : ContDiff ℝ ∞ G) (j : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv j G) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv j hG

private theorem dj_smooth (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (j : ℕ) :
    ContDiff ℝ ∞ (dJet ell Y j) :=
  smooth_jet (D_smooth (F_smooth ell hY)) j

theorem f_jet_integral (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (j : ℕ) :
    iteratedDeriv j (f ell Y) = fun p => (Real.pi:ℂ)⁻¹ * A (dJet ell Y j) p := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ,ih]; ext p
    have hc : HasCompactSupport (dJet ell Y j) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (dj_support ell hY j)
    have J := hc.hasDerivAt_convolution_right (lsmul ℝ ℝ) K_integrable.locallyIntegrable
      ((dj_smooth ell hY j).of_le (by simp)) p
    simpa only [dJet,iteratedDeriv_succ] using (J.const_mul (Real.pi:ℂ)⁻¹).deriv

theorem f_jet_below (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (j : ℕ) {p : ℝ} (hp : p≤lo Y) :
    iteratedDeriv j (f ell Y) p=0 := by
  rw [f_jet_integral ell hY j,show A (dJet ell Y j) p=0 from ?_,mul_zero]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  by_cases hu : 0<u
  · have zz := image_eq_zero_of_notMem_tsupport (f := dJet ell Y j)
      (show p-u∉tsupport (dJet ell Y j) from fun H => (not_le.mpr (by linarith)) (dj_support ell hY j H).1)
    simp [zz]
  · simp [K,hu]

/-- Exponential tilting moves half of the decay to the smooth compact
factor. This bound includes the whole half-line and every derivative. -/
theorem f_jet_decay (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (j : ℕ) :
    ∃C : ℝ, 0≤C ∧ ∀p, ‖iteratedDeriv j (f ell Y) p‖≤C*Real.exp (-p/2) := by
  let D := dJet ell Y j
  have hc : HasCompactSupport D :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (dj_support ell hY j)
  let W : ℝ→ℂ := fun x => (Real.exp (x/2):ℂ)*D x
  have hw : Continuous W := by dsimp [W,D]; fun_prop (disch := exact (dj_smooth ell hY j).continuous)
  obtain ⟨B,hB⟩ := hw.norm.bddAbove_range_of_hasCompactSupport (hc.mul_left : HasCompactSupport W).norm
  have B0 : 0≤B := (norm_nonneg (W 0)).trans (hB (mem_range_self _))
  let M : ℝ→ℝ := fun u => (Real.sqrt 2)⁻¹ * K (u/2)
  have Mpos (u : ℝ) : 0≤M u := mul_nonneg (by positivity) (K_nonneg _)
  have M_int : Integrable M := (K_integrable.comp_div (by norm_num : (2:ℝ)≠0)).const_mul _
  refine ⟨‖(Real.pi:ℂ)⁻¹‖*((∫u:ℝ,M u)*B),by positivity [integral_nonneg Mpos],?_⟩
  intro p
  have dom (u : ℝ) : ‖K u • D (p-u)‖ ≤ M u*(B*Real.exp (-p/2)) := by
    by_cases h : 0<u
    · have eqn : K u=M u*Real.exp (-u/2) := by
        dsimp [M,K]; rw [if_pos h,if_pos (half_pos h),Real.sqrt_div h.le]
        have su := (Real.sqrt_pos.mpr h).ne'
        have st : Real.sqrt 2≠0 := by positivity
        rw [show -u= -(u/2)+(-u/2) by ring,Real.exp_add]
        field_simp [su,st]; ring
      have val := hB (mem_range_self (p-u))
      change ‖W (p-u)‖≤B at val
      simp only [W,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le] at val
      rw [norm_smul,Real.norm_of_nonneg (K_nonneg _),eqn]
      calc
        _ = (M u*Real.exp (-p/2))*(Real.exp ((p-u)/2)*‖D (p-u)‖) := by
          rw [show -u/2= -p/2+(p-u)/2 by ring, Real.exp_add]; ring
        _ ≤ _ := by grw [val]; ring_nf
    · simp [K,h,M,show ¬0<u/2 by linarith]
  rw [f_jet_integral ell hY j,norm_mul]
  have bnd := (norm_integral_le_of_norm_le (M_int.mul_const (B*Real.exp (-p/2)))
    (ae_of_all _ dom))
  rw [integral_mul_const] at bnd
  change _*‖∫u:ℝ,K u • D (p-u)‖≤_
  grw [bnd]; ring_nf

end
end ImbalancedChen.Part3.OriginalPrescribedAbelProfile
