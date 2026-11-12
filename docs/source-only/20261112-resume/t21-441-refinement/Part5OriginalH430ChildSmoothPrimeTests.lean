import ImbalancedChen.Part5OriginalCausalSmoothAtlas
import ImbalancedChen.Part5OriginalBuchstabTrueAtomLimits
import ImbalancedChen.Part5OriginalH430TrueAtomLimits

/-! Place a fixed pre-N smooth test on the *new* native prime coordinate(s),
not just on the old positive parent. The physical test is φ(L • u), with L
varying over the whole genuine residual interval. The compact-parameter
prime theorem controls it before N. Both Buchstab polarities and all 401 atoms
are simultaneously summed in absolute value, including the closed knots.
Source only. `trueSingleTest` still precedes a request-specific ceiling/prefix
trim; no change of the original ordinary/positive-switching base is asserted. -/
namespace ImbalancedChen.Part5OriginalH430ChildSmoothPrimeTests
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology Pointwise
open Part5OriginalCausalSmoothAtlas
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalCompactThetaMass
open P2OriginalCompactMovingGateMass P2OriginalCompactScaledPrimeMass
open P2OriginalAffineProfilePassage P2OriginalClosedCellProfileAtoms
open P2OriginalOldProfilePrimeLimits P2OriginalPhysicalOldProfileMass
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalBuchstabCompactAtoms

def childTest {d : ℕ} (P : Plan) (j : Box P d) (L : ℝ) (f : Coord d → ℝ)
    (x : Coord d) : ℝ := f x * atom P j (L • x)

theorem childTest_bound {d : ℕ} (P : Plan) (j : Box P d) (L : ℝ) {B : ℝ}
    (f : Coord d → ℝ) (hf : ∀ x, |f x| ≤ B) (x : Coord d) : |childTest P j L f x| ≤ B := by
  rw [childTest,abs_mul,abs_of_nonneg (atom_nonneg _ _ _)]
  exact ((mul_le_mul_of_nonneg_left (atom_le_one P j _) (abs_nonneg (f x))).trans
    (by simpa only [mul_one] using hf x))

/-- Exact old parameter sandwich with its kernel multiplied on the PHYSICAL
coordinates by the requested native child label. All compact-parameter and
arithmetic quantities are the old definitions; no weak-limit premise. -/
theorem scaled_child_limit {V : Type*} [MetricSpace V] {d r : ℕ}
    (P : Plan) (j : Box P d) {K : Set V} (hK : IsCompact K)
    {Lmin Lmax B epsilon : ℝ} (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax)
    (hB : 0 ≤ B) (he : 0 < epsilon)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ i, A i ≠ 0)
    (c : V → Fin r → ℝ) (hc : ∀ i, Continuous (fun q => c q i))
    (D : V → Set (Coord d)) (hD : ∀ q ∈ K, AffineSandwich A (c q) (D q))
    (hbox : ∀ q ∈ K, D q ⊆ cube d)
    (f : Coord d → ℝ) (hf : Continuous f) (hb : ∀ x, |f x| ≤ B) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax, ∀ q ∈ K,
      |scaledPrimeSum N L (D q) (childTest P j L f) -
        (∫ u in D q, childTest P j L f u * ∏ i, 1/u i)| < epsilon := by
  let E (z : ℝ × V) : Set (Coord d) := {x | z.1⁻¹ • x ∈ D z.2}
  let C (z : ℝ × V) (i : Fin r) : ℝ := z.1*c z.2 i
  let F (z : (ℝ × V) × Coord d) : ℝ := dilationKernel Lmin f (z.1.1,z.2) * atom P j z.2
  have hC (i : Fin r) : Continuous (fun z : ℝ × V => C z i) := continuous_fst.mul ((hc i).comp continuous_snd)
  have hF : Continuous F :=
    ((dilationKernel_continuous hmin f hf).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).mul
      ((atom_smooth P j).continuous.comp continuous_snd)
  have hFb (z : ℝ × V) (x : Coord d) : |F (z,x)| ≤ B := by
    unfold F
    rw [abs_mul,abs_of_nonneg (atom_nonneg _ _ _)]
    exact (mul_le_mul_of_nonneg_left (atom_le_one P j x) (abs_nonneg _)).trans
      (by simpa only [mul_one,dilationKernel] using hb ((max (Lmin/2) z.1)⁻¹ • x))
  obtain ⟨T,hT⟩ := Part5OriginalCompactParameterSandwich.compact_uniform_sandwich
    (isCompact_Icc.prod hK) (a := Lmin/20) (b := Lmax) (by positivity) (by linarith) hB
    A hA C hC E (fun z hz => scaled_sandwich (hmin.trans_le hz.1.1) A (c z.2) (hD z.2 hz.2))
    F hF (fun z _ x _ => hFb z x) he
  refine ⟨max 2 T,?_⟩
  intro N hN L hL q hq
  have hh := hT N (by omega) (L,q) ⟨hL,hq⟩
  have hL0 := (hmin.trans_le hL.1).ne'
  have hFq : (fun x => F ((L,q),x)) = (fun x => childTest P j L f (L⁻¹ • x)) := by
    funext x
    simp only [F,dilationKernel_on_interval hmin hL,childTest,smul_smul,mul_inv_cancel₀ hL0,one_smul]
  rw [hFq] at hh
  rw [scaled_sum_rebox (by omega : 1 < N) hmin hL (D q) (hbox q hq)]
  rw [← scaled_integral_rebox hmin hL (D q) (hbox q hq)]
  exact hh

def BIndex (P : Plan) := Bool × FloorAtom × Box P 1
instance (P : Plan) : Fintype (BIndex P) := inferInstanceAs (Fintype (Bool × FloorAtom × Box P 1))

def bGap (P : Plan) (N d : ℕ) (L c : ℝ) (i : BIndex P) : ℝ :=
  let D := Part5OriginalBuchstabCompactAtoms.atomDomain i.1 i.2.1 c
  let f := childTest P i.2.2 L residualSingle
  |trueSingleTest N L d D f - (∫ u in D, f u * ∏ a, 1/u a)|

/-- Source-side theta multiplier on the true integer prime tuples; both
orientations and knots have exactly their original compact moving domains. -/
theorem buchstab_child_limit (P : Plan) (i : BIndex P) {F G e : ℝ}
    (hF : 0 < F) (hG : F ≤ G) (he : 0 < e) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc F G, ∀ c ∈ Icc (1:ℝ) 6, ∀ d : ℕ,
      bGap P N d L c i < e := by
  obtain ⟨TH,hH⟩ := scaled_child_limit P i.2.2 (K := Icc (1:ℝ) 6) isCompact_Icc hF hG
    (by norm_num : (0:ℝ) ≤ 10) (by positivity : 0 < e/2)
    (atomForms i.1 i.2.1) (atomForms_nonzero i.1 i.2.1)
    (atomBounds i.1 i.2.1) (atomBounds_continuous i.1 i.2.1)
    (Part5OriginalBuchstabCompactAtoms.atomDomain i.1 i.2.1) (fun c _ => atom_sandwich i.1 i.2.1 c)
    (fun c _ => atom_in_cube i.1 i.2.1 c) residualSingle residualSingle_continuous
    (fun u => by rw [abs_of_nonneg (residualSingle_bounds u).1]; exact (residualSingle_bounds u).2)
  obtain ⟨TM,hM⟩ := compact_multiplier_error (k := 1) hF hG (by norm_num : (0:ℝ) ≤ 20)
    (by positivity : 0 < e/2)
  refine ⟨max TH TM,?_⟩
  intro N hN L hL c hc d
  let D := Part5OriginalBuchstabCompactAtoms.atomDomain i.1 i.2.1 c
  let f := childTest P i.2.2 L residualSingle
  have hf (u : Coord 1) : |f u| ≤ 10 := childTest_bound P i.2.2 L residualSingle
    (fun v => by rw [abs_of_nonneg (residualSingle_bounds v).1]; exact (residualSingle_bounds v).2) u
  obtain ⟨hA,hm⟩ := hM N (by omega) L hL
  have h1 := trueSingleTest_error d D f (by norm_num : (0:ℝ) ≤ 10) hf hA
  have h2 := hH N (by omega) L hL c hc
  have ht := abs_sub_le (trueSingleTest N L d D f) (scaledPrimeSum N L D f)
    (∫ u in D, f u * ∏ a, 1/u a)
  change |scaledPrimeSum N L D f - (∫ u in D, f u * ∏ a, 1/u a)| < e/2 at h2
  change |trueSingleTest N L d D f - (∫ u in D, f u * ∏ a, 1/u a)| < e
  norm_num only at h1
  linarith

/-- The error currency is a sum of ABSOLUTE errors over the full fixed
child-label catalogue. No N-dependent list of thresholds and no factor of
the number of labels is hidden; delta/(card+1) precedes the cutoff. -/
theorem all_buchstab_child_labels (P : Plan) {F G delta : ℝ}
    (hF : 0 < F) (hG : F ≤ G) (hd : 0 < delta) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc F G, ∀ c ∈ Icc (1:ℝ) 6, ∀ d : ℕ,
      (∑ i : BIndex P, bGap P N d L c i) ≤ delta := by
  let M : ℝ := Fintype.card (BIndex P)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  let e := delta / (M+1)
  have he : 0 < e := div_pos hd (by linarith)
  have hall (i : BIndex P) : ∀ᶠ N : ℕ in atTop, ∀ L ∈ Icc F G,
      ∀ c ∈ Icc (1:ℝ) 6, ∀ d : ℕ, bGap P N d L c i < e := by
    obtain ⟨T,h⟩ := buchstab_child_limit P i hF hG he
    exact (eventually_ge_atTop T).mono (fun N hN => h N hN)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hall)
  refine ⟨T,?_⟩
  intro N hN L hL c hc d
  calc
    _ ≤ ∑ _i : BIndex P, e := Finset.sum_le_sum (fun i _ => (hT N hN i L hL c hc d).le)
    _ = M*e := by simp [M,nsmul_eq_mul]
    _ ≤ (M+1)*e := mul_le_mul_of_nonneg_right (by linarith) he.le
    _ = delta := by unfold e; field_simp [show M+1 ≠ 0 by linarith]

end
end ImbalancedChen.Part5OriginalH430ChildSmoothPrimeTests
