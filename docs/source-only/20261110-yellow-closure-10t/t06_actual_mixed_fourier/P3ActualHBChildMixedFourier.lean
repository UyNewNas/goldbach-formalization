import ImbalancedChen.P3HBSmoothLogFiniteDerivatives
import ImbalancedChen.P5ActualAllRankOccurrenceFourierBridge

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.
Manuscript 9731290e8f53cffda44129906cde6a965eaa869b, prime-product
completion §§2,4(F). Lean v4.33.0-rc1; Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

The real cutoff here is the ALREADY DEFINED original chi in
P5ActualEtaPsiOccurrenceBudget. Its complexification is substituted into
the ALREADY DEFINED P3 smoothChild. The actual positional child is never
substituted for W_T: refinedChart is actualChart * shiftedChildTensor. actualChart
retains ambient W_T, original owner/group products, complete-product trim,
group psi and the original fixed compact plateau. Ordered derivative
allocation lists retain every cross term and repeated coordinate.

The old Family's mixedEuler field is a primitive SUP bound on the original
ambient W, stronger than a merely integrated Euler class. This file does
not construct the actual manuscript caller families or remove that field.
The uniform dimension is the actual HB occurrence dimension m<=6*kStar;
the atlas mesh parameter m(N) of the distinct U5 root-atlas is not this m.
-/

namespace ImbalancedChen.P3ActualHBChildMixedFourier
noncomputable section
open Classical MeasureTheory Set Filter
open scoped BigOperators Topology
open P3HBSmoothThreeWayRatioTwo P3HBSmoothLogScaleBudget
open P3HBSmoothLogFiniteDerivatives
open P5Z.AdmissibleAllRankIntegerGeometricFamily
open P5Z.GroupedOccurrenceLogShift P5Z.AllWordAmbientOccurrenceBound
open P5Z.OccurrenceWordFourFactorLeibniz
open P5Z.ActualOccurrencePlateauWordBudget P5Z.ActualEtaPsiOccurrenceBudget
open P5Z.AllRankCoordinateFourierIBP P5Z.AllRankMixedOperatorBudget
open P5Z.AllRankCauchyKernelIntegral
open P5Z.ActualEuclideanPhysicalFourier P5Z.OccurrenceEuclideanMixedIntegral
open P5Z.ActualAllRankOccurrenceFourierBridge

/-- The real version of the SAME three original overlapping child gates. -/
def childGate (t : ℝ) (a : Fin 3) : ℝ :=
  if a = 0 then chi (4*t-2)
  else if a = 1 then chi (4*t-3)-chi (4*t-2)
  else 1-chi (4*t-3)

def childLog (a : Fin 3) (u : ℝ) : ℝ :=
  psiLog u * childGate (Real.exp u) a

theorem childLog_ofReal (a : Fin 3) (u : ℝ) :
    (childLog a u : ℂ) = logChild (fun t => (chi t : ℂ)) a u := by
  fin_cases a <;>
    simp [childLog, childGate, logChild, smoothGate, psiLog, psi]

theorem chi_smooth : ContDiff ℝ ∞ chi := contDiff_const.sub eta_smooth

theorem childGate_smooth (a : Fin 3) : ContDiff ℝ ∞ (fun t => childGate t a) := by
  have h0 : ContDiff ℝ ∞ (fun t : ℝ => chi (4*t-2)) :=
    chi_smooth.comp (by fun_prop)
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => chi (4*t-3)) :=
    chi_smooth.comp (by fun_prop)
  fin_cases a
  · simpa [childGate] using h0
  · simpa [childGate] using h1.sub h0
  · simpa [childGate] using contDiff_const.sub h1

theorem childLog_smooth (a : Fin 3) : ContDiff ℝ ∞ (childLog a) :=
  psiLog_smooth.mul ((childGate_smooth a).comp Real.contDiff_exp)

theorem childLog_sum (u : ℝ) : (∑ a : Fin 3, childLog a u) = psiLog u := by
  simp only [childLog, ← Finset.mul_sum]
  have hg : (∑ a : Fin 3, childGate (Real.exp u) a) = 1 := by
    simp [Fin.sum_univ_succ, childGate]
    ring
  rw [hg, mul_one]

/-- Necessary real/complex conversion for this actual scalar cutoff;
the earlier complex C_K is reused, rather than re-proved by compactness. -/
theorem childLog_iterated_ofReal (a : Fin 3) (n : ℕ) :
    iteratedDeriv n (logChild (fun t => (chi t : ℂ)) a) =
      fun u => (iteratedDeriv n (childLog a) u : ℂ) := by
  induction n with
  | zero =>
      funext u
      exact (childLog_ofReal a u).symm
  | succ n ih =>
      funext u
      rw [iteratedDeriv_succ, ih]
      have hd : Differentiable ℝ (iteratedDeriv n (childLog a)) :=
        ContDiff.differentiable_iteratedDeriv' n
          ((childLog_smooth a).of_le (by simp))
      simpa only [iteratedDeriv_succ] using
        ((hd u).hasDerivAt.ofReal_comp).deriv

/-- Genuine derivatives vanish off the original compact log window. -/
theorem childLog_derivative_zero_outside (a : Fin 3) (n : ℕ) {u : ℝ}
    (hu : u ∉ Icc (-Real.log 2) (Real.log 2)) :
    iteratedDeriv n (childLog a) u = 0 := by
  have heq : childLog a =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
    by_cases hl : u < -Real.log 2
    · filter_upwards [Iio_mem_nhds hl] with v hv
      simp only [childLog, psiLog_zero_left hv.le, zero_mul]
    · have hr : Real.log 2 < u := by
        by_contra hn
        exact hu ⟨le_of_not_gt hl, le_of_not_gt hn⟩
      filter_upwards [Ioi_mem_nhds hr] with v hv
      simp only [childLog, psiLog_zero_right hv.le, zero_mul]
  simpa using Filter.EventuallyEq.iteratedDeriv_eq n heq

/-- Same C_K for all three children, now on the whole real line.
No T, dyadic label, target, owner or modulus enters its selection. -/
theorem exists_childLog_global_budget (K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (a : Fin 3) (u : ℝ),
      n ≤ K → |iteratedDeriv n (childLog a) u| ≤ C := by
  have hchi : ContDiff ℝ ∞ (fun t : ℝ => (chi t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp chi_smooth
  obtain ⟨B, hB, hb⟩ := logChild_uniform_finite_order
    (fun t => (chi t : ℂ)) hchi K
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro n a u hn
  by_cases hu : u ∈ Icc (-Real.log 2) (Real.log 2)
  · have h := hb n a u hn hu
    rw [childLog_iterated_ofReal] at h
    have hr : |iteratedDeriv n (childLog a) u| ≤ B := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using h
    exact hr.trans (le_max_right _ _)
  · rw [childLog_derivative_zero_outside a n hu, abs_zero]
    exact zero_le_one.trans (le_max_left _ _)

/-- The actual child in each ORIGINAL HB occurrence coordinate. -/
def childTensor {m : ℕ} (child : Fin m → Fin 3) : (Fin m → ℝ) → ℝ :=
  groupTensor id (fun _ => 0) (fun i => childLog (child i))

theorem childTensor_eq_product {m : ℕ} (child : Fin m → Fin 3) (z : Fin m → ℝ) :
    childTensor child z = ∏ i : Fin m, childLog (child i) (z i) := by
  simp [childTensor, groupTensor, groupLog]

/-- Exact identification with the existing six labelled smooth HB factors,
BEFORE taking absolute values or differentiating. -/
theorem six_childTensor_eq_original (label : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (z : Fin 6 → ℝ) :
    (childTensor child z : ℂ) =
      ∏ i : Fin 6, smoothCoord (fun t => (chi t : ℂ))
        ((2 : ℝ)^(label i)*Real.exp (z i)) (label i) (child i) := by
  rw [childTensor_eq_product, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [smoothCoord_log_exact]
  exact childLog_ofReal (child i) (z i)

/-- Actual integer six-slot HB tensor, with the same positional getD
padding and labels as the original source. -/
theorem six_childTensor_eq_smoothTensor (label : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (marked hb : List ℕ) (z : Fin 6 → ℝ)
    (hz : ∀ i : Fin 6, ((hb.getD i.val 1 : ℕ) : ℝ) =
      (2 : ℝ)^(label i)*Real.exp (z i)) :
    (childTensor child z : ℂ) =
      smoothTensor (fun t => (chi t : ℂ)) label child marked hb := by
  rw [six_childTensor_eq_original]
  unfold smoothTensor
  apply Finset.prod_congr rfl
  intro i hi
  rw [hz i]

/-- The true mixed derivative/product identity. Each occurrence of a
coordinate increments exactly its own factor, including repetitions.
This is an equality of ordinary derivatives, using the existing exact
occOne_groupTensor calculation, not a definition of a formal derivative. -/
theorem occWord_childTensor {m : ℕ} (child : Fin m → Fin 3)
    (w : List (Fin m)) :
    occWord w (childTensor child) =
      fun z => ∏ i : Fin m,
        iteratedDeriv (w.count i) (childLog (child i)) (z i) := by
  have h : occWord w (childTensor child) =
      groupTensor id (fun _ => 0)
        (fun i => iteratedDeriv (w.count i) (childLog (child i))) := by
    induction w with
    | nil => simp [occWord, childTensor]
    | cons a w ih =>
        change occOne a (occWord w (childTensor child)) = _
        rw [ih]
        funext z
        rw [occOne_groupTensor]
        congr 1
        funext i x
        by_cases hi : i = a
        · subst i
          simp [iteratedDeriv_succ]
        · simp [hi, Ne.symm hi, Function.update_of_ne hi]
  rw [h]
  funext z
  simp [groupTensor, groupLog]

theorem childTensor_smooth {m : ℕ} (child : Fin m → Fin 3) :
    ContDiff ℝ ∞ (childTensor child) := by
  have heq : childTensor child = fun z => ∏ i : Fin m, childLog (child i) (z i) :=
    funext (childTensor_eq_product child)
  rw [heq]
  apply contDiff_prod
  intro i hi
  exact (childLog_smooth (child i)).comp (contDiff_apply ℝ ℝ i)

def childBox (m : ℕ) : Set (Fin m → ℝ) :=
  Icc (fun _ => -Real.log 2) (fun _ => Real.log 2)

theorem childTensor_support {m : ℕ} (child : Fin m → Fin 3) :
    Function.support (childTensor child) ⊆ childBox m := by
  intro z hz
  have hcoord (i : Fin m) : z i ∈ Icc (-Real.log 2) (Real.log 2) := by
    by_contra hn
    have heq : childLog (child i) (z i) = 0 := by
      simpa only [iteratedDeriv_zero] using childLog_derivative_zero_outside (child i) 0 hn
    apply hz
    rw [childTensor_eq_product]
    exact Finset.prod_eq_zero (Finset.mem_univ i) heq
  exact ⟨fun i => (hcoord i).1, fun i => (hcoord i).2⟩

theorem childTensor_compact {m : ℕ} (child : Fin m → Fin 3) :
    HasCompactSupport (childTensor child) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (childTensor_support child)

theorem childTensor_mixed_support {m : ℕ} (child : Fin m → Fin 3)
    (w : List (Fin m)) : tsupport (occWord w (childTensor child)) ⊆ childBox m :=
  (occWord_tsupport_subset m _ (childTensor_smooth child) w).trans
    (closure_minimal (childTensor_support child) isClosed_Icc)

/-- This now bounds the ACTUAL mixed derivative, not a product of
unidentified derivative norms. The exponent is the true slot count. -/
theorem childTensor_word_bound {m : ℕ} (child : Fin m → Fin 3)
    (w : List (Fin m)) (z : Fin m → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n ≤ w.length, ∀ a u, |iteratedDeriv n (childLog a) u| ≤ C) :
    |occWord w (childTensor child) z| ≤ C^m := by
  rw [occWord_childTensor, Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin m, C := by
      apply Finset.prod_le_prod (fun i hi => abs_nonneg _)
      intro i hi
      exact hb (w.count i) (count_le_word_length w i) (child i) (z i)
    _ = C^m := by simp

/-- Whole-space integrated mixed derivative budget on the actual fixed
child support. Its mass and C_K are fixed before all dyadic labels/T. -/
theorem childTensor_mixed_integral_bound {m : ℕ} (child : Fin m → Fin 3)
    (w : List (Fin m)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n ≤ w.length, ∀ a u, |iteratedDeriv n (childLog a) u| ≤ C) :
    (∫ z, |occWord w (childTensor child) z|) ≤
      (volume (childBox m)).toReal * C^m := by
  let f := occWord w (childTensor child)
  have hc : Continuous f := (occWord_smooth w _ (childTensor_smooth child)).continuous
  have hs : ∀ z ∉ childBox m, f z = 0 := by
    intro z hz
    by_contra hn
    exact hz (childTensor_mixed_support child w (subset_tsupport f hn))
  have heq : (fun z => |f z|) = (childBox m).indicator (fun z => |f z|) := by
    funext z
    by_cases hz : z ∈ childBox m
    · simp [hz]
    · simp [hz, hs z hz]
  have hi := integral_mono
    (ContinuousOn.integrableOn_compact isCompact_Icc hc.abs.continuousOn)
    (ContinuousOn.integrableOn_compact isCompact_Icc continuous_const.continuousOn)
    (fun z => childTensor_word_bound child w z C hC hb)
  calc
    _ = ∫ z in childBox m, |f z| := by rw [heq, integral_indicator measurableSet_Icc]
    _ ≤ ∫ _z : Fin m → ℝ in childBox m, C^m := hi
    _ = _ := by simp

/-- Actual Fourier coordinates use a lower rectangle endpoint U, whereas
the original smooth child is normalized at 2^j. The translation is kept
as literal later data, rather than identifying these different bases. -/
def shiftedChildTensor {m : ℕ} (offset : Fin m → ℝ) (child : Fin m → Fin 3) :
    (Fin m → ℝ) → ℝ :=
  groupTensor id offset (fun i => childLog (child i))

theorem shiftedChildTensor_eq_product {m : ℕ} (offset : Fin m → ℝ)
    (child : Fin m → Fin 3) (z : Fin m → ℝ) :
    shiftedChildTensor offset child z =
      ∏ i : Fin m, childLog (child i) (offset i+z i) := by
  simp [shiftedChildTensor, groupTensor, groupLog]

/-- Exact finite restoration of the original individual dyadic tensor;
no label or coefficient is selected after observing a discrepancy sign. -/
theorem shiftedChildTensor_children_sum {m : ℕ} (offset : Fin m → ℝ)
    (z : Fin m → ℝ) :
    (∑ child : Fin m → Fin 3, shiftedChildTensor offset child z) =
      ∏ i : Fin m, psiLog (offset i+z i) := by
  simp_rw [shiftedChildTensor_eq_product]
  rw [← Fintype.prod_sum]
  simp_rw [childLog_sum]

/-- All actual repeated coordinate partials retain the same offsets. -/
theorem occWord_shiftedChildTensor {m : ℕ} (offset : Fin m → ℝ)
    (child : Fin m → Fin 3) (w : List (Fin m)) :
    occWord w (shiftedChildTensor offset child) =
      fun z => ∏ i : Fin m,
        iteratedDeriv (w.count i) (childLog (child i)) (offset i+z i) := by
  have h : occWord w (shiftedChildTensor offset child) =
      groupTensor id offset
        (fun i => iteratedDeriv (w.count i) (childLog (child i))) := by
    induction w with
    | nil => simp [occWord, shiftedChildTensor]
    | cons a w ih =>
        change occOne a (occWord w (shiftedChildTensor offset child)) = _
        rw [ih]
        funext z
        rw [occOne_groupTensor]
        congr 1
        funext i x
        by_cases hi : i = a
        · subst i
          simp [iteratedDeriv_succ]
        · simp [hi, Ne.symm hi, Function.update_of_ne hi]
  rw [h]
  funext z
  simp [groupTensor, groupLog]

theorem shiftedChildTensor_smooth {m : ℕ} (offset : Fin m → ℝ)
    (child : Fin m → Fin 3) : ContDiff ℝ ∞ (shiftedChildTensor offset child) := by
  have heq : shiftedChildTensor offset child =
      fun z => ∏ i : Fin m, childLog (child i) (offset i+z i) :=
    funext (shiftedChildTensor_eq_product offset child)
  rw [heq]
  apply contDiff_prod
  intro i hi
  exact (childLog_smooth (child i)).comp (contDiff_const.add (contDiff_apply ℝ ℝ i))

theorem shiftedChildTensor_word_bound {m : ℕ} (offset : Fin m → ℝ)
    (child : Fin m → Fin 3) (w : List (Fin m)) (z : Fin m → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n ≤ w.length, ∀ a u, |iteratedDeriv n (childLog a) u| ≤ C) :
    |occWord w (shiftedChildTensor offset child) z| ≤ C^m := by
  rw [occWord_shiftedChildTensor, Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin m, C := by
      apply Finset.prod_le_prod (fun i hi => abs_nonneg _)
      intro i hi
      exact hb (w.count i) (count_le_word_length w i) (child i) (offset i+z i)
    _ = C^m := by simp

/-- Match the actual chart base U to the original dyadic label without
changing the smooth child, support seams or positional multiplicities. -/
theorem shiftedChildTensor_physical {m : ℕ} (label : Fin m → ℕ)
    (child : Fin m → Fin 3) (U : Fin m → ℝ) (hU : ∀ i, 0 < U i)
    (z : Fin m → ℝ) :
    (shiftedChildTensor (fun i => Real.log (U i/(2 : ℝ)^(label i))) child z : ℂ) =
      ∏ i : Fin m, smoothCoord (fun t => (chi t : ℂ))
        (U i*Real.exp (z i)) (label i) (child i) := by
  rw [shiftedChildTensor_eq_product, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [childLog_ofReal]
  have hp : (0 : ℝ) < (2 : ℝ)^(label i) := by positivity
  have heq : (2 : ℝ)^(label i)*
      Real.exp (Real.log (U i/(2 : ℝ)^(label i))+z i) = U i*Real.exp (z i) := by
    rw [Real.exp_add, Real.exp_log (div_pos (hU i) hp)]
    field_simp [hp.ne']
  rw [← smoothCoord_log_exact (fun t => (chi t : ℂ)) (label i) (child i)
    (Real.log (U i/(2 : ℝ)^(label i))+z i), heq]

theorem six_shiftedChildTensor_physical (label : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (U : Fin 6 → ℝ) (hU : ∀ i, 0 < U i)
    (z : Fin 6 → ℝ) :
    (shiftedChildTensor (fun i => Real.log (U i/(2 : ℝ)^(label i))) child z : ℂ) =
      ∏ i : Fin 6, smoothCoord (fun t => (chi t : ℂ))
        (U i*Real.exp (z i)) (label i) (child i) :=
  shiftedChildTensor_physical label child U hU z

/-- Actual original W_T, coupled group hats, complete trim and compact
extension all remain present. This is NOT the independent child tensor. -/
def refinedChart {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) (offset : Fin m → ℝ)
    (child : Fin m → Fin 3) (z : Fin m → ℝ) : ℝ :=
  actualChart A T k owner U R κ₀ z * shiftedChildTensor offset child z

theorem refinedChart_smooth {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) (offset : Fin m → ℝ) (child : Fin m → Fin 3) :
    ContDiff ℝ ∞ (refinedChart A T k owner U R κ₀ offset child) :=
  (actualChart_smooth A T k owner U R κ₀).mul (shiftedChildTensor_smooth offset child)

theorem refinedChart_children_sum {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
    (offset : Fin m → ℝ) (z : Fin m → ℝ) :
    (∑ child : Fin m → Fin 3, refinedChart A T k owner U R κ₀ offset child z) =
      actualChart A T k owner U R κ₀ z * ∏ i : Fin m, psiLog (offset i+z i) := by
  simp only [refinedChart, ← Finset.mul_sum, shiftedChildTensor_children_sum]

theorem refinedChart_support {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) (offset : Fin m → ℝ) (child : Fin m → Fin 3) :
    Function.support (refinedChart A T k owner U R κ₀ offset child) ⊆
      tsupport (actualChart A T k owner U R κ₀) := by
  intro z hz
  apply subset_tsupport
  intro heq
  exact hz (by simp [refinedChart, heq])

theorem refinedChart_compact {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) (offset : Fin m → ℝ) (child : Fin m → Fin 3) :
    HasCompactSupport (refinedChart A T k owner U R κ₀ offset child) :=
  (actualChart_compact A T k owner U R κ₀).mono'
    (refinedChart_support A T k owner U R κ₀ offset child)

theorem refinedChart_tsupport_box {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) (offset : Fin m → ℝ) (child : Fin m → Fin 3) :
    tsupport (refinedChart A T k owner U R κ₀ offset child) ⊆ plateauBox m :=
  (closure_minimal (refinedChart_support A T k owner U R κ₀ offset child) isClosed_closure).trans
    (actualChart_tsupport_box A T k owner U R κ₀)

/-- The exact coupled Leibniz identity is available independently of its
norm bound. In particular no product of separate norms is labelled the
mixed derivative, and repeated-coordinate allocations remain a list. -/
theorem occWord_refinedChart_exact {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
    (offset : Fin m → ℝ) (child : Fin m → Fin 3)
    (w : List (Fin m)) (z : Fin m → ℝ) :
    occWord w (refinedChart A T k owner U R κ₀ offset child) z =
      sumTerms (fourAlloc w)
        (fourTerm (actualChart A T k owner U R κ₀)
          (shiftedChildTensor offset child) (fun _ => 1) (fun _ => 1)) z := by
  have h := occWord_four (actualChart A T k owner U R κ₀)
    (shiftedChildTensor offset child) (fun _ => 1) (fun _ => 1)
    (actualChart_smooth A T k owner U R κ₀)
    (shiftedChildTensor_smooth offset child) contDiff_const contDiff_const w z
  simpa only [mul_one, refinedChart] using h

theorem occurrence_one_bound {m : ℕ} (w : List (Fin m)) (z : Fin m → ℝ) :
    |occWord w (fun _ : Fin m → ℝ => (1 : ℝ)) z| ≤ 1 := by
  have h : occWord w (fun _ : Fin m → ℝ => (1 : ℝ)) =
      fun _ => if w = [] then 1 else 0 := by
    induction w with
    | nil => rfl
    | cons a w ih =>
        change occOne a (occWord w (fun _ : Fin m → ℝ => (1 : ℝ))) = _
        rw [ih]
        funext x
        simp [occOne]
  rw [h]
  split_ifs <;> norm_num

/-- All cross terms are included by the previously proved ordered LIST
Leibniz rule. C,B precede T, rank, slot dimension, owner, scales and child. -/
theorem exists_refinedChart_word_budget {kStar : ℕ} (A : Family kStar) :
    ∃ C : ℝ, ∃ B : ℕ, 0 ≤ C ∧
      ∀ (T : ℕ) (k : Fin (kStar+1)) (m : ℕ)
        (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ)
        (κ₀ : ℝ) (offset : Fin m → ℝ) (child : Fin m → Fin 3) (w : List (Fin m)) (z : Fin m → ℝ),
        0 < (T : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) →
        m ≤ 6*kStar → w.length ≤ 12*kStar →
        |occWord w (refinedChart A T k owner U R κ₀ offset child) z| ≤
          C * Real.log ((T : ℝ)+2)^B := by
  obtain ⟨CA, B, hCA, bA⟩ := exists_actualChart_word_budget A
  obtain ⟨MC, hMC, bC⟩ := exists_childLog_global_budget (12*kStar)
  let C : ℝ := (4 : ℝ)^(12*kStar)*CA*MC^(6*kStar)
  refine ⟨C, B, by dsimp [C]; positivity, ?_⟩
  intro T k m owner U R κ₀ offset child w z hT hU hR hm hw
  have hlog : 0 ≤ Real.log ((T : ℝ)+2) := Real.log_nonneg (by positivity)
  have bchild (v : List (Fin m)) (hv : v.length ≤ w.length) :
      |occWord v (shiftedChildTensor offset child) z| ≤ MC^(6*kStar) :=
    (shiftedChildTensor_word_bound offset child v z MC (zero_le_one.trans hMC)
      (fun n hn a u => bC n a u (hn.trans (hv.trans hw)))).trans
        (pow_le_pow_right₀ hMC hm)
  have hraw := occWord_four_bound
    (actualChart A T k owner U R κ₀) (shiftedChildTensor offset child) (fun _ => 1) (fun _ => 1)
    (actualChart_smooth A T k owner U R κ₀) (shiftedChildTensor_smooth offset child)
    contDiff_const contDiff_const w z
    (CA*Real.log ((T : ℝ)+2)^B) (MC^(6*kStar)) 1 1
    (by positivity) (by positivity) zero_le_one zero_le_one
    (fun v hv => bA T k m owner U R κ₀ v z hT hU hR hm (hv.trans hw))
    bchild (fun v hv => occurrence_one_bound v z) (fun v hv => occurrence_one_bound v z)
  have heq : (fun y => actualChart A T k owner U R κ₀ y * shiftedChildTensor offset child y * 1 * 1) =
      refinedChart A T k owner U R κ₀ offset child := by funext y; simp [refinedChart]
  rw [heq] at hraw
  simp only [mul_one] at hraw
  calc
    _ ≤ (4 : ℝ)^w.length * ((CA*Real.log ((T : ℝ)+2)^B)*MC^(6*kStar)) := hraw
    _ ≤ (4 : ℝ)^(12*kStar) * ((CA*Real.log ((T : ℝ)+2)^B)*MC^(6*kStar)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw) (by positivity)
    _ = C*Real.log ((T : ℝ)+2)^B := by dsimp [C]; ring

def refinedEuclideanChart {kStar m : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) (offset : Fin m → ℝ) (child : Fin m → Fin 3) : V m → ℂ :=
  euclideanLift m (refinedChart A T k owner U R κ₀ offset child)

/-- Genuine mixedD, normalized Fourier L1 and H-box error for the
ACTUAL coupled refined chart. All Fourier/IBP/Fubini/inversion theorems
are reused unchanged. No mode discrepancy or Fourier budget is a premise. -/
theorem exists_refined_fourier_budgets {kStar : ℕ} (A : Family kStar) :
    ∃ C : ℝ, ∃ B : ℕ, 0 ≤ C ∧
      ∀ (T : ℕ) (k : Fin (kStar+1)) (m : ℕ)
        (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ)
        (κ₀ : ℝ) (offset : Fin m → ℝ) (child : Fin m → Fin 3),
        0 < (T : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) → m ≤ 6*kStar →
        let f := refinedEuclideanChart A T k owner U R κ₀ offset child
        mixedD m f ≤ C*Real.log ((T : ℝ)+2)^B ∧
        (∀ ξ : Fin m → ℝ, ‖physicalFourier m f ξ‖ ≤
          (C*Real.log ((T : ℝ)+2)^B)*productCauchy m ξ) ∧
        (∫ ξ : Fin m → ℝ, ‖physicalFourier m f ξ‖) / frequencyScale^m ≤
          (C*Real.log ((T : ℝ)+2)^B)/2^m ∧
        ∀ H : ℝ, 0 < H → ∀ z : V m,
          ‖f z-truncatedPhysical m f H z‖ ≤
            (m : ℝ)*(C*Real.log ((T : ℝ)+2)^B)/H := by
  obtain ⟨C₀, B, hC₀, hb⟩ := exists_refinedChart_word_budget A
  refine ⟨dimensionBudget kStar*C₀, B,
    mul_nonneg (dimensionBudget_nonneg kStar) hC₀, ?_⟩
  intro T k m owner U R κ₀ offset child hT hU hR hm
  let w := refinedChart A T k owner U R κ₀ offset child
  let f := refinedEuclideanChart A T k owner U R κ₀ offset child
  have hw : ContDiff ℝ ∞ w := refinedChart_smooth A T k owner U R κ₀ offset child
  have hc : HasCompactSupport w := refinedChart_compact A T k owner U R κ₀ offset child
  have hf : ContDiff ℝ ∞ f := euclideanLift_smooth m w hw
  have hfc : HasCompactSupport f := euclideanLift_compact m w hc
  have hlog : 0 ≤ Real.log ((T : ℝ)+2) := Real.log_nonneg (by positivity)
  have hbound : 0 ≤ C₀*Real.log ((T : ℝ)+2)^B := by positivity
  have hD := mixedD_euclideanLift_le m w hw hc
    (refinedChart_tsupport_box A T k owner U R κ₀ offset child)
    (C₀*Real.log ((T : ℝ)+2)^B) hbound
    (fun v hv z => hb T k m owner U R κ₀ offset child v z hT hU hR hm (by omega))
  have hd : mixedD m f ≤ (dimensionBudget kStar*C₀)*Real.log ((T : ℝ)+2)^B := by
    apply hD.trans
    calc
      _ ≤ dimensionBudget kStar*(C₀*Real.log ((T : ℝ)+2)^B) :=
        mul_le_mul_of_nonneg_right (dimension_factor_le hm) hbound
      _ = _ := by ring
  have hp (ξ : Fin m → ℝ) : ‖physicalFourier m f ξ‖ ≤
      ((dimensionBudget kStar*C₀)*Real.log ((T : ℝ)+2)^B)*productCauchy m ξ := by
    apply (physicalFourier_pointwise m f hf hfc ξ).trans
    apply mul_le_mul_of_nonneg_right hd
    unfold productCauchy cauchy
    exact Finset.prod_nonneg (fun i hi => by positivity)
  refine ⟨hd, hp, (physicalFourier_normalized_l1_le m f hf hfc).trans
    (div_le_div_of_nonneg_right hd (by positivity)), ?_⟩
  intro H hH z
  exact (actual_uniform_truncation_error m f hf hfc H hH z).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg m)) hH.le)

/-- The refined six-coordinate Fourier input recovers the actual original
integer chart times its actual six smooth HB factors on the same source
atom. There is no new arithmetic projector or changed complete product. -/
theorem refinedEuclideanChart_six_integer_atom {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar+1)) (owner : Fin 6 → Fin k.val)
    (U : Fin 6 → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
    (label : Fin 6 → ℕ) (child : Fin 6 → Fin 3) (n : Fin 6 → ℕ)
    (hU : ∀ i, 0 < U i) (hlo : ∀ i, U i < (n i : ℝ))
    (hhi : ∀ i, (n i : ℝ) ≤ 2*U i) :
    refinedEuclideanChart A T k owner U R κ₀
      (fun i => Real.log (U i/(2 : ℝ)^(label i))) child
      (WithLp.toLp 2 (logOccurrence U n)) =
      (integerChartWeight A T k owner R κ₀ n : ℂ) *
        ∏ i : Fin 6, smoothCoord (fun t => (chi t : ℂ))
          (n i : ℝ) (label i) (child i) := by
  have hbase := actualEuclideanChart_integer_atom A T k owner U R κ₀ n hU hlo hhi
  change (actualChart A T k owner U R κ₀ (logOccurrence U n) : ℂ) = _ at hbase
  have hchild := six_shiftedChildTensor_physical label child U hU (logOccurrence U n)
  have hcoord (i : Fin 6) : U i*Real.exp (logOccurrence U n i) = (n i : ℝ) := by
    have hn : 0 < (n i : ℝ) := (hU i).trans (hlo i)
    rw [logOccurrence, Real.exp_log (div_pos hn (hU i))]
    field_simp [(hU i).ne']
  simp_rw [hcoord] at hchild
  change ((actualChart A T k owner U R κ₀ (logOccurrence U n) *
    shiftedChildTensor (fun i => Real.log (U i/(2 : ℝ)^(label i))) child
      (logOccurrence U n) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, hbase, hchild]

end
end ImbalancedChen.P3ActualHBChildMixedFourier
