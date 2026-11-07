import ImbalancedChen.P2OriginalClosedCellProfileAtoms
import ImbalancedChen.P2OriginalCompactThetaMass
import ImbalancedChen.P2OriginalPositiveSameQMassLift

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Old arrays are parameters. This file proves their arithmetic profile
passage; their old analytic count licences are a separate obligation.
-/
namespace ImbalancedChen.P2OriginalOldProfilePrimeLimits

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalAffineProfilePassage
open P2OriginalClosedCellProfileAtoms P2OriginalCompactThetaMass
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def oldProfilePrimeSum {d : ℕ} (N : ℕ) (L : ℝ) (D : Set (Coord d))
    (f rho : Coord d → ℝ) (lower : Bool) (nums : Fin 200 → ℤ) : ℝ :=
  scaledPrimeSum N L D (fun x => f x * tableFunction lower nums (rho x))

def oldProfileIntegral {d : ℕ} (D : Set (Coord d)) (f rho : Coord d → ℝ)
    (lower : Bool) (nums : Fin 200 → ℤ) : ℝ :=
  ∑ b : FloorAtom, floorAtomValue nums b *
    ∫ x in D ∩ tablePullback lower rho b,f x * ∏ i,1/x i

theorem indicator_profile_atoms {X : Type*} (D : Set X) (f rho : X → ℝ)
    (lower : Bool) (nums : Fin 200 → ℤ) (x : X) :
    D.indicator (fun y => f y * tableFunction lower nums (rho y)) x =
      ∑ b : FloorAtom, floorAtomValue nums b * (D ∩ tablePullback lower rho b).indicator f x := by
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx]
    have ht := weightedTable_eq_atom_sum lower nums rho f x
    change f x * tableFunction lower nums (rho x) = _ at ht
    rw [ht]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : x ∈ tablePullback lower rho b <;> simp [hx,hb]
  · have hn (b : FloorAtom) : x ∉ D ∩ tablePullback lower rho b := fun h => hx h.1
    simp only [indicator_of_notMem hx]
    simp only [indicator_of_notMem (hn _),mul_zero,Finset.sum_const_zero]

theorem oldProfilePrimeSum_atoms {d : ℕ} (N : ℕ) (L : ℝ) (D : Set (Coord d))
    (f rho : Coord d → ℝ) (lower : Bool) (nums : Fin 200 → ℤ) :
    oldProfilePrimeSum N L D f rho lower nums =
      ∑ b : FloorAtom, floorAtomValue nums b *
        scaledPrimeSum N L (D ∩ tablePullback lower rho b) f := by
  unfold oldProfilePrimeSum scaledPrimeSum actualPrimeBoxTestSum
  simp_rw [indicator_profile_atoms,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem oldProfileIntegral_eq {d : ℕ} {D : Set (Coord d)} (hD : MeasurableSet D)
    (f rho : Coord d → ℝ) (hrho : Measurable rho)
    (hfi : IntegrableOn (fun x => f x * ∏ i,1/x i) D)
    (lower : Bool) (nums : Fin 200 → ℤ) :
    oldProfileIntegral D f rho lower nums =
      ∫ x in D,(f x * tableFunction lower nums (rho x)) * ∏ i,1/x i := by
  rw [oldProfileIntegral,← weightedTable_integral_atom_sum lower nums hrho hD hfi]
  apply setIntegral_congr_fun hD
  intro x _
  unfold weightedTable
  ring

def atomMagnitude (nums : Fin 200 → ℤ) : ℝ := ∑ b : FloorAtom, |floorAtomValue nums b|
theorem atomMagnitude_nonneg (nums : Fin 200 → ℤ) : 0 ≤ atomMagnitude nums :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- One target threshold for every atom, followed by one finite signed
combination. The bound does not divide by the mass of any cell. -/
theorem compact_uniform_old_profile {d r : ℕ} {Lmin Lmax C epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (hC : 0 ≤ C) (he : 0 < epsilon)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ) (hA : ∀ i, A i ≠ 0)
    {D : Set (Coord d)} (hD : AffineSandwich A c D)
    (hbox : ∀ x ∈ D, ∀ i, (1/5:ℝ) ≤ x i ∧ x i ≤ 1/2)
    (F G : Coord d →L[ℝ] ℝ) (B g : ℝ) (rho : Coord d → ℝ)
    (hFG : ∀ t : ℝ, F+t • G ≠ 0)
    (hrho : ∀ x ∈ D, rho x = (B-F x)/(g+G x))
    (hden : ∀ x ∈ D, 0 < g+G x)
    (f : Coord d → ℝ) (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C)
    (lower : Bool) (nums : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      |oldProfilePrimeSum N L D f rho lower nums-oldProfileIntegral D f rho lower nums| < epsilon := by
  let delta := epsilon/(1+atomMagnitude nums)
  have hd : 0 < delta := div_pos he (by linarith [atomMagnitude_nonneg nums])
  have hfixed (b : FloorAtom) : ∀ᶠ N : ℕ in atTop, ∀ L ∈ Icc Lmin Lmax,
      |scaledPrimeSum N L (D ∩ tablePullback lower rho b) f-
        (∫ x in D ∩ tablePullback lower rho b,f x * ∏ i,1/x i)| < delta := by
    obtain ⟨T,hT⟩ := compact_uniform_profile_atom hmin hmax hC hd A c hA hD hbox
      F G B g rho hFG hrho hden f hf hbound lower b
    exact (eventually_ge_atTop T).mono (fun N hN => hT N hN)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_all.mpr hfixed)
  refine ⟨T,?_⟩
  intro N hN L hL
  rw [oldProfilePrimeSum_atoms,oldProfileIntegral,← Finset.sum_sub_distrib]
  have hb : |∑ b : FloorAtom, floorAtomValue nums b *
      scaledPrimeSum N L (D ∩ tablePullback lower rho b) f-
        floorAtomValue nums b * (∫ x in D ∩ tablePullback lower rho b,f x * ∏ i,1/x i)| ≤
      delta * atomMagnitude nums := by
    calc
      _ ≤ ∑ b : FloorAtom, |floorAtomValue nums b *
          scaledPrimeSum N L (D ∩ tablePullback lower rho b) f-
            floorAtomValue nums b * (∫ x in D ∩ tablePullback lower rho b,f x * ∏ i,1/x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b : FloorAtom, |floorAtomValue nums b| * delta := by
        apply Finset.sum_le_sum
        intro b _
        rw [← mul_sub,abs_mul]
        exact mul_le_mul_of_nonneg_left (le_of_lt (hT N hN b L hL)) (abs_nonneg _)
      _ = _ := by rw [atomMagnitude,Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  have heq : delta * (1+atomMagnitude nums) = epsilon := by
    exact div_mul_cancel₀ _ (by linarith [atomMagnitude_nonneg nums])
  exact hb.trans_lt (by nlinarith)

theorem singleHalf_sandwich (lo hi : ℝ) :
    AffineSandwich singleForms (singleBounds lo hi) (singleHalf lo hi) := by
  constructor
  · rw [← single_as_affine]
    exact fun x hx => ⟨hx.1.le,hx.2⟩
  · intro x hx i
    fin_cases i <;> simp only [singleForms,singleBounds,closedGates,
      Matrix.cons_val_zero,Matrix.cons_val_one,ContinuousLinearMap.neg_apply,
      coord,ContinuousLinearMap.proj_apply] <;> linarith [hx.1,hx.2]

theorem pairHalf_sandwich (p : W2Parameters) (k : Fin 4) :
    AffineSandwich (pairForms k) (pairBounds p k) (pairHalf p k) := by
  constructor
  · rw [← pair_as_affine]
    intro x hx
    exact (pairHalf_partition p k x).mpr (Or.inl hx)
  · intro x hx i
    fin_cases k <;> fin_cases i <;>
      simp only [pairForms,pairBounds,closedGates,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        ContinuousLinearMap.neg_apply,ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
        coord,ContinuousLinearMap.proj_apply] <;>
      first | linarith [hx.1,hx.2.1,hx.2.2.1,hx.2.2.2]
        | linarith [hx.1,hx.2.1,hx.2.2]

def singleRho (s0 : ℝ) (x : Coord 1) : ℝ := singletonProfile s0 (x 0)

theorem single_profile_form {s0 : ℝ} (hs : 0 < s0) :
    (∀ t : ℝ,(s0 • coord (0 : Fin 1))+t • (0 : Coord 1 →L[ℝ] ℝ) ≠ 0) ∧
    (∀ x : Coord 1,singleRho s0 x = (s0-(s0 • coord (0 : Fin 1)) x)/(1+(0 : Coord 1 →L[ℝ] ℝ) x)) := by
  constructor
  · intro t h
    have hh := congrArg (fun F : Coord 1 →L[ℝ] ℝ => F (fun _ => 1)) h
    norm_num [coord] at hh
    exact hs.ne' hh
  · intro x
    simp [singleRho,singletonProfile,coord,smul_eq_mul,mul_sub]

def pairNumeratorForm (p : W2Parameters) (k : Fin 4) : Coord 2 →L[ℝ] ℝ :=
  if k.val < 2 then p.s0 • (coord 0+coord 1) else coord 0+coord 1
def pairDenominatorForm (k : Fin 4) : Coord 2 →L[ℝ] ℝ :=
  if k.val < 2 then 0 else coord 0
def pairNumeratorConstant (p : W2Parameters) (k : Fin 4) : ℝ :=
  if k.val < 2 then p.s0 else 1
def pairDenominatorConstant (k : Fin 4) : ℝ := if k.val < 2 then 1 else 0

theorem pair_profile_form {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4) :
    (∀ t : ℝ,pairNumeratorForm p k+t • pairDenominatorForm k ≠ 0) ∧
    (∀ x ∈ pairHalf p k,pairProfile p k x =
      (pairNumeratorConstant p k-pairNumeratorForm p k x)/
        (pairDenominatorConstant k+pairDenominatorForm k x)) ∧
    (∀ x ∈ pairHalf p k,0 < pairDenominatorConstant k+pairDenominatorForm k x) := by
  have hs := W2_anchor_positive hp
  refine ⟨?_,?_,?_⟩
  · intro t h
    have hh := congrArg (fun F : Coord 2 →L[ℝ] ℝ => F ![0,1]) h
    unfold pairNumeratorForm pairDenominatorForm at hh
    split_ifs at hh
    · norm_num [coord] at hh
      exact hs.ne' hh
    · norm_num [coord] at hh
  · intro x hx
    unfold pairProfile pairNumeratorConstant pairNumeratorForm
      pairDenominatorConstant pairDenominatorForm
    split_ifs
    · simp [fixedPairProfile,coord,smul_eq_mul]; ring
    · rfl
  · intro x hx
    have hu := (pairHalf_geometry hp k hx).1.1 0
    unfold pairDenominatorConstant pairDenominatorForm
    split_ifs <;> simp [coord] <;> linarith

theorem compact_uniform_single_old_profile {Lmin Lmax lo hi s0 epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (hlo : (1/5:ℝ) ≤ lo) (hhi : hi ≤ 1/2) (hs : 0 < s0)
    (lower : Bool) (nums : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      |oldProfilePrimeSum N L (singleHalf lo hi) residualSingle (singleRho s0) lower nums-
        oldProfileIntegral (singleHalf lo hi) residualSingle (singleRho s0) lower nums| < epsilon := by
  have hp := single_profile_form hs
  apply compact_uniform_old_profile hmin hmax (by norm_num : (0:ℝ) ≤ 10) he
    singleForms (singleBounds lo hi) singleForms_ne (singleHalf_sandwich lo hi)
    (fun x hx i => by fin_cases i; exact ⟨hlo.trans hx.1,hx.2.le.trans hhi⟩)
    (s0 • coord 0) 0 s0 1 (singleRho s0) hp.1 (fun x _ => hp.2 x)
    (by intro x _; norm_num) residualSingle residualSingle_continuous
    (fun x => by rw [abs_of_nonneg (residualSingle_bounds x).1]; exact (residualSingle_bounds x).2)
    lower nums

theorem compact_uniform_pair_old_profile {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4) (nums : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      |oldProfilePrimeSum N L (pairHalf p k) residualPair (pairProfile p k) false nums-
        oldProfileIntegral (pairHalf p k) residualPair (pairProfile p k) false nums| < epsilon := by
  obtain ⟨hform,hrho,hden⟩ := pair_profile_form hp k
  apply compact_uniform_old_profile hmin hmax (by norm_num : (0:ℝ) ≤ 10) he
    (pairForms k) (pairBounds p k) (pairForms_ne k) (pairHalf_sandwich p k)
    (fun x hx i => ⟨(pairHalf_geometry hp k hx).1.1 i,(pairHalf_geometry hp k hx).1.2 i⟩)
    (pairNumeratorForm p k) (pairDenominatorForm k) (pairNumeratorConstant p k)
    (pairDenominatorConstant k) (pairProfile p k) hform hrho hden
    residualPair residualPair_continuous
    (fun x => by rw [abs_of_nonneg (residualPair_bounds x).1]; exact (residualPair_bounds x).2)
    false nums

end
end ImbalancedChen.P2OriginalOldProfilePrimeLimits
