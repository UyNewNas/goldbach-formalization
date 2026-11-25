import ImbalancedChen.P2FiniteMarkedGamma5SeedCellReadout
import ImbalancedChen.P2FiniteMarkedGamma5CoarseAtlasMass
import ImbalancedChen.P5zMarkedPrimeFamilyCorrections

namespace ImbalancedChen.P2FiniteMarkedGamma5SeedCorrectionCarrier
noncomputable section
open Finset Real Filter
open P2FiniteMarkedGamma5NativeSeedSum (Index)
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor frozenLeafCutoffFloor_pos)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430PhysicalRoots (Root)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry oldRank tailRank rank Tuple weight)
open P2FiniteMarkedGamma5SeedCellReadout (planAt acceptAt)
open P2FiniteMarkedGamma5AllRankEulerBudget (scaleThreshold)
open P2FiniteMarkedGamma5AtlasFamily (atlasFamily_at_rank atlasFamily_nonneg)
open P2FiniteMarkedGamma5RadialProfileCollar (radialWidth radialWidth_pos radialWidth_le_one)
open P2FiniteMarkedGamma5AtlasEulerBudget (atlasProfile)
open P2FiniteMarkedGamma5RadialRoughMass (cut cutExponent)
open P2FiniteMarkedGamma5CoarseAtlasMass (weight_le_one_on_support)
open scoped Classical BigOperators

abbrev actualWeight {n : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (mesh : Index 430 → ℕ) {h : ℝ} (hp : 0<h) (h8 : h≤1/8) (N : ℕ) :=
  weight v (planAt mesh v) (radialWidth h) frozenLeafCutoffFloor_pos (radialWidth_pos hp)
    (radialWidth_le_one hp h8) (acceptAt root tau mesh v) N

abbrev smallTuple (N k : ℕ) := Fin k → Fin (N+1)
def enlarge {N k : ℕ} (x : smallTuple N k) : Fin k → Fin (2*N+1) :=
  fun j => ⟨(x j).val,by have := (x j).isLt; omega⟩

@[simp] theorem enlarge_product {N k : ℕ} (x : smallTuple N k) :
    Part3.labelledProduct (enlarge x) = Part3.labelledProduct x := rfl

/-- Keep exactly the relevant coordinate-sized tuples after the eventual
threshold. The explicit tests also make the old receiver's hypotheses
true at all small N, where no identification is needed. -/
def kept {k : ℕ} (N : ℕ) (W : (Fin k → Fin (2*N+1)) → ℝ) : Finset (smallTuple N k) :=
  (Part3.labelledPrimeTuples k N).filter fun x =>
    W (enlarge x) ≠ 0 ∧ W (enlarge x) ≤ 1 ∧ ∀ j, cut N ≤ ((x j).val:ℝ)

theorem actual_at_rank {N n : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (mesh : Index 430 → ℕ) {h : ℝ} (hp : 0<h) (h8 : h≤1/8) (u : Tuple N v)
    (hlarge : scaleThreshold frozenLeafCutoffFloor ≤ (N:ℝ)) :
    actualWeight v root tau mesh hp h8 N u =
      atlasProfile (planAt mesh v) (acceptAt root tau mesh v N) (log (cellQ N n v.val.2.1))
        (N:ℝ) (radialWidth h) ((N:ℝ)^frozenLeafCutoffFloor) (fun j => ((u j).val:ℝ)) := by
  exact congrFun (atlasFamily_at_rank (planAt mesh v) _ (oldRank v) (tailRank v)
    frozenLeafCutoffFloor (radialWidth h) (fun T => log (cellQ T n v.val.2.1))
    (acceptAt root tau mesh v) frozenLeafCutoffFloor_pos (radialWidth_pos hp)
    (radialWidth_le_one hp h8) v.property N hlarge) _

theorem actual_nonneg {N n : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (mesh : Index 430 → ℕ) {h : ℝ} (hp : 0<h) (h8 : h≤1/8) (u : Tuple N v) :
    0 ≤ actualWeight v root tau mesh hp h8 N u := by
  unfold actualWeight weight
  apply atlasFamily_nonneg

/-- Exact arithmetic reindexing for any test of the complete integer
product. Product equality is used for values, not for injectivity. -/
theorem compress {N n : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (mesh : Index 430 → ℕ) {h : ℝ} (hp : 0<h) (h8 : h≤1/8) (hN : 2≤N)
    (hlarge : scaleThreshold frozenLeafCutoffFloor ≤ (N:ℝ))
    (hcut : cut N≤(N:ℝ)^frozenLeafCutoffFloor/2) (F : ℕ→ℝ) :
    let W := actualWeight v root tau mesh hp h8 N
    (∑ x ∈ kept N W, W (enlarge x) * F (Part3.labelledProduct x)) =
      ∑ u ∈ Part3.labelledPrimeTuples (rank v) (2*N), W u * F (Part3.labelledProduct u) := by
  let W := actualWeight v root tau mesh hp h8 N
  let S := Part3.labelledPrimeTuples (rank v) (2*N)
  let U := S.filter (fun u => W u ≠ 0)
  change _ = ∑ u ∈ S, W u * F (Part3.labelledProduct u)
  calc
    _ = ∑ u ∈ U,W u * F (Part3.labelledProduct u) := by
      apply sum_bij (fun x _ => enlarge x)
      · intro x hx
        obtain ⟨hx,hz,_,_⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,hz⟩
      · intro x _ y _ he
        funext j
        exact Fin.ext (congrArg Fin.val (congrFun he j))
      · intro u hu
        obtain ⟨hprime,hne⟩ := mem_filter.mp hu
        have hp' := (mem_filter.mp hprime).2
        have ha := actual_at_rank v root tau mesh hp h8 u hlarge
        obtain ⟨hband,h1⟩ := weight_le_one_on_support hN hp h8 hcut (planAt mesh v)
          (acceptAt root tau mesh v N) u hprime (log (cellQ N n v.val.2.1))
          (by rw [←ha]; exact hne)
        obtain ⟨_,hf,_,hcap⟩ := mem_filter.mp hband
        have hprod : (∏ j, (u j).val) ≤ 2*N := by exact_mod_cast hcap
        obtain ⟨x,hx⟩ := P2FiniteMarkedGamma5PrimeCube.bounded_prime_tuple_in_target_carrier u hp' hprod
        have he : enlarge x = u := funext (fun j => Fin.ext (hx j))
        refine ⟨x,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,fun j => ?_⟩,?_,?_,?_⟩,he⟩
        · simpa only [hx] using hp' j
        · simpa only [he] using hne
        · simpa only [he,ha] using h1
        · intro j
          simpa only [hx] using hf j
      · intro _ _
        rfl
    _ = _ := by
      apply sum_subset (filter_subset _ _)
      intro u hu hn
      have hz : W u = 0 := by
        by_contra h
        exact hn (mem_filter.mpr ⟨hu,h⟩)
      simp [hz]

theorem compress_mass {N n : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (mesh : Index 430 → ℕ) {h : ℝ} (hp : 0<h) (h8 : h≤1/8) (hN : 2≤N)
    (hlarge : scaleThreshold frozenLeafCutoffFloor ≤ (N:ℝ))
    (hcut : cut N≤(N:ℝ)^frozenLeafCutoffFloor/2) :
    let W := actualWeight v root tau mesh hp h8 N
    p5z_labelledMass (kept N W) (fun x => W (enlarge x)) =
      p5z_labelledMass (Part3.labelledPrimeTuples (rank v) (2*N)) W := by
  simpa only [p5z_labelledMass,mul_one] using
    compress v root tau mesh hp h8 hN hlarge hcut (fun _ => 1)

/-- Compression leaves even the noncoprime correction at the original
target N and exact Q,rho. No product cutoff is applied here. -/
theorem compress_correction {N n : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (mesh : Index 430 → ℕ) {h : ℝ} (hp : 0<h) (h8 : h≤1/8) (hN : 2≤N)
    (hlarge : scaleThreshold frozenLeafCutoffFloor ≤ (N:ℝ))
    (hcut : cut N≤(N:ℝ)^frozenLeafCutoffFloor/2) (D : Finset ℕ) (rho : ℕ→ℝ) :
    let W := actualWeight v root tau mesh hp h8 N
    p5z_labelledCoprimeCorrection (kept N W) Part3.labelledProduct (fun x => W (enlarge x)) D rho =
      p5z_labelledCoprimeCorrection (Part3.labelledPrimeTuples (rank v) (2*N)) Part3.labelledProduct W D rho := by
  let W := actualWeight v root tau mesh hp h8 N
  dsimp only
  unfold p5z_labelledCoprimeCorrection
  apply sum_congr rfl
  intro d _
  have H := compress v root tau mesh hp h8 hN hlarge hcut
    (fun m => if Nat.Coprime m d then (1:ℝ) else 0)
  simp only [mul_ite,mul_one,mul_zero] at H
  rw [compress_mass v root tau mesh hp h8 hN hlarge hcut]
  unfold p5z_labelledCoprimeMass
  rw [H]

/-- Only this small-prime summand may be truncated: its own genuine
prime test includes M<N, so every omitted value is exactly zero. -/
theorem compress_small {N n : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (mesh : Index 430 → ℕ) {h : ℝ} (hp : 0<h) (h8 : h≤1/8) (hN : 2≤N)
    (hlarge : scaleThreshold frozenLeafCutoffFloor ≤ (N:ℝ))
    (hcut : cut N≤(N:ℝ)^frozenLeafCutoffFloor/2) (z : ℕ) :
    let W := actualWeight v root tau mesh hp h8 N
    p5z_labelledSmallPrimeMass ((kept N W).filter (fun x => Part3.labelledProduct x ≤ N))
      Part3.labelledProduct (fun x => W (enlarge x)) N z =
    p5z_labelledSmallPrimeMass (Part3.labelledPrimeTuples (rank v) (2*N)) Part3.labelledProduct W N z := by
  let W := actualWeight v root tau mesh hp h8 N
  have H := compress v root tau mesh hp h8 hN hlarge hcut
    (fun m => if m<N ∧ (N-m).Prime ∧ N-m<z then (1:ℝ) else 0)
  simp only [mul_ite,mul_one,mul_zero] at H
  dsimp only
  unfold p5z_labelledSmallPrimeMass
  refine Eq.trans ?_ H
  apply sum_subset (filter_subset _ _)
  intro x hx hno
  have hm : ¬ Part3.labelledProduct x ≤ N := fun hh => hno (mem_filter.mpr ⟨hx,hh⟩)
  exact if_neg (fun H => hm H.1.le)

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedCorrectionCarrier
