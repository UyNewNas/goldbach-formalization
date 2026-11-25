import ImbalancedChen.P2FiniteMarkedGamma5GeometricFamily
import ImbalancedChen.P2FiniteMarkedGamma5ActualPhysicalPlateau

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The original U4 source selects a constructed instance of the unchanged
geometric Family, and its literal integer tuple has weight one in that
Family at every scale above the existing fixed threshold. The old
ActualRank and ActualPhysicalPlateau proofs are reused, not reconstructed.

The arithmetic-history import closure of those old candidates is still
unqualified. This adapter and its old source suppliers receive no kernel
or endpoint credit. The original Family owner must use the extraction
postimage associated with P2Gamma5AdmissibleFamilyCore.

Each Family has one fixed old/tail split and the whole-scale endpoint
function T |-> log(rootQ T n U4 t p). The explicit Euler estimate chooses
one constant before n, p, t, both ranks, T and the test point. Consequently
no uniform constant is inferred by interchanging a separate Family-wise
existential with those parameters. This is geometric uniformity only;
no moving-family PP distribution assertion is made.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5ActualFamily

noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalH430SeedHistoryMass
open P2FiniteMarkedGamma5LogExtension (sourcePair canonicalTail)
open P2FiniteMarkedGamma5PhysicalExtension
open P2FiniteMarkedGamma5EulerWordBudget
open P2FiniteMarkedGamma5AllRankEulerBudget
open P2FiniteMarkedGamma5ActualRank
open P2FiniteMarkedGamma5ActualPhysicalPlateau
open P2FiniteMarkedGamma5GeometricFamily
open P5Z.AdmissibleAllRankIntegerGeometricFamily (Family eulerWord)
open scoped Classical BigOperators

/-- The literal natural-number tuple in the existing Fin coordinate
order. Repeated values remain separate slots; an empty rough tail stays
empty. No primality or other arithmetic test is inserted. -/
def sourceIntegerPoint (old qs : List ℕ) (m : ℕ) :
    Fin (old.length + (2 + m.primeFactorsList.length)) → ℕ :=
  fun i =>
    match (slotEquiv old.length m.primeFactorsList.length).symm i with
    | .inl j => old[j.val]
    | .inr (.inl j) => sourcePair qs j
    | .inr (.inr j) => canonicalTail m j

/-- Integer evaluation and the old physical source use exactly the same
coordinates. This is only a cast dictionary, not a new plateau proof. -/
theorem sourceIntegerPoint_cast (old qs : List ℕ) (m : ℕ) :
    (fun i => (sourceIntegerPoint old qs m i : ℝ)) =
      physicalToFin (sourcePhysicalPoint old qs m) := by
  funext i
  unfold sourceIntegerPoint physicalToFin
  generalize (slotEquiv old.length m.primeFactorsList.length).symm i = s
  rcases s with j | j
  · rfl
  · rcases j with j | j <;> rfl

/-- The geometric Family is constructed before its scale is evaluated.
The bound is only the numerical condition for a fixed split. The actual
source consumer below derives it from the existing history theorem. -/
def originalSplitFamily (k r n p : ℕ) (t width : ℝ)
    (hw : 0 < width) (hw1 : width ≤ 1)
    (hkr : k + 2 + r ≤ frozenSourceRankBound) : Family frozenSourceRankBound :=
  geometricFamily frozenSourceRankBound k r frozenLeafCutoffFloor width
    (fun T => log (rootQ T n .U4 t p)) frozenLeafCutoffFloor_pos hw hw1 hkr

/-- One natural Euler constant works for all original endpoint functions
and all admissible splits. In particular p may be selected after T for
this geometric estimate; no PP estimate is inferred from that fact. -/
theorem originalSplitFamily_mixedEuler_uniform {width : ℝ}
    (hw : 0 < width) (hw1 : width ≤ 1) (order : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n p k r : ℕ) (t : ℝ)
      (hkr : k + 2 + r ≤ frozenSourceRankBound) (T : ℕ)
      (d : Fin (frozenSourceRankBound + 1))
      (w : List (Fin d.val)) (v : Fin d.val → ℝ), w.length ≤ order →
      |eulerWord w
        ((originalSplitFamily k r n p t width hw hw1 hkr).ambient T d) v| ≤
          (C : ℝ) := by
  obtain ⟨C, hC, H⟩ := ambient_mixedEuler_budget frozenSourceRankBound width hw order
  refine ⟨C, hC, ?_⟩
  intro n p k r t hkr T d w v hword
  exact H frozenLeafCutoffFloor frozenLeafCutoffFloor_pos
    (fun T => log (rootQ T n .U4 t p)) k r hkr T d.val w v hword

/-- The actual U4 source supplies its own rank bound, chooses the
corresponding constructed Family and has integer weight one in it.
There is no Family, source-floor, rank or plateau premise at this call.
The same p, old list, ordered fresh pair and complete canonical tail are
retained. The original marks and any additive-prime test remain outside
this geometric factor. -/
theorem enhanced_position_family_source_one {N n p dep m : ℕ} {t width : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ originalBand N .U4)
    (hw : 0 < width) (hw1 : width ≤ 1)
    (hlarge : scaleThreshold frozenLeafCutoffFloor ≤ (N : ℝ))
    (l : LevelIndex N n .U4 t p dep) {qs : List ℕ}
    (hq : qs ∈ badLabels N (rootQ N n .U4 t p) (wordProduct l))
    (hm : m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ))
      (cutoff (rootQ N n .U4 t p) (wordProduct l) (227 / 50))) :
    let k := (levelOccurrence l).current.old.length
    let r := m.primeFactorsList.length
    let hkr : k + 2 + r ≤ frozenSourceRankBound :=
      enhanced_position_source_rank hN ht ht' hn hp l hq hm
    (originalSplitFamily k r n p t width hw hw1 hkr).ambient N
      ⟨k + (2 + r), by omega⟩
      (fun i => (sourceIntegerPoint (levelOccurrence l).current.old qs m i : ℝ)) = 1 := by
  dsimp only
  have hkr := enhanced_position_source_rank hN ht ht' hn hp l hq hm
  have heq := geometricFamily_at_rank frozenSourceRankBound
    (levelOccurrence l).current.old.length m.primeFactorsList.length
    frozenLeafCutoffFloor width (fun T => log (rootQ T n .U4 t p))
    frozenLeafCutoffFloor_pos hw hw1 hkr N hlarge
  calc
    _ = finPhysicalProfile (log (rootQ N n .U4 t p)) (N : ℝ) width
        ((N : ℝ) ^ frozenLeafCutoffFloor)
        (fun i => (sourceIntegerPoint (levelOccurrence l).current.old qs m i : ℝ)) :=
      congrFun heq _
    _ = 1 := by
      rw [sourceIntegerPoint_cast]
      exact enhanced_position_finPhysical_source_one hN ht ht' hn hp hw l hq hm

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualFamily
