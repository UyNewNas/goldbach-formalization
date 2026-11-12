import ImbalancedChen.Part5OriginalH430ActualMemberStrictCover
import ImbalancedChen.Part5OriginalH430SelectedFreshWindows

/-! The cumulative mesh retains the grid point 57/112 at every precision
at least 111. This proves both enhanced square tests at the real frozen
level, before density or any choice of N. -/
namespace ImbalancedChen.Part5OriginalH430EnhancedPhysicalGrid
noncomputable section
open Set
open P2PhysicalIncomingPrefixCells
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry
open Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430RootSourceDictionary Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SeedHistoryMass Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430SelectedFreshWindows

theorem grid111_lower {ν : ℝ} (hν : ν ∈ Icc (0:ℝ) 1) (hb : 57/112 ≤ ν) :
    57/112 ≤ rawLower 111 ν := by
  have hm := exponentCode_membership (m:=111) hν
  cases hc : exponentCode 0 1 111 ν with
  | none => norm_num [rawLower,hc,lowerEndpoint]
  | some j =>
    have hh : ν ∈ Ico (logPrimeMeshPoint 0 1 111 j.val)
        (logPrimeMeshPoint 0 1 111 (j.val+1)) := by simpa [hc,exponentCell] using hm
    have hhi := hh.2
    norm_num [logPrimeMeshPoint,logPrimeMeshStep,Nat.cast_add] at hhi
    have hj : 57 ≤ j.val := by
      by_contra! h
      have hle : j.val ≤ 56 := by omega
      have hr : (j.val:ℝ) ≤ 56 := by exact_mod_cast hle
      linarith
    have hr : (57:ℝ) ≤ j.val := by exact_mod_cast hj
    norm_num [rawLower,hc,lowerEndpoint,logPrimeMeshPoint,logPrimeMeshStep] <;> linarith

theorem grid_persists {ν : ℝ} {n : ℕ} (hn : 111 ≤ n)
    (hν : ν ∈ Icc (0:ℝ) 1) (hb : 57/112 ≤ ν) : 57/112 ≤ frozenLevel n ν := by
  have hl : rawLower 111 ν ≤ frozenLevel 111 ν :=
    le_max_right (frozenLevel 110 ν) (rawLower 111 ν)
  have hmono : Monotone (fun m => frozenLevel m ν) :=
    monotone_nat_of_le_succ (fun m => frozenLevel_step m ν)
  exact ((grid111_lower hν hb).trans hl).trans (hmono hn)

theorem precision_error {n : ℕ} (hn : 111 ≤ n) : 1/((n:ℝ)+1) ≤ 11/384 := by
  have h : (111:ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
  linarith

theorem enhanced_frozen_root_square {n : ℕ} {k : Root} {τ x : ℝ}
    (hn : 111 ≤ n) (hτ : 0≤τ) (hτ' : τ≤1/12)
    (he : rootSource k x = .enhanced) (hx : x ∈ rootBand k) :
    2*x < (frozenRoot n k τ x).physical.total := by
  have he' := enhanced_root_coordinate he hx
  have hlow : a ≤ x := (rootBand_subset k hx).1
  have hb : (57/112:ℝ) ≤ VariableEnvelope.v x := by
    rw [VariableEnvelope.v_eq_min]
    apply le_min <;> dsimp [VariableEnvelope.A,VariableEnvelope.C] <;>
      dsimp [a] at hlow <;> dsimp [tailCutoff] at he' <;> linarith
  have htotal := enhanced_root_total (tau:=τ) he
  have hgrid := grid_persists hn (root_total_bounds hτ hτ' hx) (by rw [htotal]; exact hb)
  change 2*x < frozenLevel n (sourceRoot k τ x).physical.total
  dsimp [tailCutoff] at he'
  linarith

theorem enhanced_root_gates {n : ℕ} {k : Root} {τ x : ℝ}
    (hn : 111 ≤ n) (hτ : 0≤τ) (hτ' : τ≤1/12)
    (he : rootSource k x = .enhanced) (hx : x ∈ rootBand k) :
    fullGates (frozenRoot n k τ x).physical ∧ selectedGates (frozenRoot n k τ x).physical := by
  have hg := (enhanced_frozen_root_square hn hτ hτ' he hx).le
  simpa [fullGates,selectedGates,frozenRoot,sourceRoot,word,selectedWord,remainingWord,SquareGates] using hg

theorem enhanced_history_physical_gates {N n p : ℕ} {k : Root} {τ : ℝ} {o : Occurrence N}
    (hn : 111 ≤ n) (hN : 2≤N) (hτ : 0≤τ) (hτ' : τ≤1/12) (hp : p∈originalBand N k)
    (he : rootSource k (physicalPrime N p) = .enhanced) (ho : o∈rootHistory N n k τ p) :
    fullGates o.current.node.physical ∧ selectedGates o.current.node.physical := by
  have hx := original_band_geometry hN hp
  have hg := enhanced_root_gates hn hτ hτ' he hx
  exact rootHistory_gates (by omega) hτ hτ' (precision_error hn) (original_band_prime hp) hx ho hg.1 hg.2

theorem enhanced_bank_children_gates {N n p : ℕ} {k : Root} {τ : ℝ} {g : Fin 430}
    (hn : 111 ≤ n) (hN : 2≤N) (hτ : 0≤τ) (hτ' : τ≤1/12) (hp : p∈originalBand N k)
    (he : rootSource k (physicalPrime N p) = .enhanced) (l : Index N n k τ p g) :
    let Q := rootQ N n k τ p
    let r := (levelOccurrence l).current.node.physical
    (∀ a : Lane, l∈selectedLevel N n k τ p g (owner a) →
      ∀ q∈singleChildren (rule a) N Q (oldWord l) (ceilingAt l),
        let v := perform r (singleShape (rule a)) (singleCoordinates N q.val)
        fullGates v ∧ selectedGates v) ∧
    (∀ j : Fin 36, l∈selectedLevel N n k τ p g (.inr j) →
      ∀ s : Fin 4, ∀ v∈pairChildren j s N Q (oldWord l) (ceilingAt l),
        let w := perform r (.w2Pair j s) (pairCoordinates N v.1.val v.2.val)
        fullGates w ∧ selectedGates w) := by
  have hg := enhanced_root_gates hn hτ hτ' he (original_band_geometry hN hp)
  exact selected_child_gates hN hτ hτ' (precision_error hn) hp l hg.1 hg.2

end
end ImbalancedChen.Part5OriginalH430EnhancedPhysicalGrid
