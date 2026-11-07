import ImbalancedChen.P2TwentyOneMaskedTailFloor

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This applies the actual masked-tail decomposition to the original entire
Gamma7--21 LIST bank, without reducing it to three selected slots. The
finite original word-length decision term below is only written source;
it has NOT been run or reported accepted. Its elaboration/evaluation is
an explicit user-owned finite obligation. No analytic K/PP is inferred.
-/
namespace ImbalancedChen.P2TwentyOneAllWordTailDecomposition
noncomputable section
open Wu2008DoubleSieve
open scoped Classical BigOperators
open P2EnhancedTwentyOneQuotientFinite (quotientSwitched)
open P2TwentyOneUnsiftedArithmeticSource P2TwentyOneMaskedTailFloor

/-- Literal original bank guard; UNEVALUATED source proposal. -/
theorem original_prefix_lengths :
    (secondFunctionalMotherPrefixIndices.all fun i =>
      (secondFunctionalMotherGammaWords i).all fun cs => decide (2≤cs.length))=true := by
  decide

theorem original_prefix_length {i} (hi : i ∈ secondFunctionalMotherPrefixIndices)
    {cs : List ℕ} (hcs : cs ∈ secondFunctionalMotherGammaWords i) : 2≤cs.length := by
  have houter := List.all_eq_true.mp original_prefix_lengths i hi
  exact of_decide_eq_true (List.all_eq_true.mp houter cs hcs)

def goodSwitchedPrimeMass (N d M : ℕ) (a b c e f : ℝ) (z : ℕ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map fun cs =>
      p5z_labelledPrimeMass (absoluteGoodLabels N d M a b c e f cs z) (product d)
        (fun _ => 1) N).sum).sum

def smallPartnerSwitchedMass (N d M : ℕ) (a b c e f : ℝ) (z : ℕ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map fun cs =>
      p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
        (fun _ => 1) N z).sum).sum

/-- Original ALL-word count is dominated by the independent genuine
tail-floor families plus an explicit original small-partner remainder.
The latter is neither dropped nor assumed negligible. -/
theorem quotientSwitched_le_good_add_small {N d M z : ℕ} {a b c e f : ℝ}
    (hN : 4≤N) (he : Even N) (hd : 0<d) (hza : (z : ℝ)≤a)
    (hold : ∀ p : ℕ,p.Prime → p ∣ d → z≤p) :
    quotientSwitched N d M a b c e f ≤
      goodSwitchedPrimeMass N d M a b c e f z + smallPartnerSwitchedMass N d M a b c e f z := by
  rw [quotientSwitched_eq_switchedPrimeMass hN he hd]
  have hword (i) (hi : i ∈ secondFunctionalMotherPrefixIndices) :
      ((secondFunctionalMotherGammaWords i).map fun cs =>
        p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
          (fun _ => 1) N).sum ≤
      ((secondFunctionalMotherGammaWords i).map fun cs =>
        p5z_labelledPrimeMass (absoluteGoodLabels N d M a b c e f cs z) (product d)
          (fun _ => 1) N).sum +
      ((secondFunctionalMotherGammaWords i).map fun cs =>
        p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
          (fun _ => 1) N z).sum := by
    have hh := secondFunctionalMother_list_sum_mono (secondFunctionalMotherGammaWords i)
      (fun cs => p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
        (fun _ => 1) N)
      (fun cs => p5z_labelledPrimeMass (absoluteGoodLabels N d M a b c e f cs z) (product d)
        (fun _ => 1) N +
        p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
          (fun _ => 1) N z)
      (fun cs hcs => prefix_primeMass_le_absolute_add_small
        (original_prefix_length hi hcs) hza hold 1 (by norm_num))
    simpa only [List.sum_map_add] using hh
  have hh := secondFunctionalMother_list_sum_mono secondFunctionalMotherPrefixIndices
    (fun i => ((secondFunctionalMotherGammaWords i).map fun cs =>
      p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
        (fun _ => 1) N).sum)
    (fun i => ((secondFunctionalMotherGammaWords i).map fun cs =>
      p5z_labelledPrimeMass (absoluteGoodLabels N d M a b c e f cs z) (product d)
        (fun _ => 1) N).sum +
      ((secondFunctionalMotherGammaWords i).map fun cs =>
        p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
          (fun _ => 1) N z).sum)
    hword
  simpa only [List.sum_map_add,switchedPrimeMass,goodSwitchedPrimeMass,
    smallPartnerSwitchedMass] using hh

end
end ImbalancedChen.P2TwentyOneAllWordTailDecomposition
