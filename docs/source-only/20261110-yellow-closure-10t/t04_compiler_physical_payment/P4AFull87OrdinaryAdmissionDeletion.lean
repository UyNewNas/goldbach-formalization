import ImbalancedChen.P4AFull87ActualAffineDeletion
import ImbalancedChen.P5PresievedRoughSlotAffineGates

/-! Every original total-product or odd-cardinality cube flip against a
common native affine cap is paid by deleting one actual prime. The centre
has just one variable shape index, the endpoint of that product or cube.
The length of the word first rejected is not a second summation index. -/
namespace ImbalancedChen.P4AFull87OrdinaryAdmissionDeletion
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P4AUpperTaggedParityCompiler
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AFull87ActualAffineDeletion P4AFull87MarkedPrimePayment
open P5Z.PresievedRoughSlotAffineGates (cube prefix region original_upper_prefix_iff_log)

def dim (m j : ℕ) := max (m-1) j

private theorem baseLe (m j : ℕ) : m ≤ dim m j+1 := by
  unfold dim
  omega

private theorem endLt (m j : ℕ) : j < dim m j+1 := by
  unfold dim
  omega

/-- False selects the total through j; true selects the old cube at j. -/
def test (kind : Bool) (j : ℕ) {m : ℕ} (a : Affine m) : Affine (dim m j+1) :=
  let slot (i : Fin (j+1)) : Fin (dim m j+1) := i.castLE (endLt m j)
  let first := Affine.sum Finset.univ (fun i : Fin j => Affine.coord (slot i.castSucc))
  let last := (Affine.coord (slot (Fin.last j))).scale (if kind then 3 else 1)
  (first.add last).sub (a.pull (fun i => i.castLE (baseLe m j)))

def centres {m : ℕ} (a : Affine m) (kind : Bool) (N J : ℕ) :=
  familyCentre N (fun s : Fin J => dim m s.val) (fun s => test kind s.val a)

private def logAt (N : ℕ) (xs : List ℕ) (j : ℕ) :=
  Real.log (xs.getD j 0 : ℝ) / Real.log (N : ℝ)

private theorem test_eval (N : ℕ) (xs : List ℕ) (j : ℕ) {m : ℕ}
    (a : Affine m) (kind : Bool) :
    (test kind j a).eval (coords N _ xs) =
      (∑ i : Fin j, logAt N xs i.val) + (if kind then 3 else 1)*logAt N xs j -
        a.eval (coords N m xs) := by
  simp [test,coords,logAt]

private theorem prefix_sum (N r : ℕ) (xs : List ℕ) (j : Fin r) :
    prefix (coords N r xs) j = ∑ i : Fin j.val, logAt N xs i.val := by
  unfold prefix
  refine Finset.sum_bij' (fun i hi => (⟨i.val,(Finset.mem_filter.mp hi).2⟩ : Fin j.val))
    (fun i _ => (⟨i.val,i.isLt.trans j.isLt⟩ : Fin r))
    (fun _ _ => Finset.mem_univ _)
    (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.isLt⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

private theorem total_eval (N j : ℕ) (xs : List ℕ) {m : ℕ} (a : Affine m) :
    (test false j a).eval (coords N _ xs) =
      (∑ i : Fin (j+1), coords N (j+1) xs i) - a.eval (coords N m xs) := by
  rw [test_eval,Fin.sum_univ_castSucc]
  simp [coords,logAt]

private theorem cube_eval (N r : ℕ) (xs : List ℕ) {m : ℕ} (a : Affine m) (j : Fin r) :
    (test true j.val a).eval (coords N _ xs) =
      cube (coords N r xs) j - a.eval (coords N m xs) := by
  rw [test_eval,cube,prefix_sum]
  rfl

theorem reversed_prefix (x r : ℕ) (hr : r ≤ x.primeFactorsList.length) :
    (List.ofFn (canonicalPrefix r x)).reverse = rosserAncestor r x.primeFactorsList := by
  apply List.reverse_injective
  rw [List.reverse_reverse,canonicalPrefix_ofFn hr,rosserAncestor,List.reverse_drop]
  congr 1
  omega

theorem in_cell_flip_covered (N cap J : ℕ) (hN : 1 < N)
    (omega v tau : ℝ) (hw : 0 < omega) (hv : omega ≤ v) (ht : 0 < tau)
    (tags : ℕ → List Bool) {d f m r : ℕ}
    (hd : d ∈ universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (hf : f ∈ cell tags N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau d)
    (hr0 : 0 < r) (hm : m ≤ r) (hr : r ≤ d.primeFactorsList.length)
    (hJ : r ≤ J) (a : Affine m)
    (hflip : ¬(ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^(a.eval (coords N m d.primeFactorsList.reverse))) (rosserAncestor r d.primeFactorsList) ↔
      ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^(a.eval (coords N m f.primeFactorsList.reverse))) (rosserAncestor r f.primeFactorsList))) :
    ∃ kind : Bool, d ∈ covered N cap J omega v ((J:ℝ)*tau) (centres a kind N J) := by
  let x := d.primeFactorsList.reverse
  let y := f.primeFactorsList.reverse
  let X := coords N r x
  let Y := coords N r y
  let A := a.eval (coords N m x)
  let B := a.eval (coords N m y)
  have hrf : r ≤ f.primeFactorsList.length := by rw [cell_rank_preserved _ _ _ _ _ _ hf]; exact hr
  have hfU := (Finset.mem_filter.mp hf).1
  have hreg : ¬(X ∈ region r A ↔ Y ∈ region r B) := by
    dsimp only [X,Y,x,y,A,B]
    rw [canonical_coords N r d hr,canonical_coords N r f hrf]
    rw [← original_upper_prefix_iff_log hN _ _ (canonicalPrefix_pos hd hr)
      (canonicalPrefix_strictAnti hd hr),← original_upper_prefix_iff_log hN _ _
      (canonicalPrefix_pos hfU hrf) (canonicalPrefix_strictAnti hfU hrf),
      reversed_prefix d r hr,reversed_prefix f r hrf]
    exact hflip
  have mark (j : ℕ) (hj : j < r) (kind : Bool)
      (hg : ¬((test kind j a).eval (coords N _ x) < 0 ↔
              (test kind j a).eval (coords N _ y) < 0)) :
      d ∈ covered N cap J omega v ((J:ℝ)*tau) (centres a kind N J) := by
    have hdim : dim m j+1 ≤ r := by unfold dim; omega
    have hrd := hdim.trans hr
    have hfr := hdim.trans hrf
    apply flip_mem_covered N cap J hN omega v tau hw hv ht
      (fun s : Fin J => dim m s.val) (fun s => test kind s.val a)
      ⟨j,hj.trans_le hJ⟩ (hdim.trans hJ) hd hrd (coords N _ y) _ hg
    intro i
    dsimp only [y]
    rw [canonical_coords _ _ _ hrd,canonical_coords _ _ _ hfr]
    exact (same_primeLabel_coordinate_distance_lt N ht
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hf hrd i)).le
  by_cases hsum : (∑ i, X i) < A ↔ (∑ i, Y i) < B
  · have hchange : ∃ i : Fin r, Even i.val ∧ ¬(cube X i < A ↔ cube Y i < B) := by
      by_contra! h
      apply hreg
      constructor
      · intro hX
        exact ⟨hsum.mp hX.1,fun i he => (h i he).mp (hX.2 i he)⟩
      · intro hY
        exact ⟨hsum.mpr hY.1,fun i he => (h i he).mpr (hY.2 i he)⟩
    obtain ⟨i,_,hi⟩ := hchange
    exact ⟨true,mark i.val i.isLt true (by simpa only [cube_eval N r x a i,
      cube_eval N r y a i,sub_lt_zero] using hi)⟩
  · cases r with
    | zero => omega
    | succ j =>
      exact ⟨false,mark j (Nat.lt_succ_self j) false (by
        simpa only [total_eval,sub_lt_zero] using hsum)⟩

end
end ImbalancedChen.P4AFull87OrdinaryAdmissionDeletion
