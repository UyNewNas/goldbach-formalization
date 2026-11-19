import ImbalancedChen.P4AOriginalEarlyTupleComparison

namespace ImbalancedChen.P4AOriginalEarlySumComparison
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalEarlyFiniteStages (A4 A5 F4 F5 W signed_lower_early)
open P4AOriginalEarlyHistoricalSums (B4 B5 O4 O5 unrounded_sums)
open P4AOriginalEarlyTupleLevels (occurs4 occurs5)
open P4AOriginalEarlyTupleCarriers (Alignment box bank hist4 hist5)
open P4AOriginalEarlyTupleComparison
open P4AOriginalFull87RawChronology (cutoff rawRoot)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P4AOriginalFiniteFallbackPolicy (dispatch)
open P4AOriginalOrderedSixthStages (orderedFifth)
open P5OriginalCommonPositivePresieve (normalize)

/-- Transfer two signed sums on their actual, possibly different, carriers.
Only the common occupied part needs a lower comparison. Its reciprocal
weight is charged to the fixed target-deleted box. -/
theorem charge_on_box {α : Type*} [DecidableEq α] (A B C : Finset α) (E : α→Prop)
    (w f g : α→ℝ) {u : ℝ} (hu : 0≤u)
    (hoff : ∀p,¬E p → f p=0 ∧ g p=0)
    (hon : ∀p∈A∪B,E p → p∈A ∧ p∈B ∧ p∈C ∧ g p≤f p+u)
    (hw : ∀p∈C,0≤w p) :
    (∑p∈B,w p*g p)≤(∑p∈A,w p*f p)+u*(∑p∈C,w p) := by
  let J := A.filter E
  have hJ : J=B.filter E := by
    ext p
    simp only [J,Finset.mem_filter]
    constructor
    · rintro ⟨hp,H⟩; exact ⟨(hon p (Finset.mem_union_left _ hp) H).2.1,H⟩
    · rintro ⟨hp,H⟩; exact ⟨(hon p (Finset.mem_union_right _ hp) H).1,H⟩
  have hsub : J⊆C := by
    intro p hp
    obtain ⟨ha,H⟩ := Finset.mem_filter.mp hp
    exact (hon p (Finset.mem_union_left _ ha) H).2.2.1
  have jf : (∑p∈J,w p*f p)=∑p∈A,w p*f p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hne
    have H : ¬E p := fun h => hne (Finset.mem_filter.mpr ⟨hp,h⟩)
    rw [(hoff p H).1,mul_zero]
  have jg : (∑p∈J,w p*g p)=∑p∈B,w p*g p := by
    rw [hJ]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hne
    have H : ¬E p := fun h => hne (Finset.mem_filter.mpr ⟨hp,h⟩)
    rw [(hoff p H).2,mul_zero]
  have weight : (∑p∈J,w p)≤∑p∈C,w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _=>hw p hp)
  calc
    _ = ∑p∈J,w p*g p := jg.symm
    _ ≤ ∑p∈J,w p*(f p+u) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨ha,H⟩ := Finset.mem_filter.mp hp
      exact mul_le_mul_of_nonneg_left ((hon p (Finset.mem_union_left _ ha) H).2.2.2) (hw p (hsub hp))
    _ = (∑p∈A,w p*f p)+(∑p∈J,w p)*u := by
      simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,jf]
    _ ≤ _ := by rw [mul_comm u]; exact add_le_add_left (mul_le_mul_of_nonneg_right weight hu) _

abbrev M (k N : ℕ) := actualPrimeBoxMass N (fun _ : Fin k=>1/400) (fun _=>19/96)

theorem fixed_mass (k : ℕ) : ∃ C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,M k N≤C := by
  let L := ∏ _i : Fin k,Real.log ((19/96:ℝ)/(1/400))
  have h : Tendsto (M k) atTop (𝓝 L) := tendsto_actualPrimeBoxMass _ _ (fun _=>by norm_num) (fun _=>by norm_num)
  have hc : L<|L|+1 := by linarith [le_abs_self L]
  refine ⟨|L|+1,by positivity,?_⟩
  filter_upwards [h.eventually (gt_mem_nhds hc)] with N hN
  exact hN.le

/-- Error for the actual finite coefficient on a fixed target. The
chosen upper bank is common to both trees on every high word. -/
theorem same_target {e : ℚ} {k n N : ℕ} {a w u : ℝ} (S : Alignment e k a w)
    (he' : (e:ℝ)≤1/384) (hu : 0≤u) (hN : 1<N) (H4 : PlusShift n N u) (H5 : MinusShift n N u) :
    let d := bank e k a
    P4AOriginalEarlyHistoricalFloors.gain e (256*k) a N≤
      normalize N (rawRoot (fresh d w N) N-rawRoot (dispatch N (fresh d w N) (orderedFifth n d w N)) N)+
      u*M 4 N+2*u*M 5 N := by
  let d := bank e k a
  have h4 := charge_on_box (A4 d w N N (cutoff N)) (B4 d N N (cutoff N)) (box 4 N)
    (fun p=>occurs4 d N (hist4 p)) W (F4 n d w N N) (O4 d N N) hu
    (off_four n d w N S.nonneg he') (on_four S he' hN H4)
    (fun _ hp=>actualPrimeBoxWeight_nonneg hp)
  have h5 := charge_on_box (A5 d w N N (cutoff N)) (B5 d N N (cutoff N)) (box 5 N)
    (fun p=>occurs5 d N (hist5 p)) W (F5 n d w N N) (O5 d N N) (show 0≤2*u by linarith)
    (off_five n d w N) (on_five S he' hN H5) (fun _ hp=>actualPrimeBoxWeight_nonneg hp)
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN.le
  dsimp only
  rw [unrounded_sums e (256*k) a N hn,signed_lower_early n d w N hn]
  dsimp only [M,actualPrimeBoxMass,box] at h4 h5 ⊢
  linarith only [h4,h5]

end
end ImbalancedChen.P4AOriginalEarlySumComparison

