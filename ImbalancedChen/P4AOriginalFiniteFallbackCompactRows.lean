import ImbalancedChen.P4AOriginalFiniteFallbackFullTree
import ImbalancedChen.P4AFallbackJointFiniteCover

namespace ImbalancedChen.P4AOriginalFiniteFallbackCompactRows
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open P4AOriginalFiniteFallbackBank (read read_some_iff)
open P4AOriginalFiniteFallbackCanonical (selected_second selected_third)
open P4AOriginalFiniteFallbackOwnCubeRows (old pairPoint secondRow thirdRow)
open P4AOriginalFiniteFallbackSmallThird (diff)
open P4AFallbackCanonicalBanks
open P4AFallbackJointFiniteCover
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4ACatalogFiveCoarseWeightedPayment (candidateTuples)
open P4ACatalogFiveCoarseResidualUniformity
open P4AOriginalThirdFallbackPrimeTests (cut cut_pos combined guard_cube guard_profile)
open VariableEnvelope

theorem profile_mono {t : Fin 3 → ℝ} (hz : 0<t 2) {a b : ℝ} (hab : a≤b) :
    primeTupleMinusProfile a t≤primeTupleMinusProfile b t := by
  rw [primeTupleMinusProfile_eq_extendedThirdFactor _ _ hz,primeTupleMinusProfile_eq_extendedThirdFactor _ _ hz]
  apply div_le_div_of_nonneg_right _ hz.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply monotone_actualExtendedThirdLowerFactor
  apply div_le_div_of_nonneg_right _ hz.le
  linarith

/-- Uniform one-sided price for the genuine signed lower-residual row.
Only the new cap needs to approximate its endpoint. The old actual
buffered level is allowed to lie below its endpoint by any amount. -/
theorem compact (h eta : ℝ) (hh : 0<h) (heta : 0<eta) :
    ∃ delta : ℝ,0<delta ∧ ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
    ∀ p∈actualPrimeBoxTuples N (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ)),
    ∀ a b x y : ℝ, a≤x → x≤thirdPrefixTheta → b≤thirdPrefixTheta → y≤thirdPrefixTheta →
      |b-y|≤delta →
    primeTupleMinusProfile y (actualPrimeTupleLog N p)-primeTupleMinusProfile x (actualPrimeTupleLog N p)-3*eta≤
      diff N p a b ∧ diff N p x y-5*eta≤diff N p a b := by
  obtain ⟨delta,hdelta,hmod⟩ := exists_actual_profile_cap_modulus h eta hh heta
  obtain ⟨N0,hN0,hun⟩ := exists_all_caps_ownCube_uniform_threshold h eta hh heta
  refine ⟨delta,hdelta,N0,hN0,?_⟩
  intro N hN hEven p hp a b x y hax hx hb hy hd
  let t := actualPrimeTupleLog N p
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hcap : (N:ℝ)^(19/96:ℝ)≤N := by simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (19/96:ℝ)≤1))
  have hs := hun N hN hEven N hcap p hp
  have hbox := mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff (by omega) _ _ p).mp hp).2
  have hby := hmod b y hb hy hd t (fun i => ⟨(hbox i).1,(hbox i).2.le⟩)
  have hmon := profile_mono (hh.trans_le (hbox 2).1) hax
  have ha' := (abs_lt.mp (hs a (hax.trans hx))).2
  have hb' := (abs_lt.mp (hs b hb)).1
  have hx' := (abs_lt.mp (hs x hx)).1
  have hy' := (abs_lt.mp (hs y hy)).2
  unfold diff
  dsimp only [t] at *
  constructor <;> linarith [(abs_le.mp hby).1]

def applied (m : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) :=
  if p∈candidateTuples d N then thirdRow m d w N p else 0

theorem supported {m : ℕ} {d : OriginalData} {w : ℝ} {N : ℕ} (hn : 1<N) {p : Fin 3 → ℕ}
    (h : applied m d w N p≠0) : p∈P4AOriginalThirdFallbackPrimeTests.primes N := by
  by_cases hp : p∈candidateTuples d N
  · cases ha : read m (bank m).third (actualPrimeTupleLog N p) with
    | none => exact (h (by simp [applied,hp,thirdRow,ha])).elim
    | some c =>
      exact P4ACatalogFiveOmittedOrderPayment.candidate_cutoff_mem_box d cut N hn p hp
        ((mem_logPrimeBox.mp (guard_cube (selected_third ha).1) 2).1)
  · exact (h (if_neg hp)).elim

theorem sum_eq (m : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (hn : 1<N) :
    P4AOriginalFiniteFallbackSignedSource.sum d N (thirdRow m d w N)=
      ∑ p∈P4AOriginalThirdFallbackPrimeTests.primes N,
        (∏ i,P4ACatalogFiveCoarseWeightedPayment.weight (p i))*applied m d w N p := by
  let C := candidateTuples d N
  let S := P4AOriginalThirdFallbackPrimeTests.primes N
  let g := fun p => (∏ i,P4ACatalogFiveCoarseWeightedPayment.weight (p i))*applied m d w N p
  change (∑ p∈C,_) = ∑ p∈S,g p
  calc
    _ = ∑ p∈C,g p := Finset.sum_congr rfl (fun p hp => by simp [g,applied,show p∈candidateTuples d N from hp])
    _ = ∑ p∈C∪S,g p := Finset.sum_subset Finset.subset_union_left (fun p _ hp => by
      have hc : p∉candidateTuples d N := hp
      simp [g,applied,hc])
    _ = ∑ p∈S,g p := (Finset.sum_subset Finset.subset_union_right (fun p _ hp => by
      have hh : applied m d w N p=0 := Classical.byContradiction (fun H => hp (supported hn H))
      simp [g,hh])).symm

end
end ImbalancedChen.P4AOriginalFiniteFallbackCompactRows
