import ImbalancedChen.P4AOriginalOrderedThirdFullPolicy
import ImbalancedChen.P1ActualHistoricalThirdCellPartition

namespace ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient
noncomputable section
open Set VariableEnvelope HistoricalThirdCoarse P4AOriginalOrderedThirdTable
open HistoricalThirdCoarse.P1ActualTuple (history history_log)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87CompiledCounting (moduli compiled_modulus_dvd)
open scoped Classical BigOperators

/-- Every admissible ordered rough triple has one actual coarse owner.
The prime upper bound and first stop belong to the original integer
word. Even a triple with three identical coarse labels is covered. -/
theorem actual_triple {e omega : ℝ} (he : 0≤e) {m N : ℕ} (hN : 1<N)
    (p : Fin 3 → ℕ) (hp : p∈actualPrimeBoxTuples N (fun _ => (0:ℝ)) (fun _ => (19/96:ℝ)))
    (hs : StrictAnti p) (hw : (N:ℝ)^omega≤p 2) (hfirst : firstStop e m (N:ℝ) [p 0]) :
    ∃! j : Cell m, actualPrimeTupleLog N p∈logPrimeMeshCell 0 (19/96) m j ∧
      j∈retained e m ∧ rawExponent e m omega N (history p)=capValue e m j ∧
      capValue e m j≤VariableEnvelope.cap-2*e := by
  let t := actualPrimeTupleLog N p
  have hbox := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
  have hanti := (actualPrimeTupleLog_strictAnti_iff hN p (fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos)).mpr hs
  have ho : t∈actualExtendedThirdClosedOrder :=
    ⟨(mem_logPrimeBox.mp hbox 2).1,(hanti (by decide : (1:Fin 3)<2)).le,
      (hanti (by decide : (0:Fin 3)<1)).le⟩
  obtain ⟨j,hj⟩ := exists_logPrimeMeshCell 0 (19/96) m hbox
  obtain ⟨i,hi,hi',histop⟩ := (HistoricalThirdCoarse.P1ActualPartition.firstStop_iff_log e m N p).mp hfirst
  have hj0 := mem_logPrimeMeshCell.mp hj (0:Fin 3)
  have heq : i=j 0 := by
    apply Fin.ext
    rcases lt_trichotomy i.val (j 0).val with h|h|h
    · exact False.elim ((not_lt_of_ge ((logPrimeMeshPoint_mono (by norm_num : (0:ℝ)≤19/96) m
        (Nat.succ_le_of_lt h)).trans hj0.1)) hi')
    · exact h
    · exact False.elim ((not_lt_of_ge ((logPrimeMeshPoint_mono (by norm_num : (0:ℝ)≤19/96) m
        (Nat.succ_le_of_lt h)).trans hi)) hj0.2)
  have hstop : logPrimeMeshHi 0 (19/96) m j 0≤extendedFirstStop-4*e := heq ▸ histop
  have hphys := owned_portion hj ho
  have hp' : primeHistoryLogCoordinates (N:ℝ) 3 (history p)∈logPrimeMeshCell 0 (19/96) m j := by
    rw [history_log]; exact hj
  have ho' : primeHistoryLogCoordinates (N:ℝ) 3 (history p)∈actualExtendedThirdClosedOrder := by
    rw [history_log]; exact ho
  have hraw := raw_on_physical_triple (m:=m) (j:=j) hw hp' ho' hstop
  exact ⟨j,⟨hj,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨_,hphys⟩,hstop⟩,hraw,cap_on_ordered he hphys⟩,
    fun k hk => logPrimeMeshCell_unique (by norm_num) hk.1 hj⟩

abbrev keep (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :=
  P4AOriginalOrderedThirdFullPolicy.policy (width r) n (data e q a) omega N false

/-- Literal manuscript fine boxes: all words with the same ordered
one-prime interval labels share the atom. Its Q is exactly the
existing complete small-times-rough Q. -/
def coefficient (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (tau L : ℝ) :=
  P4AUpperTaggedBetaAttachment.rho (keep r n e q a omega N) (fun _ => []) N N
    ((N:ℝ)^omega) (cutoff N) tau L

def alignedWidth (m k : ℕ) := logPrimeMeshStep 0 (19/96) m/((k:ℝ)+1)

theorem aligned_small (m : ℕ) {eps : ℝ} (he : 0<eps) :
    ∃ k : ℕ, 0<alignedWidth m k ∧ alignedWidth m k≤eps := by
  obtain ⟨k,hk⟩ := exists_nat_gt (logPrimeMeshStep 0 (19/96) m/eps)
  have hh := (div_lt_iff₀ he).mp hk
  exact ⟨k,div_pos (logPrimeMeshStep_pos (by norm_num) m) (by positivity),
    (div_le_iff₀ (by positivity : 0<(k:ℝ)+1)).mpr (by nlinarith)⟩

/-- The floor convention includes the lower boundary of each full coarse
interval. A sufficiently fine such grid can be selected before N. -/
theorem aligned_cut (m k i : ℕ) (t : ℝ) :
    t < logPrimeMeshPoint 0 (19/96) m i ↔
      ⌊t/alignedWidth m k⌋ < ((i*(k+1):ℕ):ℤ) := by
  have hk : 0<(k:ℝ)+1 := by positivity
  have hs : 0<alignedWidth m k := div_pos (logPrimeMeshStep_pos (by norm_num) m) hk
  rw [Int.floor_lt,div_lt_iff₀ hs]
  push_cast
  dsimp only [logPrimeMeshPoint,alignedWidth]
  rw [zero_add]
  congr 1
  field_simp <;> ring

theorem cell_value_constant (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau : ℝ) {x y : ℕ}
    (hx : x∈P4AUpperTaggedParityCompiler.universe N N ((N:ℝ)^omega) (cutoff N))
    (hy : y∈P4AUpperTaggedParityCompiler.universe N N ((N:ℝ)^omega) (cutoff N))
    (h : P2LowerFiniteCellRounding.label N tau x=P2LowerFiniteCellRounding.label N tau y) :
    P4AFull87TaggedAtomValue.occupied (keep r n e q a omega N) (fun _ => [])
      N N ((N:ℝ)^omega) (cutoff N) tau x =
    P4AFull87TaggedAtomValue.occupied (keep r n e q a omega N) (fun _ => [])
      N N ((N:ℝ)^omega) (cutoff N) tau y :=
  P4AFull87TaggedAtomValue.fibre_scalar _ _ _ _ _ _ _ hx hy (congrArg (fun l => ([],l)) h)

theorem upper_majorant (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (tau L : ℝ)
    (hL : 1<L) (hwL : (N:ℝ)^omega≤L) (hwz : (N:ℝ)^omega≤cutoff N)
    (hz : cutoff N≤(N:ℝ)) (x : ℕ) :
    (if x.Coprime (sieveProduct N (Nat.ceil (cutoff N))) then (1:ℝ) else 0) ≤
      physicalDivisorSum (moduli N ((N:ℝ)^omega)) (coefficient r n e q a omega N tau L) x := by
  have h := P4AUpperTaggedBetaAttachment.rho_majorant (keep r n e q a omega N) (fun _ => [])
    N N ((N:ℝ)^omega) (cutoff N) tau L hL hwL hwz hz (x:ℤ)
  rw [actualSmallRoughIndicator_eq_sieveProduct_natAbs] at h
  simpa only [Int.natAbs_natCast] using h

theorem count (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (tau L : ℝ)
    (hL : 1<L) (hwL : (N:ℝ)^omega≤L) (hwz : (N:ℝ)^omega≤cutoff N) (hz : cutoff N≤(N:ℝ))
    {b T : ℝ} (hb : 0<b) (hb1 : b<1) (hT : 0<T) (hgate : (Nat.ceil (cutoff N):ℝ)≤T^(b/(1+b))) :
    let Q := moduli N ((N:ℝ)^omega)
    let rho := coefficient r n e q a omega N tau L
    (RealB b N:ℝ) ≤ ((realHalfProductSource b N T).card:ℝ)*physicalDensitySum Q rho+
      realPhysicalDistributionError b N T Q rho+(Nat.ceil (cutoff N):ℝ)+(T+1) :=
  RealB_cast_le_same_rho_main_add_distribution_of_gate N _ _ _ hb hb1 hT hgate
    (fun _ hm _ => compiled_modulus_dvd N _ hwz hm)
    (upper_majorant r n e q a omega N tau L hL hwL hwz hz)

end
end ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient
