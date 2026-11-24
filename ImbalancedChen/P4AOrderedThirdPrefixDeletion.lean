import ImbalancedChen.P4AFull87NativeThirdProgram
import ImbalancedChen.P4AFull87FiniteWallRate

namespace ImbalancedChen.P4AOrderedThirdPrefixDeletion
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P4AUpperTaggedParityCompiler
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AFull87ActualAffineDeletion P4AFull87MarkedPrimePayment P4AFull87OrdinaryAdmissionDeletion

variable {m : ℕ}

abbrev Family (p : Program (m+1)) (caps : Finset ℝ) :=
  ((caps : Type) × Bool) ⊕ ((p.Signature × Bool) ⊕ (p.Label × p.Label))

def bank (p : Program (m+1)) (caps : Finset ℝ) (N J : ℕ) : Family p caps → ℕ → ℕ → ℝ
  | .inl (a,k) => centres (Affine.const (k := 0) a.val) k N J
  | .inr (.inl (s,k)) => centres (p.table s) k N J
  | .inr (.inr ab) => familyCentre N (fun _ : Fin J => m)
      (fun _ => ab.1.val.sub ab.2.val)

private theorem signature_flip (p : Program (m+1)) (x y : Fin (m+1) → ℝ)
    (h : p.signature x ≠ p.signature y) :
    ∃ ab : p.Label × p.Label, ¬((ab.1.val.sub ab.2.val).eval x < 0 ↔
      (ab.1.val.sub ab.2.val).eval y < 0) := by
  by_contra! hall
  simp only [Affine.eval_sub, sub_lt_zero] at hall
  apply h
  funext ab
  apply Prod.ext
  · exact congrArg (fun q : Prop => decide q) (propext (hall ab))
  · have hle : ab.1.val.eval x ≤ ab.2.val.eval x ↔ ab.1.val.eval y ≤ ab.2.val.eval y := by
      simpa only [not_lt] using (not_congr (hall (ab.2,ab.1)))
    exact congrArg (fun q : Prop => decide q) (propext hle)

abbrev Seen (p : Program (m+1)) (caps : Finset ℝ) (N cap J : ℕ) (w v t : ℝ) (d : ℕ) :=
  ∃ i : Family p caps, d ∈ covered N cap J w v ((J:ℝ)*t) (bank p caps N J i)

theorem constant_seen (p : Program (m+1)) (caps : Finset ℝ) (N cap J : ℕ) (hN : 1 < N)
    (omega v tau : ℝ) (hw : 0 < omega) (hv : omega ≤ v) (ht : 0 < tau)
    (tags : ℕ → List Bool) {d f r : ℕ}
    (hd : d ∈ universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (hf : f ∈ cell tags N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau d)
    (hr : r ≤ d.primeFactorsList.length) (hJ : r ≤ J) {a : ℝ} (ha : a ∈ caps)
    (hflip : ¬(ordinaryRosserPrefixAdmissible false ((N:ℝ)^a) (rosserAncestor r d.primeFactorsList) ↔
      ordinaryRosserPrefixAdmissible false ((N:ℝ)^a) (rosserAncestor r f.primeFactorsList))) :
    Seen p caps N cap J omega v tau d := by
  have hr0 : 0 < r := by
    by_contra! h
    have hz : r=0 := by omega
    exact hflip (by simp [hz,rosserAncestor])
  obtain ⟨k,hk⟩ := in_cell_flip_covered N cap J hN omega v tau hw hv ht tags hd hf hr0
    (Nat.zero_le r) hr hJ (Affine.const (k := 0) a) (by simpa using hflip)
  exact ⟨.inl (⟨a,ha⟩,k),hk⟩

theorem native_seen (p : Program (m+1)) (caps : Finset ℝ) (N cap J : ℕ) (hN : 1 < N)
    (omega v tau : ℝ) (hw : 0 < omega) (hv : omega ≤ v) (ht : 0 < tau)
    (tags : ℕ → List Bool) {d f r : ℕ}
    (hd : d ∈ universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (hf : f ∈ cell tags N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau d)
    (hm : m+1 ≤ r) (hr : r ≤ d.primeFactorsList.length) (hJ : r ≤ J)
    (hflip : ¬(ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^(p.eval (coords N (m+1) d.primeFactorsList.reverse))) (rosserAncestor r d.primeFactorsList) ↔
      ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^(p.eval (coords N (m+1) f.primeFactorsList.reverse))) (rosserAncestor r f.primeFactorsList))) :
    Seen p caps N cap J omega v tau d := by
  let X := coords N (m+1) d.primeFactorsList.reverse
  let Y := coords N (m+1) f.primeFactorsList.reverse
  by_cases hp : p.signature X = p.signature Y
  · let s := p.signature X
    have hx : (p.table s).eval X = p.eval X := p.table_exact X
    have hy : (p.table s).eval Y = p.eval Y := p.table_on_region s Y hp.symm
    obtain ⟨k,hk⟩ := in_cell_flip_covered N cap J hN omega v tau hw hv ht tags hd hf
      (by omega) hm hr hJ (p.table s) (by
        change ¬(ordinaryRosserPrefixAdmissible false ((N:ℝ)^((p.table s).eval X)) _ ↔
          ordinaryRosserPrefixAdmissible false ((N:ℝ)^((p.table s).eval Y)) _)
        rw [hx,hy]
        exact hflip)
    exact ⟨.inr (.inl (s,k)),hk⟩
  · obtain ⟨ab,hab⟩ := signature_flip p X Y hp
    refine ⟨.inr (.inr ab),?_⟩
    have hrd := hm.trans hr
    have hrf : m+1 ≤ f.primeFactorsList.length := by rw [cell_rank_preserved _ _ _ _ _ _ hf]; exact hrd
    apply flip_mem_covered N cap J hN omega v tau hw hv ht (fun _ : Fin J => m)
      (fun _ => ab.1.val.sub ab.2.val) ⟨0,by omega⟩ (hm.trans hJ) hd hrd Y _ hab
    intro i
    dsimp only [Y]
    rw [canonical_coords N (m+1) d hrd,canonical_coords N (m+1) f hrf]
    exact (same_primeLabel_coordinate_distance_lt N ht
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hf hrd i)).le

end
end ImbalancedChen.P4AOrderedThirdPrefixDeletion
