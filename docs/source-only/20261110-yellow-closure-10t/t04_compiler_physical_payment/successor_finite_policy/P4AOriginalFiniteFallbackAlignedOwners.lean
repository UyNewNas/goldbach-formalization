import ImbalancedChen.P4AOriginalFiniteFallbackCount

namespace ImbalancedChen.P4AOriginalFiniteFallbackAlignedOwners
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackBank (Bank read read_on_cell read_some_iff)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth aligned_cut)

def subdivisions (m k : ℕ) := 76*(m+1)*(k+1)-1

theorem subdivisions_succ (m k : ℕ) : subdivisions m k+1=76*(m+1)*(k+1) :=
  Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))

theorem joint_succ (B : Bank) (m : ℕ) : jointIndex B m+1=76*(m+1)*(B.mesh+1) := by
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))

theorem aligned (B : Bank) (m k : ℕ) :
    alignedWidth (jointIndex B m) k=alignedWidth m (subdivisions B.mesh k) ∧
    alignedWidth (jointIndex B m) k=alignedWidth B.mesh (subdivisions m k) := by
  have h (a b : ℕ) : ((subdivisions a b:ℕ):ℝ)+1=76*((a:ℝ)+1)*((b:ℝ)+1) := by
    exact_mod_cast subdivisions_succ a b
  have H : ((jointIndex B m:ℕ):ℝ)+1=76*((m:ℝ)+1)*((B.mesh:ℝ)+1) := by exact_mod_cast joint_succ B m
  simp only [alignedWidth,logPrimeMeshStep,H,h]
  constructor <;> field_simp <;> ring

theorem cell_iff {r m k : ℕ} {t u : Fin r → ℝ}
    (h : ∀ i,⌊t i/alignedWidth m k⌋=⌊u i/alignedWidth m k⌋) (j : Fin r → Fin (m+1)) :
    t∈logPrimeMeshCell 0 (19/96) m j ↔ u∈logPrimeMeshCell 0 (19/96) m j := by
  have cut (i : Fin r) (v : ℕ) : t i<logPrimeMeshPoint 0 (19/96) m v ↔ u i<logPrimeMeshPoint 0 (19/96) m v := by
    rw [aligned_cut m k v,aligned_cut m k v,h i]
  rw [mem_logPrimeMeshCell,mem_logPrimeMeshCell]
  apply forall_congr'
  intro i
  change (_≤t i ∧ t i<_) ↔ (_≤u i ∧ u i<_)
  exact and_congr (by simpa only [not_lt] using not_congr (cut i (j i))) (cut i ((j i).val+1))

theorem read_eq {r m k : ℕ} (rows : (Fin r → Fin (m+1)) → Option ℚ) {t u : Fin r → ℝ}
    (h : ∀ i,⌊t i/alignedWidth m k⌋=⌊u i/alignedWidth m k⌋) : read m rows t=read m rows u := by
  cases ht : read m rows t with
  | some c =>
    obtain ⟨j,hj,hr⟩ := read_some_iff.mp ht
    exact ((read_on_cell ((cell_iff h j).mp hj)).trans hr).symm
  | none =>
    cases hu : read m rows u with
    | none => rfl
    | some c =>
      obtain ⟨j,hj,hr⟩ := read_some_iff.mp hu
      rw [read_on_cell ((cell_iff h j).mpr hj),hr] at ht
      contradiction

theorem bank_read {r : ℕ} (B : Bank) (m k : ℕ) (rows : (Fin r → Fin (B.mesh+1)) → Option ℚ)
    {t u : Fin r → ℝ} (h : ∀ i,⌊t i/alignedWidth (jointIndex B m) k⌋=⌊u i/alignedWidth (jointIndex B m) k⌋) :
    read B.mesh rows t=read B.mesh rows u := by
  apply read_eq (k:=subdivisions m k)
  simpa only [(aligned B m k).2] using h

end
end ImbalancedChen.P4AOriginalFiniteFallbackAlignedOwners
