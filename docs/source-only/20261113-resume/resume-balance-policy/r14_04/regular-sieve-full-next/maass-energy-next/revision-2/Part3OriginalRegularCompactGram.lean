import ImbalancedChen.Part3OriginalRegularCutoffDiagonal
import ImbalancedChen.Part3OriginalSameInfinityFullModulus
import ImbalancedChen.Part3OriginalHolomorphicInfinityGram
import ImbalancedChen.Part3OriginalRegularGaussianOffDiagonal

/-! The actual quotient-L² packet, the full progression, and the true
identity cell on a whole arbitrary integer row. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCompactGram20261113
open Real Complex Set Filter MeasureTheory Finset
open scoped Topology MatrixGroups ComplexConjugate
open OriginalRegularCutoffDiagonal20261113 (height diagonal_value)
open OriginalRegularCutoffPlane20261113 (compact cutoffPair)
open OriginalRegularCutoffModuli20261113 (series full_average)
open OriginalRegularPreKuznetsovAverage20261113 (gaussianOrbit)
open OriginalSameInfinityScalarGeometry20261113 (term rank_one_term)
open OriginalPositiveScalarGeometry20261112 (induced)
open OriginalInfinitySwitchedGeometry20261113 (offDiagonal)
open OriginalHolomorphicInfinityGram20261113 (packet packet_diagonal)
open OriginalHolomorphicInfinityProgression20261113 (sameDelta)
open OriginalAllParameterKloosterman20261113 (dyadEnergy)
open OriginalRegularGaussianOffDiagonal20261113 (entry)
open OriginalRegularGaussianForms20261113 (numerator)
open ActualInfinityCuspAnnihilator20261026b (HeightSeed QuotientL2)
open private multiple multiple_injective from ImbalancedChen.Part3OriginalHolomorphicInfinityProgression
open private packetVector probe from ImbalancedChen.Part3OriginalInfinitySwitchedGeometry
open private all_moduli from ImbalancedChen.Part3OriginalSameInfinityFullModulus
open private native_diag from ImbalancedChen.Part3OriginalSameInfinityScalarGeometry
open private packet_const from ImbalancedChen.Part3OriginalHolomorphicInfinityGram

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def mark (m : ℕ) : ℕ+ := ⟨max 1 m,by omega⟩

theorem mark_of_pos {m : ℕ} (hm : 0<m) : (mark m).val=m := max_eq_right hm

def vector (q : ℕ+) (M : ℕ) (a : ℕ→ℂ) (ψ : HeightSeed) : QuotientL2 q.val :=
  ∑ i∈range (M+1),star (a (M+i)) • packetVector q (mark (M+i)) ψ

private theorem pair (q m n : ℕ+) (j : ℕ) (r : ℝ) :
    star (inner ℂ (packetVector q m (compact r j)) (packetVector q n (compact r j)))=
      (if m=n then (height j:ℂ) else 0)+series q m n (some j) r := by
  let ψ := compact r j
  have T := (all_moduli q m n ψ ψ).star
  have E := (T.congr_fun (fun c => rank_one_term q m n c ψ ψ)).tsum_eq
  have A := native_diag m n ψ ψ
  change OriginalPositiveScalarGeometry20261112.diagonal (cutoffPair j r) 1 m.val (n.val:ℤ)=_ at A
  rw [diagonal_value] at A
  change star (inner ℂ (packetVector q m ψ) (packetVector q n ψ))=
    (if m=n then (height j:ℂ) else 0)+∑' c,term (induced (cutoffPair j r)) q m n c
  rw [E,A,←star_add,offDiagonal,add_comm,sub_add_cancel]

theorem gram (q : ℕ+) {M : ℕ} (hM : 0<M) (a : ℕ→ℂ) (j : ℕ) (r : ℝ) :
    (‖vector q M a (compact r j)‖^2:ℝ)=
      height j*dyadEnergy M a+
        (packet M a (fun m n => series q (mark m) (mark n) (some j) r)).re := by
  let ψ := compact r j
  let F := fun m n => star (inner ℂ (packetVector q (mark m) ψ) (packetVector q (mark n) ψ))
  have eq : ((‖vector q M a ψ‖^2:ℝ):ℂ)=packet M a F := by
    calc
      _ = star (inner ℂ (vector q M a ψ) (vector q M a ψ)) := by
        rw [inner_self_eq_norm_sq_to_K,star_pow,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_pow]
      _ = _ := by
        simp only [vector,sum_inner,inner_sum,inner_smul_left,inner_smul_right,star_sum,star_mul',
          star_star,starRingEnd_apply,packet,F,←Complex.star_def]
        exact sum_congr rfl (fun i _ => sum_congr rfl (fun l _ => by ring))
  have split : packet M a F=(height j:ℂ)*dyadEnergy M a+
      packet M a (fun m n => series q (mark m) (mark n) (some j) r) := by
    rw [←packet_diagonal,←packet_const]
    simp only [packet,←sum_add_distrib,←mul_add]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro l _
    have hm : 0<M+i := by omega
    have hn : 0<M+l := by omega
    have iff : mark (M+i)=mark (M+l) ↔ M+i=M+l :=
      ⟨fun h => by simpa only [mark_of_pos hm,mark_of_pos hn] using congrArg Subtype.val h,
        congrArg mark⟩
    rw [F,pair]
    by_cases e : M+i=M+l <;> simp [sameDelta,iff,e]
  have T := congrArg Complex.re (eq.trans split)
  simpa only [Complex.ofReal_re,Complex.add_re,←Complex.ofReal_mul] using T

private theorem block_eq (q : ℕ+) {M : ℕ} (hM : 0<M) (a : ℕ→ℂ) (K : ℝ) (l : ℕ) :
    entry M q.val K (fun n => star (a n)) a l=
      packet M a (fun m n => term (gaussianOrbit K) q (mark m) (mark n) (multiple q.val l)) := by
  let c := q.val*(l+1)
  have cd : q.val∣c := dvd_mul_right _ _
  simp only [entry,numerator,OriginalHolomorphicPhysicalCosine20261113.form,packet,
    Finset.sum_div]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  have hm : 0<M+i := by omega
  have hn : 0<M+j := by omega
  have ct : (multiple q.val l).val=c := rfl
  simp only [term,ct,if_pos cd,mark_of_pos hm,mark_of_pos hn,
    OriginalInfinitySwitchedGeometry20261113.argument,OriginalHolomorphicPhysicalCosine20261113.argument,
    OriginalHolomorphicPhysicalCosine20261113.scale,Real.sqrt_mul (Nat.cast_nonneg (M+i)),←Complex.star_def]
  dsimp only [c]
  rw [show 4*Real.pi*(Real.sqrt ↑(M+i)*Real.sqrt ↑(M+j))/(q.val*(l+1):ℕ)=
    4*Real.pi/(q.val*(l+1):ℕ)*Real.sqrt ↑(M+i)*Real.sqrt ↑(M+j) by ring] <;> ring

theorem full_rows {K : ℝ} (hK : 0<K) (q : ℕ+) {M : ℕ} (hM : 0<M) (a : ℕ→ℂ) :
    HasSum (entry M q.val K (fun n => star (a n)) a)
      (packet M a (fun m n => ∑' c,term (gaussianOrbit K) q (mark m) (mark n) c)) := by
  let f := fun m n c => term (gaussianOrbit K) q (mark m) (mark n) c
  have H (m n : ℕ) : HasSum (fun l => f m n (multiple q.val l)) (∑' c,f m n c) := by
    have supp : Function.support (f m n)⊆Set.range (multiple q.val) := by
      intro c hc
      by_cases d : q.val∣c.val
      · obtain ⟨v,hv⟩ := d
        cases v with
        | zero => have u := c.property;simp [hv] at u
        | succ l => exact ⟨l,Subtype.ext hv.symm⟩
      · exact (hc (by simp [f,term,d])).elim
    have eq := (multiple_injective q.val).tsum_eq supp
    have sum := (full_average hK q (mark m) (mark n)).1.of_norm.comp_injective (multiple_injective q.val)
    rw [←eq]
    exact sum.hasSum
  have packed := hasSum_sum (s:=range (M+1)) fun i _ => hasSum_sum (s:=range (M+1)) fun j _ =>
    (H (M+i) (M+j)).mul_left (conj (a (M+i))*a (M+j))
  exact packed.congr_fun (fun l => block_eq q hM a K l)

end ImbalancedChen.Part3.OriginalRegularCompactGram20261113
end

