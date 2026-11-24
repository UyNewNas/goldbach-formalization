import ImbalancedChen.P4AFull87MarkedPrimePayment
import ImbalancedChen.P4AFull87SamePieceCapVariation

/-! A flipped affine test on the actual canonical word. Erase the fixed
coordinate of largest slope. The interval halfwidth is rank*tau even
when the slope is tiny. Its centre uses only the remaining whole divisor
and the preassigned test, including if the marked prime was in the first
six. -/
namespace ImbalancedChen.P4AFull87ActualAffineDeletion
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AFull87MarkedPrimePayment P1FiniteAffineDecisionProgram
open P2CanonicalWallFullResidualPayment P4AUpperTaggedFrozenAdmissionCatalogue

def coords (N k : ℕ) (xs : List ℕ) : Fin k → ℝ :=
  fun i => Real.log (xs.getD i.val 0 : ℝ)/Real.log (N : ℝ)

theorem canonical_coords (N k x : ℕ) (hk : k ≤ x.primeFactorsList.length) :
    coords N k x.primeFactorsList.reverse = actualPrimeTupleLog N (canonicalPrefix k x) := by
  funext i
  simp only [coords,actualPrimeTupleLog,canonicalPrefix,primeHistoryTuple,List.reverse_reverse]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_reverse] using i.isLt.trans_le hk),
    List.getD_eq_getElem _ _ (by simp [List.length_take,Nat.min_eq_left hk])]
  simp only [List.getElem_take]

private def magnitude {k : ℕ} (a : Affine (k+1)) :=
  (Finset.univ : Finset (Fin (k+1))).image fun i => |a.coefficient i|

private theorem mag_nonempty {k : ℕ} (a : Affine (k+1)) : (magnitude a).Nonempty :=
  Finset.image_nonempty.mpr Finset.univ_nonempty

def pivot {k : ℕ} (a : Affine (k+1)) : Fin (k+1) :=
  Classical.choose (Finset.mem_image.mp (Finset.max'_mem (magnitude a) (mag_nonempty a)))

private theorem mag_max {k : ℕ} (a : Affine (k+1)) (i : Fin (k+1)) :
    |a.coefficient i| ≤ |a.coefficient (pivot a)| := by
  have he := (Classical.choose_spec
    (Finset.mem_image.mp (Finset.max'_mem (magnitude a) (mag_nonempty a)))).2
  change |a.coefficient (pivot a)| = _ at he
  rw [he]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

def restored (j p n : ℕ) :=
  n.primeFactorsList.reverse.take j ++ p :: n.primeFactorsList.reverse.drop j

def centre {k : ℕ} (N : ℕ) (a : Affine (k+1)) (n : ℕ) :=
  -(a.eval (coords N (k+1) (restored (pivot a).val 1 n))) / a.coefficient (pivot a)

private theorem get_pivot (u v : List ℕ) (p q i : ℕ) :
    (u ++ p :: v).getD i 0 = if i = u.length then p else (u ++ q :: v).getD i 0 := by
  induction u generalizing i with
  | nil => cases i <;> simp
  | cons x xs ih => cases i <;>
      simp [List.cons_append,List.getD_cons_zero,List.getD_cons_succ,ih]

private theorem actual_erasure {N cap x : ℕ} {w z : ℝ} (hx : x ∈ universe N cap w z)
    {i : ℕ} (hi : i < x.primeFactorsList.reverse.length) :
    ∃ n ∈ universe N cap w z, ∃ p ∈ roughPrimeFinset N cap w z, n.Coprime p ∧
      n*p = x ∧ restored i p n = x.primeFactorsList.reverse ∧
      (n.primeFactorsList.reverse.take i).length = i := by
  let xs := x.primeFactorsList.reverse
  let u := xs.take i
  let p := xs[i]'hi
  let v := xs.drop (i+1)
  let n := (u++v).prod
  have hu : u.length = i := by simp [u,List.length_take,Nat.min_eq_left hi.le]
  have he : xs = u ++ p :: v := by
    calc
      xs = xs.take (i+1) ++ xs.drop (i+1) := (List.take_append_drop _ _).symm
      _ = _ := by rw [List.take_succ_eq_append_getElem hi]; simp [u,v,p,List.append_assoc]
  obtain ⟨hsub,hprod⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap w z hx
  change xs <+ _ at hsub
  change xs.prod = x at hprod
  rw [he] at hsub hprod
  have hdel : u++v <+ roughPrimeUniverse N cap w z :=
    ((List.Sublist.refl u).append ((List.Sublist.refl v).cons p)).trans hsub
  have hcanon : u++v = n.primeFactorsList.reverse :=
    P2LowerCanonicalRetainedTrace.actual_chosen_eq_canonical N cap w z (u++v) hdel rfl
  have hmul : n*p = x := by
    rw [← hprod]
    simp [n,mul_assoc,mul_left_comm,mul_comm]
  have hnf : n ∈ universe N cap w z :=
    Nat.mem_divisors.mpr ⟨(show n ∣ x from ⟨p,hmul.symm⟩).trans (Nat.mem_divisors.mp hx).1,
      (Nat.mem_divisors.mp hx).2⟩
  have hcop := P2LowerFiniteCellRounding.universe_squarefree N cap w z hx
  rw [← hmul,Nat.squarefree_mul_iff] at hcop
  have hp : p ∈ roughPrimeUniverse N cap w z := hsub.subset (by simp)
  refine ⟨n,hnf,p,(by simpa only [roughPrimeUniverse,Finset.mem_sort] using hp),
    hcop.1,hmul,?_,?_⟩
  · change _ = xs
    rw [restored,← hcanon,List.take_left' hu,List.drop_left' hu,he]
  · rw [← hcanon,List.take_left' hu,hu]

private theorem erase_eval {k : ℕ} (N : ℕ) (a : Affine (k+1)) (n p : ℕ)
    (hl : (n.primeFactorsList.reverse.take (pivot a).val).length = (pivot a).val) :
    a.eval (coords N (k+1) (restored (pivot a).val p n)) -
      a.eval (coords N (k+1) (restored (pivot a).val 1 n)) =
        a.coefficient (pivot a)*(Real.log (p : ℝ)/Real.log (N : ℝ)) := by
  let i := pivot a
  let t (m : ℕ) := coords N (k+1) (restored i.val m n)
  have hdiag (m : ℕ) : t m i = Real.log (m : ℝ)/Real.log (N : ℝ) := by
    dsimp only [t,coords,restored]
    rw [get_pivot _ _ m 1 i.val,hl,if_pos rfl]
  have hoff (j : Fin (k+1)) (hj : j ≠ i) : t p j = t 1 j := by
    dsimp only [t,coords,restored]
    rw [get_pivot _ _ p 1 j.val,hl,if_neg (fun he => hj (Fin.ext he))]
  change a.eval (t p)-a.eval (t 1)=_
  simp only [Affine.eval]
  rw [add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [hdiag,hdiag]; simp
  · intro j _ hj
    rw [hoff j hj,sub_self]
  · simp

private theorem flip_distance {k : ℕ} (a : Affine (k+1)) (x y : Fin (k+1) → ℝ)
    (tau : ℝ) (ht : 0 ≤ tau) (hxy : ∀ i, |x i-y i| ≤ tau)
    (hflip : ¬(a.eval x < 0 ↔ a.eval y < 0)) :
    a.coefficient (pivot a) ≠ 0 ∧
      |a.eval x| ≤ ((k+1 : ℕ):ℝ)*|a.coefficient (pivot a)|*tau := by
  have hn : a.coefficient (pivot a) ≠ 0 := by
    intro h
    have ha (j : Fin (k+1)) : a.coefficient j=0 := by
      exact abs_nonpos_iff.mp (by simpa only [h,abs_zero] using mag_max a j)
    exact hflip (by simp [Affine.eval,ha])
  refine ⟨hn,?_⟩
  have h0 : |a.eval x| ≤ |a.eval x-a.eval y| := by
    by_cases h : a.eval x < 0
    · have hy : 0 ≤ a.eval y := le_of_not_gt (fun hyp => hflip (iff_of_true h hyp))
      rw [abs_of_neg h,abs_of_nonpos (by linarith)]
      linarith
    · have hy : a.eval y < 0 := by by_contra hn; exact hflip (iff_of_false h hn)
      rw [abs_of_nonneg (le_of_not_gt h),abs_of_nonneg (by linarith)]
      linarith
  have hs := P4AFull87SamePieceCapVariation.affine_diff a x y tau hxy
  apply (h0.trans hs).trans
  apply mul_le_mul_of_nonneg_right _ ht
  calc
    _ ≤ ∑ _i : Fin (k+1), |a.coefficient (pivot a)| := Finset.sum_le_sum (fun i _ => mag_max a i)
    _ = _ := by simp [nsmul_eq_mul]

/-- Centre indexed by one deterministic family coordinate. There is no
additional sum over the possible marked primes' positions. -/
def familyCentre {J : ℕ} (N : ℕ) (dim : Fin J → ℕ)
    (rows : (j : Fin J) → Affine (dim j+1)) (n r : ℕ) :=
  if h : r < J then centre N (rows ⟨r,h⟩) n else 0

theorem flip_mem_covered (N cap J : ℕ) (hN : 1 < N) (omega v tau : ℝ)
    (hw : 0 < omega) (hv : omega ≤ v) (ht : 0 < tau)
    (dim : Fin J → ℕ) (rows : (s : Fin J) → Affine (dim s+1))
    (s : Fin J) (hdim : dim s+1 ≤ J) {x : ℕ}
    (hx : x ∈ universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (hrank : dim s+1 ≤ x.primeFactorsList.length)
    (y : Fin (dim s+1) → ℝ)
    (hclose : ∀ i, |coords N (dim s+1) x.primeFactorsList.reverse i-y i| ≤ tau)
    (hflip : ¬((rows s).eval (coords N (dim s+1) x.primeFactorsList.reverse) < 0 ↔
        (rows s).eval y < 0)) :
    x ∈ covered N cap J omega v ((J:ℝ)*tau) (familyCentre N dim rows) := by
  let a := rows s
  let i := pivot a
  let b := a.coefficient i
  let W := (J:ℝ)*tau
  have hi : i.val < x.primeFactorsList.reverse.length := by
    rw [List.length_reverse]; exact i.isLt.trans_le hrank
  obtain ⟨n,hn,p,hp,hcop,hmul,hs,hlen⟩ := actual_erasure hx hi
  obtain ⟨hb,hnear⟩ := flip_distance a _ y tau ht.le hclose hflip
  let l := Real.log (p : ℝ)/Real.log (N : ℝ)
  have hvary := erase_eval N a n p hlen
  rw [hs] at hvary
  have hEq : a.eval (coords N _ x.primeFactorsList.reverse) = b*(l-centre N a n) := by
    calc
      _ = a.eval (coords N _ (restored i.val 1 n))+b*l := by
        dsimp only [i,b,l]
        linarith only [hvary]
      _ = _ := by
        unfold centre
        change _ = b*(l- -(_)/b)
        field_simp [hb]
        <;> ring
  have hlim : |l-centre N a n| ≤ W := by
    rw [hEq,abs_mul] at hnear
    have hJ : ((dim s+1 : ℕ) : ℝ) ≤ J := by exact_mod_cast hdim
    apply le_of_mul_le_mul_left (a := |b|) _ (abs_pos.mpr hb)
    calc
      _ ≤ _ := hnear
      _ ≤ (J:ℝ)*|b|*tau :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJ (abs_nonneg _)) ht.le
      _ = _ := by dsimp only [W]; ring
  obtain ⟨_,hpp,hpN,hlo,hhi⟩ := mem_roughPrimeFinset.mp hp
  have hnR : (1:ℝ) < N := by exact_mod_cast hN
  have hn0 := zero_lt_one.trans hnR
  have hpn : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hpow : (N:ℝ)^l = p := by
    calc
      _ = Real.exp (Real.log (p:ℝ)) := by
        rw [Real.rpow_def_of_pos hn0]
        congr 1
        dsimp only [l]
        field_simp [(Real.log_pos hnR).ne']
        <;> ring
      _ = _ := Real.exp_log hpn
  rw [← hpow] at hlo hhi
  have ha := (Real.rpow_le_rpow_left_iff hnR).mp hlo
  have hz := (Real.rpow_lt_rpow_left_iff hnR).mp hhi
  obtain ⟨hlow,hup⟩ := abs_le.mp hlim
  have hW : 0 < W := mul_pos (Nat.cast_pos.mpr ((Nat.zero_le s.val).trans_lt s.isLt)) ht
  have hab : clip omega v (centre N a n-W) ≤ l :=
    max_le ha ((min_le_right _ _).trans (by linarith))
  have hba : l < clip omega v (centre N a n+2*W) :=
    (lt_min hz (by linarith)).trans_le (le_max_right _ _)
  have hwin : p ∈ window N omega v (familyCentre N dim rows n s.val) W := by
    simp only [familyCentre,dif_pos s.isLt,window]
    apply (mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil _)).mpr
    exact ⟨hpp,hpN,(Real.rpow_le_rpow_of_exponent_le hnR.le hab).trans_eq hpow,
      hpow.symm.trans_lt ((Real.rpow_lt_rpow_left_iff hnR).mpr hba)⟩
  apply Finset.mem_image.mpr
  refine ⟨⟨(n,s.val),p⟩,Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
    ⟨hn,Finset.mem_range.mpr s.isLt⟩,Finset.mem_filter.mpr ⟨hwin,hcop⟩⟩,hmul⟩

end
end ImbalancedChen.P4AFull87ActualAffineDeletion
