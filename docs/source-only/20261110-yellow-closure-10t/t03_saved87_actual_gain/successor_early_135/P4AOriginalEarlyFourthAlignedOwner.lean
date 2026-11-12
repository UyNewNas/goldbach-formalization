import ImbalancedChen.P1OriginalFourthUniformCutoffLicence
import ImbalancedChen.P4AOrderedThirdFifthOwnersAndTail

namespace ImbalancedChen.P4AOriginalEarlyFourthAlignedOwner
noncomputable section
open scoped Classical
open Set Filter VariableEnvelope HistoricalThirdCoarse
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh refined_step)
open P2OriginalFourthCapProducerInterface
open P5OriginalFourthFifthSourceInputs
open P1OriginalFourthAllRowsAdmission (originalRows4_geometry)
open P1OriginalFourthCommonHistoricalMesh (prefix3)
open P2OriginalSaving16HistoricalMesh (mesh_box_width mesh_box_lower_nonneg)
open P4AOriginalNewFifthUnion (data)

/-- An actual target-deleted prime cannot be on a rational coordinate wall.
This includes the integer endpoint zero. -/
theorem prime_off_wall {N p : ℕ} (hN : 1 < N) (hp : p.Prime) (hd : ¬p ∣ N)
    (u v : ℕ) (hv : 0 < v) : Real.log (p:ℝ)/Real.log (N:ℝ) ≠ (u:ℝ)/v := by
  intro H
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hvr : (0:ℝ)<v := by exact_mod_cast hv
  have H' := (div_eq_div_iff (Real.log_pos hNr).ne' hvr.ne').mp H
  have hl : Real.log ((p:ℝ)^v) = Real.log ((N:ℝ)^u) := by
    simpa only [Real.log_pow,mul_comm] using H'
  have hpR : 0 < (p:ℝ)^v := pow_pos (by exact_mod_cast hp.pos) _
  have hNR : 0 < (N:ℝ)^u := pow_pos (by linarith) _
  have heq := congrArg Real.exp hl
  rw [Real.exp_log hpR, Real.exp_log hNR] at heq
  have hpow : p^v=N^u := by exact_mod_cast heq
  have hdiv : p ∣ N^u := hpow ▸ dvd_pow_self p hv.ne'
  exact hd (hp.dvd_of_dvd_pow hdiv)

/-- At q=256k each archive lattice unit comprises exactly 3k half-open
mesh bins. An archive coordinate interval wholly contains every mesh bin
which owns one of its half-open points. -/
theorem mesh_contained {k u v j : ℕ} (hk : 0<k) {x : ℝ}
    (hB : (u:ℝ)/204800 ≤ x ∧ x < (v:ℝ)/204800)
    (hJ : (j:ℝ)/(614400*(k:ℝ)) ≤ x ∧ x < ((j:ℝ)+1)/(614400*(k:ℝ))) :
    (u:ℝ)/204800 ≤ (j:ℝ)/(614400*(k:ℝ)) ∧
      ((j:ℝ)+1)/(614400*(k:ℝ)) ≤ (v:ℝ)/204800 := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hD : (0:ℝ)<614400*(k:ℝ) := by positivity
  have h1 := hB.1.trans_lt hJ.2
  have h2 := hJ.1.trans_lt hB.2
  have h1' : ((u*(3*k):ℕ):ℝ) < (j+1:ℕ) := by
    have H := (div_lt_div_iff₀ (by norm_num : (0:ℝ)<204800) hD).mp h1
    push_cast; nlinarith only [H]
  have h2' : (j:ℝ) < ((v*(3*k):ℕ):ℝ) := by
    have H := (div_lt_div_iff₀ hD (by norm_num : (0:ℝ)<204800)).mp h2
    push_cast; nlinarith only [H]
  have h1n : u*(3*k) < j+1 := by exact_mod_cast h1'
  have h2n : j < v*(3*k) := by exact_mod_cast h2'
  have h1r : ((u*(3*k):ℕ):ℝ) ≤ j := by exact_mod_cast (Nat.lt_succ_iff.mp h1n)
  have h2r : ((j+1:ℕ):ℝ) ≤ ((v*(3*k):ℕ):ℝ) := by exact_mod_cast (Nat.succ_le_of_lt h2n)
  push_cast at h1r h2r
  exact ⟨(div_le_div_iff₀ (by norm_num : (0:ℝ)<204800) hD).mpr (by nlinarith only [h1r]),
    (div_le_div_iff₀ hD (by norm_num : (0:ℝ)<204800)).mpr (by nlinarith only [h2r])⟩

private theorem aligned_real_cell {d : ℕ} {k : ℕ} (hk : 0<k)
    {j : Fin d → Fin (refinedMesh (256*k)+1)} (i : Fin d) :
    logPrimeMeshLo 0 (19/96) (refinedMesh (256*k)) j i =
      ((j i).val:ℝ)/(614400*(k:ℝ)) ∧
    logPrimeMeshHi 0 (19/96) (refinedMesh (256*k)) j i =
      (((j i).val:ℝ)+1)/(614400*(k:ℝ)) := by
  have hq : 0<256*k := by omega
  simp only [logPrimeMeshLo,logPrimeMeshHi,logPrimeMeshPoint,refined_step _ hq,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,zero_add]
  constructor <;> field_simp <;> ring

/-- Every actual original fourth row gives a genuine old third owner
on the aligned cofinal mesh. The same statement covers words arbitrarily
close to two equal coordinates. -/
theorem all_fourth_owners {e a : ℝ} {k : ℕ} (hk : 0<k) (ha : a≤3/200)
    (hsmall : 4*e+e/20 ≤ 1/3200)
    (hmesh : logPrimeMeshStep 0 (19/96) (refinedMesh (256*k)) ≤ e/20)
    (r : ProducerRow) (hr : r∈originalRows4) {N cap : ℕ} (hN : 1<N) {w z : ℝ}
    (p : Fin 4→ℕ) (hp : ∀ i,p i∈roughPrimeUniverse N cap w z)
    (ht : actualPrimeTupleLog N p∈r.box) :
    P1ThirdFallbackSupport.frozenSupported e (e/20) (refinedMesh (256*k)) a (N:ℝ)
      [p 3,p 2,p 1,p 0] := by
  let t := actualPrimeTupleLog N p
  let m := refinedMesh (256*k)
  have G := originalRows4_geometry r hr
  have H := r.ordered G t ht
  have top : t 0≤39/200 := (ht.2 0).trans (by exact_mod_cast G.2.2.2.2.2.1)
  have low : 3/200≤t 3 := (show (3/200:ℝ)≤(r.lower 3:ℝ) by
    exact_mod_cast G.2.2.2.2.1).trans (ht.1 3)
  have hbox : prefix3 t∈logPrimeBox (fun _=>(0:ℝ)) (fun _=>(19/96:ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro i
    change 0≤t i.castSucc ∧ t i.castSucc<19/96
    fin_cases i <;> constructor <;> linarith [H.1.1,H.1.2.1,H.1.2.2.1,H.2.2]
  obtain ⟨j,hj⟩ := exists_logPrimeMeshCell 0 (19/96) m hbox
  have inside (i : Fin 3) :
      (r.lower i.castSucc:ℝ) ≤ (qLogPrimeMeshLo 0 (19/96) m j i:ℝ) ∧
      (qLogPrimeMeshHi 0 (19/96) m j i:ℝ) ≤ (r.upper i.castSucc:ℝ) := by
    let j' := i.castSucc
    have pr := mem_roughPrimeUniverse.mp (hp j')
    have ne := prime_off_wall hN pr.2.1 pr.2.2.1 (r.hi j') 204800 (by decide)
    have upper : t j'<(r.upper j':ℝ) := lt_of_le_of_ne (ht.2 j') (by
      simpa [t,j',actualPrimeTupleLog,ProducerRow.upper] using ne)
    have hd := aligned_real_cell hk (j:=j) i
    have hm := mem_logPrimeMeshCell.mp hj i
    rw [hd.1,hd.2] at hm
    have hb : (r.lo j':ℝ)/204800 ≤ t j' ∧ t j'<(r.hi j':ℝ)/204800 := by
      simpa [ProducerRow.lower,ProducerRow.upper] using And.intro (ht.1 j') upper
    have hs := mesh_contained hk hb hm
    rw [← hd.1,← hd.2] at hs
    simpa [ProducerRow.lower,ProducerRow.upper,j',m] using hs
  have orderedBins (i : Fin 2) :
      qLogPrimeMeshHi 0 (19/96) m j i.succ ≤ qLogPrimeMeshLo 0 (19/96) m j i.castSucc := by
    have hab : r.upper i.succ.castSucc ≤ r.lower i.castSucc.castSucc := by
      have hi := G.2.2.2.1 i.castSucc
      apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℚ)≤204800)
      exact_mod_cast hi
    have hr' : (r.upper i.succ.castSucc:ℝ) ≤ (r.lower i.castSucc.castSucc:ℝ) := by exact_mod_cast hab
    exact_mod_cast (inside i.succ).2.trans (hr'.trans (inside i.castSucc).1)
  have hb := inBox_of_cell hj
  have hwidth : ((box m j).width:ℝ) ≤ e/20 := by rw [mesh_box_width]; exact hmesh
  have sw := P4AOriginalFull87GammaApproximation.side_widths hwidth
  have hret : j∈cells e (e/20) m := by
    apply (mem_cells _ _ _ _).mpr
    refine ⟨RationalBox.wellFormed_of_inBox hb,mesh_box_lower_nonneg m j,
      orderedBins 1,orderedBins 0,?_,hwidth⟩
    change ((box m j).ux:ℝ)≤extendedFirstStop-4*e
    change (box m j).InBox (t 0) (t 1) (t 2) at hb
    unfold extendedFirstStop
    linarith [hb.1,sw.1]
  have hN' : (1:ℝ)<N := by exact_mod_cast hN
  have hcut : (N:ℝ)^a ≤ p 2 := by
    rw [←actualPrimeTupleLog_rpow hN p
      (fun i=>(mem_roughPrimeUniverse.mp (hp i)).2.1.pos) 2]
    exact Real.rpow_le_rpow_of_exponent_le hN'.le (ha.trans (low.trans H.2.2))
  have t3 : primeHistoryLogCoordinates (N:ℝ) 3 [p 2,p 1,p 0] = prefix3 t := by
    funext i; fin_cases i <;> rfl
  change P1ThirdFallbackSupport.supported e (e/20) m a (N:ℝ) [p 2,p 1,p 0]
  exact ⟨⟨rfl,hcut⟩,j,hret,by simpa only [t3] using hj⟩

theorem updated_root_on_fourth {e : ℚ} (he : 0≤(e:ℝ)) {k : ℕ} (hk : 0<k)
    {a omega : ℝ} (ha : a≤3/200) (hwa : omega≤a) (hsmall : 4*(e:ℝ)+(e:ℝ)/20≤1/3200)
    (hmesh : logPrimeMeshStep 0 (19/96) (refinedMesh (256*k)) ≤ (e:ℝ)/20)
    (r : ProducerRow) (hr : r∈originalRows4) {N cap : ℕ} (hN : 1<N) {w z : ℝ}
    (p : Fin 4→ℕ) (hp : ∀i,p i∈roughPrimeUniverse N cap w z) (ht : actualPrimeTupleLog N p∈r.box) :
    let d := data e (256*k) a
    P4AOriginalOrderedThirdFullPolicy.current d omega N [p 3,p 2,p 1,p 0] =
      P4AOriginalOrderedThirdFullPolicy.prior d N [p 3,p 2,p 1,p 0] := by
  exact P4AOriginalOrderedThirdFullPolicy.root_on_old_owner he (by exact_mod_cast hN.le) hwa
    (all_fourth_owners hk ha hsmall hmesh r hr hN p hp ht)

end
end ImbalancedChen.P4AOriginalEarlyFourthAlignedOwner
