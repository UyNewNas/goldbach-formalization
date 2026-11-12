import ImbalancedChen.P4AOriginalFiniteFallbackJointHigh

namespace ImbalancedChen.P4AOriginalFiniteFallbackGroupedAtoms
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackPhysicalSelected (head upperGroups)
open P4AOriginalFiniteFallbackSelectedMask (Mask front selected remaining perm)
open P4AOriginalFiniteFallbackCommonGroups (choice groupsAt)
open P4AOrderedThirdPhysicalAtoms (boxScalar)
open P4AUpperTaggedParityCompiler (coefficient)
open P4AOriginalFull87RawChronology (cutoff)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4BUpperSelectedBoxCapacity (endpoint endpoints groups groups_partition)

def slots (m N : ℕ) (d : OriginalData) (w tau x U eta : ℝ) (p : Fin 3 → ℕ) (J : List ℕ) :=
  let g := choice m N d w p
  let D := x^(g.2+4*eta)
  let A := U/x^eta
  let H := actualPrimeFineLabelIntegerUpper N tau
  match g.1 with
  | some kind => groups D A H (selected kind (head J)) (remaining kind (head J) (J.drop 3)) J
  | none => groups D A H (J.take 1) (J.drop 1) J

theorem partition (m N : ℕ) (d : OriginalData) (w tau x U eta : ℝ) (p : Fin 3 → ℕ) (J : List ℕ)
    (hJ : 3≤J.length) :
    let g := slots m N d w tau x U eta p J
    (g.1++(g.2.1++g.2.2)).Perm J := by
  have H : front (head J) (J.drop 3)=J := by
    rcases J with _|⟨a,J⟩ <;> try simp at hJ
    rcases J with _|⟨b,J⟩ <;> try simp at hJ
    rcases J with _|⟨c,J⟩ <;> try simp at hJ
    rfl
  dsimp only [slots]
  split
  · apply groups_partition
    simpa only [H] using perm _ (head J) (J.drop 3)
  · apply groups_partition
    simpa only [List.take_append_drop] using List.Perm.refl J

def clipped (N : ℕ) (w tau : ℝ) (j : ℕ) :=
  actualPrimeFineLabelFinset N tau j∩roughPrimeFinset N N ((N:ℝ)^w) (cutoff N)
def box (N : ℕ) (w tau : ℝ) := actualPrimeSlotBox (clipped N w tau)

theorem sizes (m N : ℕ) (d : OriginalData) (w tau x U eta : ℝ) (p : Fin 3 → ℕ) (J : List ℕ) :
    let S := slots m N d w tau x U eta p J
    let hi := actualPrimeFineLabelIntegerUpper N tau
    groupsAt m N d w tau x U eta p J=(endpoint hi S.1,endpoint hi S.2.1,endpoint hi S.2.2) := by
  dsimp only [slots,groupsAt]
  split <;> rfl

def beta (N : ℕ) (w L : ℝ) (J : List ℕ) (a : ℕ) :=
  if 0≤(-1:ℝ)^J.length then actualSmallRosserPlus N N ((N:ℝ)^w) L a else actualSmallRosserMinus N N ((N:ℝ)^w) L a

theorem rho_atom (f : List ℕ→Bool) (N : ℕ) (w tau L : ℝ) (J : List ℕ) {a n : ℕ}
    (ha : a∈actualSmallRosserSupport N N ((N:ℝ)^w))
    (hn : n∈P4AUpperTaggedParityCompiler.universe N N ((N:ℝ)^w) (cutoff N))
    (hat : n∈((actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J).filter List.SortedGT).image List.prod) :
    P4AUpperTaggedBetaAttachment.rho f (fun _ => []) N N ((N:ℝ)^w) (cutoff N) tau L (a*n)=
      coefficient f (fun _ => []) N N ((N:ℝ)^w) (cutoff N) tau n*beta N w L J a := by
  rw [P4AUpperTaggedBetaAttachment.rho_at_product _ _ _ _ _ _ _ _ ha hn]
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hat
  obtain ⟨hB,hG⟩ := Finset.mem_filter.mp hps
  have hp := actualPrimeSlotBox_prime _ J (fun _ _ q hq => (mem_actualPrimeFineLabelFinset.mp hq).1) ps hB
  have hlen := actualPrimeSlotBox_length _ J ps hB
  have hmu : (ArithmeticFunction.moebius ps.prod:ℝ)=(-1:ℝ)^J.length := by
    rw [←hlen]; exact_mod_cast moebius_list_prod_eq_negOnePow_length ps hG.nodup hp
  simp only [coefficient,if_pos hn,beta,hmu]
  split_ifs <;> simp_all

theorem group_support (N : ℕ) (w tau : ℝ) (J : List ℕ) (n : ℕ)
    (h : n∈(box N w tau J).image List.prod) : (n:ℝ)≤endpoint (actualPrimeFineLabelIntegerUpper N tau) J := by
  obtain ⟨ps,hp,rfl⟩ := Finset.mem_image.mp h
  rw [P4BUpperSelectedBoxCapacity.endpoint_eq_cast]
  exact_mod_cast actualPrimeSlotBox_prod_le_upper _ _ J
    (fun i _ q hq => actualPrimeFineLabelFinset_le_integerUpper (Finset.mem_inter.mp hq).1) ps hp

theorem group_unit (N : ℕ) (w tau : ℝ) (J : List ℕ) (n : ℕ) :
    |actualNormalizedPrimeTupleCoefficient (box N w tau J) J.length n|≤1 :=
  actualPrimeSlotBox_normalized_abs_le_one _ J
    (fun i _ q hq => (mem_actualPrimeFineLabelFinset.mp (Finset.mem_inter.mp hq).1).1) n

theorem regroup (m N : ℕ) (hN : 1<N) (d : OriginalData) (w tau x U eta : ℝ) (ht : 0<tau)
    (p : Fin 3 → ℕ) (J : List ℕ) (horder : J.Pairwise (·≥·)) (hr : 3≤J.length)
    (f : List ℕ → Bool) (H : ℕ→ℝ) :
    let S := slots m N d w tau x U eta p J
    let T := box N w tau
    let C := boxScalar f N N ((N:ℝ)^w) (cutoff N) tau J/(actualPrimeFineWordMultiplicity J:ℝ)
    (∑ n∈((actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J).filter List.SortedGT).image List.prod,
      coefficient f (fun _ => []) N N ((N:ℝ)^w) (cutoff N) tau n*H n)=
    ∑ a∈(T S.1).image List.prod,∑ b∈(T S.2.1).image List.prod,∑ c∈(T S.2.2).image List.prod,
      (C*(S.1.length.factorial:ℝ)*(S.2.1.length.factorial:ℝ)*(S.2.2.length.factorial:ℝ))*
        actualNormalizedPrimeTupleCoefficient (T S.1) S.1.length a*
        actualNormalizedPrimeTupleCoefficient (T S.2.1) S.2.1.length b*
        actualNormalizedPrimeTupleCoefficient (T S.2.2) S.2.2.length c*
        ((ArithmeticFunction.moebius (a*b*c):ℝ)*H (a*b*c)) := by
  let S := slots m N d w tau x U eta p J
  let C := boxScalar f N N ((N:ℝ)^w) (cutoff N) tau J/(actualPrimeFineWordMultiplicity J:ℝ)
  let t := clipped N w tau
  let G (n : ℕ) := (ArithmeticFunction.moebius n:ℝ)*H n
  rw [←P4AOriginalFiniteFallbackAtoms.rectangular_factorial f w N hN tau ht J horder H]
  change C*(∑ ps∈actualPrimeSlotBox t J,G ps.prod)=_
  rw [Finset.mul_sum,←actualPrimeSlotBox_product_sum_perm t (partition m N d w tau x U eta p J hr) (fun n => C*G n)]
  rw [actualPrimeSlotBox_product_sum_append]
  simp_rw [actualPrimeSlotBox_product_sum_append]
  simpa only [mul_assoc] using actualPrimeTuple_threeGroup_sum_normalized
    (actualPrimeSlotBox t S.1) (actualPrimeSlotBox t S.2.1) (actualPrimeSlotBox t S.2.2)
    S.1.length S.2.1.length S.2.2.length C G

/-- Reconstruct the original sign-attached physical coefficient, at a
fixed supported small factor, from these exact clipped group boxes. -/
theorem attached (m N : ℕ) (hN : 1<N) (d : OriginalData) (w tau L x U eta : ℝ) (ht : 0<tau)
    (p : Fin 3 → ℕ) (J : List ℕ) (horder : J.Pairwise (·≥·)) (hr : 3≤J.length)
    (f : List ℕ → Bool) (H : ℕ→ℝ) {v : ℕ} (hv : v∈actualSmallRosserSupport N N ((N:ℝ)^w)) :
    let S := slots m N d w tau x U eta p J
    let T := box N w tau
    let C := boxScalar f N N ((N:ℝ)^w) (cutoff N) tau J/(actualPrimeFineWordMultiplicity J:ℝ)
    let rawBox := ((actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J).filter List.SortedGT).image List.prod
    let V := P4AUpperTaggedParityCompiler.universe N N ((N:ℝ)^w) (cutoff N)
    (∑ n∈rawBox.filter (·∈V),P4AUpperTaggedBetaAttachment.rho f (fun _ => []) N N ((N:ℝ)^w)
      (cutoff N) tau L (v*n)*H (v*n))=
    ∑ a∈(T S.1).image List.prod,∑ b∈(T S.2.1).image List.prod,∑ c∈(T S.2.2).image List.prod,
      (C*(S.1.length.factorial:ℝ)*(S.2.1.length.factorial:ℝ)*(S.2.2.length.factorial:ℝ))*
        actualNormalizedPrimeTupleCoefficient (T S.1) S.1.length a*
        actualNormalizedPrimeTupleCoefficient (T S.2.1) S.2.1.length b*
        actualNormalizedPrimeTupleCoefficient (T S.2.2) S.2.2.length c*
        ((ArithmeticFunction.moebius (a*b*c):ℝ)*(beta N w L J v*H (v*(a*b*c)))) := by
  dsimp only
  rw [←regroup m N hN d w tau x U eta ht p J horder hr f (fun n => beta N w L J v*H (v*n)),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : n∈P4AUpperTaggedParityCompiler.universe N N ((N:ℝ)^w) (cutoff N)
  · rw [if_pos h,rho_atom _ _ _ _ _ J hv h hn]; ring
  · simp [h,coefficient]

end
end ImbalancedChen.P4AOriginalFiniteFallbackGroupedAtoms
