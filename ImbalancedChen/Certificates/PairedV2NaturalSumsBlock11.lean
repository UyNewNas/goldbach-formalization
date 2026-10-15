import ImbalancedChen.Certificates.PairedV2FullCertificateDataBlock11

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block11 : List (List Approximation) :=
  [approximations502, approximations503, approximations504, approximations505, approximations506, approximations507, approximations508, approximations509, approximations510, approximations511]

theorem strip502_sums :
    (approximations502.map Approximation.lower).sum = 539519020978654 ∧
      (approximations502.map Approximation.upper).sum = 539519278866544 := by
  decide +kernel

theorem strip503_sums :
    (approximations503.map Approximation.lower).sum = 541715972011593 ∧
      (approximations503.map Approximation.upper).sum = 541716230414487 := by
  decide +kernel

theorem strip504_sums :
    (approximations504.map Approximation.lower).sum = 543903533699933 ∧
      (approximations504.map Approximation.upper).sum = 543903792613134 := by
  decide +kernel

theorem strip505_sums :
    (approximations505.map Approximation.lower).sum = 546081702865560 ∧
      (approximations505.map Approximation.upper).sum = 546081962286026 := by
  decide +kernel

theorem strip506_sums :
    (approximations506.map Approximation.lower).sum = 548250476366515 ∧
      (approximations506.map Approximation.upper).sum = 548250736291263 := by
  decide +kernel

theorem strip507_sums :
    (approximations507.map Approximation.lower).sum = 552825693209477 ∧
      (approximations507.map Approximation.upper).sum = 552825954438331 := by
  decide +kernel

theorem strip508_sums :
    (approximations508.map Approximation.lower).sum = 554965607109566 ∧
      (approximations508.map Approximation.upper).sum = 554965868831498 := by
  decide +kernel

theorem strip509_sums :
    (approximations509.map Approximation.lower).sum = 557096110338498 ∧
      (approximations509.map Approximation.upper).sum = 557096372549069 := by
  decide +kernel

theorem strip510_sums :
    (approximations510.map Approximation.lower).sum = 559217199921237 ∧
      (approximations510.map Approximation.upper).sum = 559217462617655 := by
  decide +kernel

theorem strip511_sums :
    (approximations511.map Approximation.lower).sum = 561328872915670 ∧
      (approximations511.map Approximation.upper).sum = 561329136095219 := by
  decide +kernel

theorem block11_lower :
    (block11.map (fun xs => (xs.map Approximation.lower).sum)).sum = 5504904189416703 := by
  change (approximations502.map Approximation.lower).sum + ((approximations503.map Approximation.lower).sum + ((approximations504.map Approximation.lower).sum + ((approximations505.map Approximation.lower).sum + ((approximations506.map Approximation.lower).sum + ((approximations507.map Approximation.lower).sum + ((approximations508.map Approximation.lower).sum + ((approximations509.map Approximation.lower).sum + ((approximations510.map Approximation.lower).sum + ((approximations511.map Approximation.lower).sum + 0))))))))) = 5504904189416703
  rw [strip502_sums.1, strip503_sums.1, strip504_sums.1, strip505_sums.1, strip506_sums.1, strip507_sums.1, strip508_sums.1, strip509_sums.1, strip510_sums.1, strip511_sums.1]

theorem block11_upper :
    (block11.map (fun xs => (xs.map Approximation.upper).sum)).sum = 5504906795003226 := by
  change (approximations502.map Approximation.upper).sum + ((approximations503.map Approximation.upper).sum + ((approximations504.map Approximation.upper).sum + ((approximations505.map Approximation.upper).sum + ((approximations506.map Approximation.upper).sum + ((approximations507.map Approximation.upper).sum + ((approximations508.map Approximation.upper).sum + ((approximations509.map Approximation.upper).sum + ((approximations510.map Approximation.upper).sum + ((approximations511.map Approximation.upper).sum + 0))))))))) = 5504906795003226
  rw [strip502_sums.2, strip503_sums.2, strip504_sums.2, strip505_sums.2, strip506_sums.2, strip507_sums.2, strip508_sums.2, strip509_sums.2, strip510_sums.2, strip511_sums.2]



/-- Each length is checked separately over its original literal list. -/
theorem strip502_length :
    approximations502.length = 512 - firstU (⟨176, by decide⟩ : Fin 186) := by
  rfl

theorem strip503_length :
    approximations503.length = 512 - firstU (⟨177, by decide⟩ : Fin 186) := by
  rfl

theorem strip504_length :
    approximations504.length = 512 - firstU (⟨178, by decide⟩ : Fin 186) := by
  rfl

theorem strip505_length :
    approximations505.length = 512 - firstU (⟨179, by decide⟩ : Fin 186) := by
  rfl

theorem strip506_length :
    approximations506.length = 512 - firstU (⟨180, by decide⟩ : Fin 186) := by
  rfl

theorem strip507_length :
    approximations507.length = 512 - firstU (⟨181, by decide⟩ : Fin 186) := by
  rfl

theorem strip508_length :
    approximations508.length = 512 - firstU (⟨182, by decide⟩ : Fin 186) := by
  rfl

theorem strip509_length :
    approximations509.length = 512 - firstU (⟨183, by decide⟩ : Fin 186) := by
  rfl

theorem strip510_length :
    approximations510.length = 512 - firstU (⟨184, by decide⟩ : Fin 186) := by
  rfl

theorem strip511_length :
    approximations511.length = 512 - firstU (⟨185, by decide⟩ : Fin 186) := by
  rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
