import ImbalancedChen.Certificates.PairedV2FullCertificateData

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block09 : List (List Approximation) :=
  [approximations470, approximations471, approximations472, approximations473, approximations474, approximations475, approximations476, approximations477, approximations478, approximations479, approximations480, approximations481, approximations482, approximations483, approximations484, approximations485]

theorem strip470_sums :
    (approximations470.map Approximation.lower).sum = 458711463543845 ∧
      (approximations470.map Approximation.upper).sum = 458711700838694 := by
  decide +kernel

theorem strip471_sums :
    (approximations471.map Approximation.lower).sum = 461228708282866 ∧
      (approximations471.map Approximation.upper).sum = 461228946251758 := by
  decide +kernel

theorem strip472_sums :
    (approximations472.map Approximation.lower).sum = 463735922046423 ∧
      (approximations472.map Approximation.upper).sum = 463736160678594 := by
  decide +kernel

theorem strip473_sums :
    (approximations473.map Approximation.lower).sum = 466233870612692 ∧
      (approximations473.map Approximation.upper).sum = 466234109903932 := by
  decide +kernel

theorem strip474_sums :
    (approximations474.map Approximation.lower).sum = 471439699482360 ∧
      (approximations474.map Approximation.upper).sum = 471439940380031 := by
  decide +kernel

theorem strip475_sums :
    (approximations475.map Approximation.lower).sum = 473910591238783 ∧
      (approximations475.map Approximation.upper).sum = 473910832779173 := by
  decide +kernel

theorem strip476_sums :
    (approximations476.map Approximation.lower).sum = 476372198383715 ∧
      (approximations476.map Approximation.upper).sum = 476372440561672 := by
  decide +kernel

theorem strip477_sums :
    (approximations477.map Approximation.lower).sum = 478824517031824 ∧
      (approximations477.map Approximation.upper).sum = 478824759842296 := by
  decide +kernel

theorem strip478_sums :
    (approximations478.map Approximation.lower).sum = 481267543317578 ∧
      (approximations478.map Approximation.upper).sum = 481267786755589 := by
  decide +kernel

theorem strip479_sums :
    (approximations479.map Approximation.lower).sum = 483701273392727 ∧
      (approximations479.map Approximation.upper).sum = 483701517451986 := by
  decide +kernel

theorem strip480_sums :
    (approximations480.map Approximation.lower).sum = 486125165751843 ∧
      (approximations480.map Approximation.upper).sum = 486125410427309 := by
  decide +kernel

theorem strip481_sums :
    (approximations481.map Approximation.lower).sum = 488538997104949 ∧
      (approximations481.map Approximation.upper).sum = 488539242389596 := by
  decide +kernel

theorem strip482_sums :
    (approximations482.map Approximation.lower).sum = 490943521676102 ∧
      (approximations482.map Approximation.upper).sum = 490943767565328 := by
  decide +kernel

theorem strip483_sums :
    (approximations483.map Approximation.lower).sum = 493338735693745 ∧
      (approximations483.map Approximation.upper).sum = 493338982183044 := by
  decide +kernel

theorem strip484_sums :
    (approximations484.map Approximation.lower).sum = 495724635409935 ∧
      (approximations484.map Approximation.upper).sum = 495724882496311 := by
  decide +kernel

theorem strip485_sums :
    (approximations485.map Approximation.lower).sum = 498101217099358 ∧
      (approximations485.map Approximation.upper).sum = 498101464777001 := by
  decide +kernel

theorem block09_lower :
    (block09.map (fun xs => (xs.map Approximation.lower).sum)).sum = 7668198060068745 := by
  change (approximations470.map Approximation.lower).sum + ((approximations471.map Approximation.lower).sum + ((approximations472.map Approximation.lower).sum + ((approximations473.map Approximation.lower).sum + ((approximations474.map Approximation.lower).sum + ((approximations475.map Approximation.lower).sum + ((approximations476.map Approximation.lower).sum + ((approximations477.map Approximation.lower).sum + ((approximations478.map Approximation.lower).sum + ((approximations479.map Approximation.lower).sum + ((approximations480.map Approximation.lower).sum + ((approximations481.map Approximation.lower).sum + ((approximations482.map Approximation.lower).sum + ((approximations483.map Approximation.lower).sum + ((approximations484.map Approximation.lower).sum + ((approximations485.map Approximation.lower).sum + 0))))))))))))))) = 7668198060068745
  rw [strip470_sums.1, strip471_sums.1, strip472_sums.1, strip473_sums.1, strip474_sums.1, strip475_sums.1, strip476_sums.1, strip477_sums.1, strip478_sums.1, strip479_sums.1, strip480_sums.1, strip481_sums.1, strip482_sums.1, strip483_sums.1, strip484_sums.1, strip485_sums.1]
  decide +kernel

theorem block09_upper :
    (block09.map (fun xs => (xs.map Approximation.upper).sum)).sum = 7668201945282314 := by
  change (approximations470.map Approximation.upper).sum + ((approximations471.map Approximation.upper).sum + ((approximations472.map Approximation.upper).sum + ((approximations473.map Approximation.upper).sum + ((approximations474.map Approximation.upper).sum + ((approximations475.map Approximation.upper).sum + ((approximations476.map Approximation.upper).sum + ((approximations477.map Approximation.upper).sum + ((approximations478.map Approximation.upper).sum + ((approximations479.map Approximation.upper).sum + ((approximations480.map Approximation.upper).sum + ((approximations481.map Approximation.upper).sum + ((approximations482.map Approximation.upper).sum + ((approximations483.map Approximation.upper).sum + ((approximations484.map Approximation.upper).sum + ((approximations485.map Approximation.upper).sum + 0))))))))))))))) = 7668201945282314
  rw [strip470_sums.2, strip471_sums.2, strip472_sums.2, strip473_sums.2, strip474_sums.2, strip475_sums.2, strip476_sums.2, strip477_sums.2, strip478_sums.2, strip479_sums.2, strip480_sums.2, strip481_sums.2, strip482_sums.2, strip483_sums.2, strip484_sums.2, strip485_sums.2]
  decide +kernel


end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
