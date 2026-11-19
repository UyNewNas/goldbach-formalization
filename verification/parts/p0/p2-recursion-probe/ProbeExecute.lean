import ImbalancedChen.Probes.IterativeProbe

def main : IO Unit := do
  unless ImbalancedChen.Probes.IterativeProbe.outputChecks do
    throw (IO.userError "P2_RECURSION_PROBE_OUTPUT_MISMATCH")
  IO.println "P2_RECURSION_PROBE_OUTPUT_OK: leaf=1 sample=7 surplus=7 sizeOf=7"
