import ImbalancedChen.P2OriginalSaving19PackedCharData00

namespace ImbalancedChen.P2OriginalSaving19PackedChars
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option stderrAsMessages false

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 length_before_guard"
  err.flush

theorem geometryPacked00_count : geometryPacked00.count = 195134 := by
  decide +kernel

theorem geometryPackedChars00_length : geometryPackedChars00.length = 195134 := by
  rw [geometryPackedChars00, Tree.length_toList]
  exact geometryPacked00_count

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 length_after_guard"
  err.flush

#print axioms geometryPacked00_count
#print axioms geometryPackedChars00_length
end ImbalancedChen.P2OriginalSaving19PackedChars
