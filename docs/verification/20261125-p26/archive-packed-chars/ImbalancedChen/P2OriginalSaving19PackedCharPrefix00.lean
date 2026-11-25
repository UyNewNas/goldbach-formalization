import ImbalancedChen.P2OriginalSaving19PackedCharData00

namespace ImbalancedChen.P2OriginalSaving19PackedChars
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option stderrAsMessages false

-- Mechanical quotation of the original first 20 UTF-8 decoded codepoints,
-- including CRLF. No line ending normalization or JSON parsing occurred.
def geometryPackedPrefix20 : List Char := [Char.ofNat 123, Char.ofNat 13, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 34, Char.ofNat 100, Char.ofNat 105, Char.ofNat 109, Char.ofNat 101, Char.ofNat 110, Char.ofNat 115, Char.ofNat 105, Char.ofNat 111, Char.ofNat 110, Char.ofNat 34, Char.ofNat 58, Char.ofNat 32, Char.ofNat 56, Char.ofNat 44]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 prefix_before_guard"
  err.flush

theorem geometryPackedChars00_take20 :
    geometryPackedChars00.take 20 = geometryPackedPrefix20 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 prefix_after_guard"
  err.flush

#print axioms geometryPackedChars00_take20
end ImbalancedChen.P2OriginalSaving19PackedChars
