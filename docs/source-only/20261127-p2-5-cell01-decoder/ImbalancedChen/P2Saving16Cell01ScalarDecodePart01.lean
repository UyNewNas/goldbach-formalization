import ImbalancedChen.P2OriginalSaving16DecoderChars
import ImbalancedChen.P2Saving16Cell01TypedPayload
import ImbalancedChen.P2Saving16Cell00ScalarDecode

/-! Cell01 decoder proof candidates. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/
namespace ImbalancedChen.P2Saving16Cell01ScalarDecode
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell01TypedPayload

theorem rational128_decoded :
    parseRational (String.ofList ['2', '0', '6', '4', '4', '9', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0']) = .ok rational128 := by
  rw [parseRational_ofList]
  rfl

theorem rational129_decoded :
    parseRational (String.ofList ['7', '6', '3', '2', '9', '3', '4', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational129 := by
  rw [parseRational_ofList]
  rfl

theorem rational130_decoded :
    parseRational (String.ofList ['8', '2', '8', '2', '0', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational130 := by
  rw [parseRational_ofList]
  rfl

theorem rational131_decoded :
    parseRational (String.ofList ['1', '/', '3', '7', '5', '0', '0', '0']) = .ok rational131 := by
  rw [parseRational_ofList]
  rfl

theorem rational132_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '6', '9', '/', '1', '3', '5', '0', '0', '0', '0', '0']) = .ok rational132 := by
  rw [parseRational_ofList]
  rfl

theorem rational133_decoded :
    parseRational (String.ofList ['0']) = .ok rational133 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational053_decoded

theorem rational134_decoded :
    parseRational (String.ofList ['1', '6', '4', '0', '6', '1', '7', '/', '2', '5', '0', '0', '0', '0', '0', '0']) = .ok rational134 := by
  rw [parseRational_ofList]
  rfl

theorem rational135_decoded :
    parseRational (String.ofList ['6', '7', '1', '8', '7', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0']) = .ok rational135 := by
  rw [parseRational_ofList]
  rfl

theorem rational136_decoded :
    parseRational (String.ofList ['1', '3', '0', '3', '2', '0', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0']) = .ok rational136 := by
  rw [parseRational_ofList]
  rfl

theorem rational137_decoded :
    parseRational (String.ofList ['1', '/', '7', '5', '0', '0', '0', '0']) = .ok rational137 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational059_decoded

theorem rational138_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational138 := by
  rw [parseRational_ofList]
  rfl

theorem rational139_decoded :
    parseRational (String.ofList ['7', '2', '8', '9', '0', '4', '6', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational139 := by
  rw [parseRational_ofList]
  rfl

theorem rational140_decoded :
    parseRational (String.ofList ['2', '2', '3', '4', '4', '1', '1', '/', '1', '4', '0', '0', '0', '0', '0', '0']) = .ok rational140 := by
  rw [parseRational_ofList]
  rfl

theorem rational141_decoded :
    parseRational (String.ofList ['1', '0', '9', '2', '2', '1', '4', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational141 := by
  rw [parseRational_ofList]
  rfl

theorem rational142_decoded :
    parseRational (String.ofList ['4', '8', '5', '9', '3', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational142 := by
  rw [parseRational_ofList]
  rfl

theorem rational143_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '2', '3', '/', '3', '0', '0', '0', '0', '0', '0']) = .ok rational143 := by
  rw [parseRational_ofList]
  rfl

theorem rational144_decoded :
    parseRational (String.ofList ['1', '1', '7', '6', '6', '1', '3', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok rational144 := by
  rw [parseRational_ofList]
  rfl

theorem rational145_decoded :
    parseRational (String.ofList ['3', '0', '4', '7', '0', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational145 := by
  rw [parseRational_ofList]
  rfl

theorem rational146_decoded :
    parseRational (String.ofList ['2', '2', '2', '6', '6', '1', '0', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']) = .ok rational146 := by
  rw [parseRational_ofList]
  rfl

theorem rational147_decoded :
    parseRational (String.ofList ['5', '6', '7', '2', '0', '3', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']) = .ok rational147 := by
  rw [parseRational_ofList]
  rfl

theorem rational148_decoded :
    parseRational (String.ofList ['2', '5', '7', '8', '2', '1', '1', '/', '3', '7', '5', '0', '0', '0', '0', '0']) = .ok rational148 := by
  rw [parseRational_ofList]
  rfl

theorem rational149_decoded :
    parseRational (String.ofList ['3', '0', '4', '6', '9', '9', '9', '/', '6', '0', '0', '0', '0', '0', '0', '0']) = .ok rational149 := by
  rw [parseRational_ofList]
  rfl

theorem rational150_decoded :
    parseRational (String.ofList ['4', '6', '8', '8', '7', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational150 := by
  rw [parseRational_ofList]
  rfl

theorem rational151_decoded :
    parseRational (String.ofList ['1', '4', '0', '6', '6', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational151 := by
  rw [parseRational_ofList]
  rfl

theorem rational152_decoded :
    parseRational (String.ofList ['2', '0', '4', '6', '7', '6', '7', '/', '4', '7', '2', '0', '0', '0', '0', '0', '0']) = .ok rational152 := by
  rw [parseRational_ofList]
  rfl

theorem rational153_decoded :
    parseRational (String.ofList ['3', '9', '0', '6', '3', '7', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational153 := by
  rw [parseRational_ofList]
  rfl

theorem rational154_decoded :
    parseRational (String.ofList ['4', '0', '4', '6', '8', '6', '3', '/', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok rational154 := by
  rw [parseRational_ofList]
  rfl

theorem rational155_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '6', '0', '3', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational155 := by
  rw [parseRational_ofList]
  rfl

theorem rational156_decoded :
    parseRational (String.ofList ['1', '1', '7', '1', '8', '8', '7', '/', '5', '0', '0', '0', '0', '0', '0']) = .ok rational156 := by
  rw [parseRational_ofList]
  rfl

theorem rational157_decoded :
    parseRational (String.ofList ['4', '8', '2', '8', '1', '6', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0']) = .ok rational157 := by
  rw [parseRational_ofList]
  rfl

theorem rational158_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '7', '0', '0', '0', '0', '0', '0']) = .ok rational158 := by
  rw [parseRational_ofList]
  rfl

theorem rational159_decoded :
    parseRational (String.ofList ['2', '3', '4', '3', '7', '9', '/', '1', '6', '0', '0', '0', '0', '0']) = .ok rational159 := by
  rw [parseRational_ofList]
  rfl

theorem rational160_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational160 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational079_decoded

theorem rational161_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational161 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational076_decoded

theorem rational162_decoded :
    parseRational (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational162 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational084_decoded

theorem rational163_decoded :
    parseRational (String.ofList ['2', '1', '7', '1', '8', '7', '3', '/', '2', '9', '5', '0', '0', '0', '0', '0']) = .ok rational163 := by
  rw [parseRational_ofList]
  rfl

theorem rational164_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok rational164 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational094_decoded

theorem rational165_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '3', '3', '/', '9', '0', '0', '0', '0', '0', '0']) = .ok rational165 := by
  rw [parseRational_ofList]
  rfl

theorem rational166_decoded :
    parseRational (String.ofList ['1', '1', '8', '5', '9', '4', '4', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']) = .ok rational166 := by
  rw [parseRational_ofList]
  rfl

theorem rational167_decoded :
    parseRational (String.ofList ['3', '9', '0', '6', '2', '9', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok rational167 := by
  rw [parseRational_ofList]
  rfl

theorem rational168_decoded :
    parseRational (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational168 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational083_decoded

theorem rational169_decoded :
    parseRational (String.ofList ['3', '7', '7', '8', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0']) = .ok rational169 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational092_decoded

theorem rational170_decoded :
    parseRational (String.ofList ['2', '7', '3', '9', '0', '6', '2', '1', '/', '4', '7', '2', '0', '0', '0', '0', '0', '0']) = .ok rational170 := by
  rw [parseRational_ofList]
  rfl

theorem rational171_decoded :
    parseRational (String.ofList ['1', '8', '7', '5', '0', '3', '/', '1', '0', '0', '0', '0', '0', '0']) = .ok rational171 := by
  rw [parseRational_ofList]
  rfl

theorem rational172_decoded :
    parseRational (String.ofList ['4', '0', '4', '6', '8', '6', '3', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0']) = .ok rational172 := by
  rw [parseRational_ofList]
  rfl

theorem rational173_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '3', '3', '/', '4', '5', '0', '0', '0', '0', '0']) = .ok rational173 := by
  rw [parseRational_ofList]
  rfl

theorem rational174_decoded :
    parseRational (String.ofList ['1', '1', '8', '5', '9', '4', '4', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational174 := by
  rw [parseRational_ofList]
  rfl

theorem rational175_decoded :
    parseRational (String.ofList ['3', '9', '0', '6', '2', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']) = .ok rational175 := by
  rw [parseRational_ofList]
  rfl

theorem rational176_decoded :
    parseRational (String.ofList ['1', '9', '5', '3', '1', '3', '7', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok rational176 := by
  rw [parseRational_ofList]
  rfl

theorem rational177_decoded :
    parseRational (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0']) = .ok rational177 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational090_decoded

theorem rational178_decoded :
    parseRational (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational178 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational102_decoded

theorem rational179_decoded :
    parseRational (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '7', '0', '0', '0', '0', '0', '0']) = .ok rational179 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational103_decoded

theorem rational180_decoded :
    parseRational (String.ofList ['4', '0', '6', '8', '0', '0', '2', '3', '3', '9', '3', '4', '3', '9', '7', '5', '9', '7', '7', '2', '5', '2', '2', '0', '3', '6', '7', '8', '7', '1', '2', '6', '8', '6', '0', '5', '5', '3', '9', '7', '4', '3', '0', '0', '8', '1', '/', '1', '3', '4', '7', '2', '2', '2', '0', '8', '1', '1', '6', '1', '1', '3', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational180 := by
  rw [parseRational_ofList]
  rfl

theorem rational181_decoded :
    parseRational (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0']) = .ok rational181 := by
  rw [parseRational_ofList]
  rfl

theorem rational182_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational182 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational106_decoded

theorem rational183_decoded :
    parseRational (String.ofList ['1', '1', '1', '9', '8', '5', '0', '2', '0', '3', '5', '7', '6', '1', '1', '/', '1', '6', '5', '7', '7', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational183 := by
  rw [parseRational_ofList]
  rfl

theorem rational184_decoded :
    parseRational (String.ofList ['1', '1', '4', '7', '8', '3', '5', '5', '5', '1', '6', '6', '9', '6', '1', '/', '1', '6', '5', '7', '7', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational184 := by
  rw [parseRational_ofList]
  rfl

theorem rational185_decoded :
    parseRational (String.ofList ['8', '2', '8', '1', '7', '3', '0', '7', '3', '7', '2', '1', '3', '6', '9', '/', '4', '9', '7', '3', '3', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational185 := by
  rw [parseRational_ofList]
  rfl

theorem rational186_decoded :
    parseRational (String.ofList ['1', '1', '5', '0', '8', '0', '0', '9', '3', '7', '7', '6', '8', '6', '7', '/', '9', '9', '4', '6', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational186 := by
  rw [parseRational_ofList]
  rfl

theorem rational187_decoded :
    parseRational (String.ofList ['8', '0', '7', '3', '6', '9', '7', '6', '8', '3', '5', '0', '2', '3', '/', '9', '9', '4', '6', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational187 := by
  rw [parseRational_ofList]
  rfl

theorem rational188_decoded :
    parseRational (String.ofList ['1', '8', '8', '9', '2', '0', '9', '4', '8', '2', '1', '7', '5', '7', '/', '4', '9', '7', '3', '3', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational188 := by
  rw [parseRational_ofList]
  rfl

theorem rational189_decoded :
    parseRational (String.ofList ['7', '1', '0', '7', '2', '9', '1', '5', '7', '5', '0', '3', '/', '2', '0', '7', '2', '2', '2', '7', '5', '0', '0', '0', '0', '0', '0']) = .ok rational189 := by
  rw [parseRational_ofList]
  rfl

theorem rational190_decoded :
    parseRational (String.ofList ['3', '2', '2', '8', '0', '4', '0', '4', '5', '1', '8', '4', '5', '9', '/', '9', '9', '4', '6', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational190 := by
  rw [parseRational_ofList]
  rfl

theorem rational191_decoded :
    parseRational (String.ofList ['1', '5', '9', '8', '4', '8', '2', '1', '0', '0', '4', '8', '2', '0', '7', '/', '4', '9', '7', '3', '3', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational191 := by
  rw [parseRational_ofList]
  rfl

theorem rational192_decoded :
    parseRational (String.ofList ['1', '3', '6', '7', '9', '8', '5', '8', '5', '1', '4', '8', '3', '8', '1', '/', '4', '9', '7', '3', '3', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational192 := by
  rw [parseRational_ofList]
  rfl

theorem rational193_decoded :
    parseRational (String.ofList ['1', '7', '7', '2', '6', '1', '5', '5', '5', '6', '6', '7', '2', '1', '7', '0', '4', '9', '9', '4', '3', '4', '8', '6', '4', '8', '1', '0', '4', '8', '7', '2', '9', '0', '6', '5', '8', '2', '3', '8', '0', '4', '9', '7', '2', '1', '3', '2', '0', '8', '9', '0', '9', '5', '3', '1', '2', '5', '0', '/', '4', '4', '3', '8', '7', '5', '0', '6', '5', '7', '1', '7', '2', '6', '6', '2', '9', '9', '1', '5', '4', '6', '2', '4', '2', '6', '5', '3', '1', '0', '3', '0', '0', '9', '0', '5', '4', '0', '3', '7', '7', '3', '7', '5', '3', '8', '7', '5', '0', '0', '5', '4', '7', '4', '4', '7', '8', '5', '6', '9', '8', '1', '0', '6', '3', '3', '6', '0', '2', '2', '9', '0', '1']) = .ok rational193 := by
  rw [parseRational_ofList]
  rfl

theorem rational194_decoded :
    parseRational (String.ofList ['3', '8', '8', '3', '7', '9', '0', '2', '0', '7', '4', '7', '8', '0', '7', '9', '9', '6', '8', '9', '5', '7', '1', '5', '1', '2', '2', '1', '2', '8', '2', '7', '9', '2', '7', '2', '1', '1', '2', '1', '1', '9', '9', '9', '5', '1', '8', '3', '9', '9', '4', '4', '4', '4', '0', '5', '7', '0', '2', '2', '6', '3', '4', '0', '3', '6', '6', '9', '6', '9', '0', '9', '2', '6', '2', '4', '1', '9', '6', '0', '4', '6', '6', '0', '7', '4', '1', '6', '9', '0', '1', '0', '7', '0', '6', '2', '4', '9', '3', '3', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '3', '7', '4', '4', '5', '4', '4', '4', '2', '4', '4', '8', '9', '4', '4', '0', '1', '2', '2', '1', '2', '5', '3', '8', '1', '0', '0', '8', '9', '0', '0', '9', '3', '4', '2', '1', '7', '8', '9', '9', '8', '5', '5', '1', '6', '5', '2', '7', '7', '6', '8', '5', '3', '3', '2', '8', '1', '1', '4', '3', '2', '1', '6', '8', '6', '8', '2', '8', '5', '2', '9', '4', '3', '0', '8', '3', '6', '6', '8', '1', '3', '4', '8', '8', '7', '9', '6', '0', '2', '6', '2', '7', '9', '5', '2', '8', '4', '7', '7', '2', '2', '5', '9', '3', '2', '9', '2', '3', '5', '6', '4', '1', '7', '0', '5', '6', '9', '4', '1', '1', '0', '3', '7', '8', '6', '1', '1', '5', '0', '9', '3', '3', '9', '5', '3', '1', '7']) = .ok rational194 := by
  rw [parseRational_ofList]
  rfl

theorem rational195_decoded :
    parseRational (String.ofList ['2', '7', '0', '1', '2', '5', '2', '5', '3', '9', '8', '6', '3', '2', '9', '7', '0', '6', '6', '3', '6', '1', '0', '0', '3', '9', '8', '1', '8', '5', '6', '9', '3', '2', '6', '3', '5', '8', '6', '0', '7', '7', '3', '7', '6', '4', '2', '4', '4', '6', '3', '1', '/', '5', '9', '0', '5', '3', '2', '3', '4', '5', '5', '7', '5', '6', '3', '0', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational195 := by
  rw [parseRational_ofList]
  rfl

theorem rational196_decoded :
    parseRational (String.ofList ['3', '0', '5', '6', '3', '8', '4', '2', '8', '5', '3', '3', '5', '8', '4', '0', '3', '/', '4', '3', '5', '9', '9', '6', '6', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational196 := by
  rw [parseRational_ofList]
  rfl

theorem rational197_decoded :
    parseRational (String.ofList ['3', '1', '2', '9', '9', '8', '5', '7', '5', '0', '8', '2', '1', '7', '4', '5', '3', '/', '4', '3', '5', '9', '9', '6', '6', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational197 := by
  rw [parseRational_ofList]
  rfl

theorem rational198_decoded :
    parseRational (String.ofList ['2', '1', '8', '6', '0', '2', '0', '5', '5', '4', '8', '9', '3', '7', '4', '3', '6', '7', '/', '1', '3', '0', '7', '9', '8', '9', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational198 := by
  rw [parseRational_ofList]
  rfl

theorem rational199_decoded :
    parseRational (String.ofList ['3', '0', '2', '5', '2', '8', '5', '5', '7', '1', '1', '6', '3', '8', '4', '4', '9', '/', '2', '6', '1', '5', '9', '7', '9', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational199 := by
  rw [parseRational_ofList]
  rfl

theorem rational200_decoded :
    parseRational (String.ofList ['2', '1', '3', '1', '3', '0', '7', '8', '6', '1', '7', '6', '7', '6', '4', '8', '1', '/', '2', '6', '1', '5', '9', '7', '9', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational200 := by
  rw [parseRational_ofList]
  rfl

theorem rational201_decoded :
    parseRational (String.ofList ['4', '9', '2', '2', '3', '8', '9', '6', '0', '7', '2', '5', '0', '5', '8', '9', '/', '1', '3', '0', '7', '9', '8', '9', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational201 := by
  rw [parseRational_ofList]
  rfl

theorem rational202_decoded :
    parseRational (String.ofList ['7', '3', '9', '9', '8', '1', '8', '5', '1', '8', '8', '1', '2', '3', '9', '/', '2', '1', '7', '9', '9', '8', '3', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational202 := by
  rw [parseRational_ofList]
  rfl

theorem rational203_decoded :
    parseRational (String.ofList ['8', '3', '9', '7', '2', '8', '3', '7', '2', '6', '6', '1', '1', '7', '1', '3', '/', '2', '6', '1', '5', '9', '7', '9', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational203 := by
  rw [parseRational_ofList]
  rfl

theorem rational204_decoded :
    parseRational (String.ofList ['4', '0', '2', '5', '6', '7', '8', '3', '5', '6', '6', '8', '7', '3', '0', '2', '1', '/', '1', '3', '0', '7', '9', '8', '9', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational204 := by
  rw [parseRational_ofList]
  rfl

theorem rational205_decoded :
    parseRational (String.ofList ['3', '4', '1', '9', '4', '8', '1', '9', '4', '1', '7', '5', '5', '1', '9', '8', '3', '/', '1', '3', '0', '7', '9', '8', '9', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational205 := by
  rw [parseRational_ofList]
  rfl

theorem rational206_decoded :
    parseRational (String.ofList ['2', '3', '5', '4', '1', '1', '9', '7', '2', '5', '2', '2', '8', '1', '1', '8', '8', '7', '4', '7', '7', '2', '9', '8', '4', '1', '1', '0', '8', '1', '2', '3', '3', '8', '6', '3', '7', '6', '0', '4', '1', '4', '2', '8', '3', '7', '4', '0', '1', '5', '4', '1', '5', '6', '1', '5', '1', '7', '8', '4', '3', '7', '5', '0', '0', '/', '3', '8', '9', '1', '2', '3', '8', '3', '2', '9', '6', '0', '0', '2', '5', '8', '5', '4', '0', '2', '0', '4', '1', '8', '2', '7', '6', '4', '2', '6', '6', '9', '6', '6', '4', '9', '2', '4', '1', '5', '8', '9', '3', '8', '9', '7', '9', '0', '6', '1', '4', '3', '8', '4', '9', '7', '6', '0', '0', '5', '5', '2', '4', '3', '3', '5', '0', '7', '3', '9', '3', '9', '4', '6', '1']) = .ok rational206 := by
  rw [parseRational_ofList]
  rfl

theorem rational207_decoded :
    parseRational (String.ofList ['8', '6', '6', '5', '3', '1', '3', '4', '9', '2', '1', '7', '1', '1', '7', '8', '2', '1', '5', '4', '4', '1', '8', '3', '4', '5', '4', '3', '1', '1', '2', '0', '4', '1', '7', '3', '1', '4', '1', '0', '9', '2', '2', '1', '2', '5', '4', '2', '4', '7', '5', '9', '1', '2', '4', '2', '1', '1', '9', '3', '6', '1', '9', '3', '6', '0', '3', '9', '2', '0', '0', '3', '4', '2', '5', '8', '3', '4', '5', '6', '6', '9', '3', '7', '1', '6', '5', '2', '9', '5', '2', '9', '1', '0', '8', '1', '2', '6', '5', '9', '1', '5', '4', '3', '8', '1', '0', '7', '7', '0', '0', '9', '8', '7', '8', '1', '1', '6', '6', '5', '1', '6', '2', '0', '4', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '2', '0', '3', '3', '4', '3', '9', '1', '2', '6', '4', '2', '4', '6', '8', '3', '7', '5', '3', '0', '3', '4', '2', '4', '5', '0', '1', '3', '6', '8', '2', '2', '8', '0', '8', '5', '9', '7', '7', '0', '0', '8', '1', '3', '7', '2', '8', '6', '8', '3', '9', '2', '7', '6', '0', '4', '5', '5', '7', '3', '8', '2', '4', '5', '4', '0', '5', '7', '9', '9', '5', '2', '0', '6', '4', '6', '1', '3', '0', '7', '2', '1', '6', '6', '0', '5', '7', '9', '0', '1', '7', '5', '5', '8', '0', '5', '4', '3', '5', '5', '5', '2', '4', '1', '9', '9', '7', '6', '0', '9', '0', '6', '8', '1', '9', '7', '1', '4', '3', '6', '8', '7', '7', '4', '3', '1', '5', '5', '7', '2', '4', '4', '2', '8', '3', '4', '2', '4', '3', '1', '9', '6', '8', '1', '5', '3', '1', '0', '9', '3', '4', '3', '4', '9', '3', '5', '8', '0', '1', '1']) = .ok rational207 := by
  rw [parseRational_ofList]
  rfl

theorem rational208_decoded :
    parseRational (String.ofList ['9', '7', '2', '7', '0', '9', '2', '9', '3', '6', '1', '9', '5', '9', '5', '5', '5', '7', '9', '6', '5', '3', '2', '3', '5', '9', '4', '1', '1', '1', '0', '4', '6', '4', '0', '5', '5', '1', '2', '3', '4', '5', '9', '/', '6', '0', '4', '1', '3', '5', '4', '6', '2', '4', '0', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational208 := by
  rw [parseRational_ofList]
  rfl

theorem rational209_decoded :
    parseRational (String.ofList ['5', '0', '8', '0', '3', '0', '1', '5', '1', '2', '0', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational209 := by
  rw [parseRational_ofList]
  rfl

theorem rational210_decoded :
    parseRational (String.ofList ['5', '2', '0', '5', '7', '9', '6', '3', '4', '6', '5', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational210 := by
  rw [parseRational_ofList]
  rfl

theorem rational211_decoded :
    parseRational (String.ofList ['3', '7', '1', '2', '3', '6', '1', '5', '1', '1', '5', '5', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational211 := by
  rw [parseRational_ofList]
  rfl

theorem rational212_decoded :
    parseRational (String.ofList ['5', '0', '7', '6', '0', '8', '9', '3', '7', '6', '5', '9', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational212 := by
  rw [parseRational_ofList]
  rfl

theorem rational213_decoded :
    parseRational (String.ofList ['3', '6', '9', '1', '6', '6', '4', '1', '1', '2', '3', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational213 := by
  rw [parseRational_ofList]
  rfl

theorem rational214_decoded :
    parseRational (String.ofList ['5', '2', '6', '2', '2', '3', '5', '5', '8', '9', '/', '1', '3', '9', '3', '8', '7', '5', '0', '0', '0', '0', '0']) = .ok rational214 := by
  rw [parseRational_ofList]
  rfl

theorem rational215_decoded :
    parseRational (String.ofList ['2', '5', '3', '2', '2', '9', '6', '1', '9', '4', '3', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational215 := by
  rw [parseRational_ofList]
  rfl

theorem rational216_decoded :
    parseRational (String.ofList ['1', '4', '3', '7', '1', '0', '8', '8', '8', '0', '6', '3', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational216 := by
  rw [parseRational_ofList]
  rfl

theorem rational217_decoded :
    parseRational (String.ofList ['7', '1', '1', '5', '8', '6', '6', '7', '1', '0', '5', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational217 := by
  rw [parseRational_ofList]
  rfl

theorem rational218_decoded :
    parseRational (String.ofList ['6', '3', '4', '7', '8', '7', '2', '5', '9', '7', '9', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational218 := by
  rw [parseRational_ofList]
  rfl

theorem rational219_decoded :
    parseRational (String.ofList ['1', '7', '8', '0', '8', '9', '9', '7', '4', '0', '5', '9', '5', '8', '6', '6', '1', '6', '6', '3', '1', '3', '5', '1', '3', '0', '8', '9', '1', '3', '8', '5', '2', '3', '3', '3', '2', '1', '8', '9', '4', '2', '1', '9', '2', '5', '0', '0', '0', '7', '8', '1', '2', '5', '/', '8', '5', '3', '3', '9', '8', '3', '7', '2', '0', '8', '3', '0', '3', '0', '6', '0', '3', '6', '6', '5', '7', '5', '1', '2', '6', '4', '8', '5', '8', '8', '6', '5', '1', '3', '0', '7', '2', '8', '2', '0', '3', '2', '2', '1', '5', '7', '9', '5', '0', '3', '2', '8', '2', '1', '1', '9', '9', '6', '6', '0', '0', '8', '4', '3', '9', '0', '7']) = .ok rational219 := by
  rw [parseRational_ofList]
  rfl

theorem rational220_decoded :
    parseRational (String.ofList ['3', '4', '0', '4', '7', '3', '9', '3', '5', '3', '9', '6', '4', '4', '7', '3', '2', '5', '5', '9', '2', '0', '4', '5', '5', '1', '2', '3', '6', '5', '6', '4', '5', '1', '3', '2', '2', '5', '3', '6', '4', '9', '7', '1', '0', '2', '3', '0', '4', '1', '3', '6', '3', '9', '0', '3', '3', '5', '5', '3', '3', '2', '5', '0', '3', '1', '8', '4', '0', '5', '9', '6', '2', '3', '3', '1', '4', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '9', '1', '5', '0', '8', '0', '2', '5', '8', '1', '0', '0', '5', '0', '8', '1', '2', '1', '2', '9', '5', '4', '6', '4', '8', '6', '2', '5', '0', '2', '2', '9', '2', '7', '9', '2', '4', '3', '4', '2', '7', '4', '7', '2', '0', '3', '3', '8', '1', '0', '1', '0', '8', '1', '0', '6', '4', '2', '7', '2', '0', '0', '6', '9', '8', '0', '3', '1', '1', '0', '4', '2', '1', '3', '3', '2', '4', '4', '4', '5', '1', '9', '8', '1', '2', '0', '5', '9', '6', '2', '6', '1', '1', '1', '0', '5', '7', '4', '0', '6', '8', '9', '2', '6', '4', '9', '0', '4', '6', '9', '4', '4', '9']) = .ok rational220 := by
  rw [parseRational_ofList]
  rfl

theorem rational221_decoded :
    parseRational (String.ofList ['5', '2', '7', '3', '8', '8', '2', '3', '7', '6', '4', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational221 := by
  rw [parseRational_ofList]
  rfl

theorem rational222_decoded :
    parseRational (String.ofList ['5', '3', '9', '9', '3', '7', '7', '2', '1', '0', '9', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational222 := by
  rw [parseRational_ofList]
  rfl

theorem rational223_decoded :
    parseRational (String.ofList ['3', '7', '2', '6', '8', '7', '9', '7', '0', '4', '6', '8', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational223 := by
  rw [parseRational_ofList]
  rfl

theorem rational224_decoded :
    parseRational (String.ofList ['4', '9', '8', '8', '9', '8', '0', '2', '1', '7', '8', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational224 := by
  rw [parseRational_ofList]
  rfl

theorem rational225_decoded :
    parseRational (String.ofList ['3', '7', '7', '8', '7', '7', '3', '2', '7', '1', '0', '9', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational225 := by
  rw [parseRational_ofList]
  rfl

theorem rational226_decoded :
    parseRational (String.ofList ['8', '2', '7', '4', '3', '9', '5', '0', '1', '1', '1', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational226 := by
  rw [parseRational_ofList]
  rfl

theorem rational227_decoded :
    parseRational (String.ofList ['6', '2', '0', '9', '7', '5', '5', '5', '4', '3', '/', '1', '8', '5', '8', '5', '0', '0', '0', '0', '0', '0', '0']) = .ok rational227 := by
  rw [parseRational_ofList]
  rfl

theorem rational228_decoded :
    parseRational (String.ofList ['1', '4', '0', '8', '0', '7', '2', '4', '9', '4', '3', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational228 := by
  rw [parseRational_ofList]
  rfl

theorem rational229_decoded :
    parseRational (String.ofList ['6', '9', '7', '0', '6', '6', '9', '9', '1', '1', '2', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational229 := by
  rw [parseRational_ofList]
  rfl

theorem rational230_decoded :
    parseRational (String.ofList ['6', '2', '0', '2', '6', '9', '0', '6', '6', '6', '6', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational230 := by
  rw [parseRational_ofList]
  rfl

theorem rational231_decoded :
    parseRational (String.ofList ['1', '7', '8', '0', '8', '9', '9', '7', '4', '0', '5', '9', '5', '8', '6', '6', '1', '6', '6', '3', '1', '3', '5', '1', '3', '0', '8', '9', '1', '3', '8', '5', '2', '3', '3', '3', '2', '1', '8', '9', '4', '2', '1', '9', '2', '5', '0', '0', '0', '7', '8', '1', '2', '5', '/', '8', '5', '3', '3', '8', '3', '8', '0', '7', '0', '6', '9', '4', '7', '3', '6', '6', '2', '6', '8', '9', '6', '0', '5', '6', '4', '5', '9', '9', '7', '9', '5', '8', '2', '2', '2', '8', '2', '7', '5', '8', '6', '0', '2', '1', '4', '9', '7', '5', '5', '4', '3', '6', '7', '2', '3', '1', '2', '1', '1', '4', '1', '9', '0', '4', '2', '8', '7']) = .ok rational231 := by
  rw [parseRational_ofList]
  rfl

theorem rational232_decoded :
    parseRational (String.ofList ['8', '0', '1', '1', '1', '5', '1', '4', '2', '1', '0', '9', '2', '8', '7', '8', '2', '4', '9', '2', '2', '4', '6', '0', '0', '2', '9', '0', '9', '5', '6', '3', '5', '6', '0', '5', '3', '0', '2', '7', '0', '5', '2', '0', '0', '5', '4', '2', '1', '4', '9', '7', '3', '8', '9', '0', '2', '4', '7', '8', '4', '1', '1', '8', '3', '9', '6', '2', '4', '9', '3', '2', '3', '1', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '8', '1', '4', '8', '9', '6', '8', '6', '7', '7', '5', '2', '0', '9', '3', '9', '9', '4', '5', '0', '1', '7', '3', '6', '2', '2', '7', '9', '8', '7', '5', '6', '4', '1', '3', '7', '9', '4', '8', '4', '9', '9', '5', '9', '6', '6', '9', '0', '6', '7', '5', '2', '3', '4', '1', '8', '2', '8', '0', '5', '4', '3', '8', '2', '5', '9', '3', '3', '7', '0', '9', '9', '6', '0', '9', '1', '5', '7', '1', '5', '4', '8', '0', '2', '7', '9', '9', '5', '5', '7', '5', '1', '8', '9', '6', '3', '2', '4', '7', '7', '6', '5', '2', '8', '8', '7', '6', '1', '9', '2', '2', '7']) = .ok rational232 := by
  rw [parseRational_ofList]
  rfl

theorem rational233_decoded :
    parseRational (String.ofList ['7', '5', '8', '3', '1', '6', '0', '6', '8', '2', '9', '8', '0', '2', '7', '4', '7', '9', '1', '8', '6', '3', '4', '0', '8', '1', '6', '5', '2', '8', '0', '8', '7', '0', '9', '1', '4', '5', '4', '1', '8', '0', '7', '1', '/', '3', '6', '3', '1', '7', '1', '7', '1', '7', '9', '7', '0', '9', '1', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational233 := by
  rw [parseRational_ofList]
  rfl

theorem rational234_decoded :
    parseRational (String.ofList ['1', '3', '9', '9', '2', '1', '2', '1', '4', '1', '1', '1', '4', '6', '1', '/', '1', '9', '5', '5', '1', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational234 := by
  rw [parseRational_ofList]
  rfl

theorem rational235_decoded :
    parseRational (String.ofList ['1', '4', '3', '2', '2', '1', '7', '2', '8', '2', '5', '8', '8', '1', '1', '/', '1', '9', '5', '5', '1', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational235 := by
  rw [parseRational_ofList]
  rfl

theorem rational236_decoded :
    parseRational (String.ofList ['9', '8', '0', '8', '2', '1', '3', '8', '1', '7', '4', '5', '1', '2', '9', '/', '5', '8', '6', '5', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational236 := by
  rw [parseRational_ofList]
  rfl

theorem rational237_decoded :
    parseRational (String.ofList ['1', '3', '3', '7', '4', '7', '3', '5', '9', '6', '9', '6', '1', '0', '3', '/', '1', '1', '7', '3', '0', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational237 := by
  rw [parseRational_ofList]
  rfl

theorem rational238_decoded :
    parseRational (String.ofList ['9', '7', '2', '6', '2', '8', '9', '8', '7', '2', '1', '3', '6', '7', '/', '1', '1', '7', '3', '0', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational238 := by
  rw [parseRational_ofList]
  rfl

theorem rational239_decoded :
    parseRational (String.ofList ['2', '1', '9', '0', '5', '6', '2', '7', '7', '6', '7', '5', '4', '3', '/', '5', '8', '6', '5', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational239 := by
  rw [parseRational_ofList]
  rfl

theorem rational240_decoded :
    parseRational (String.ofList ['3', '2', '9', '0', '3', '2', '6', '2', '3', '0', '3', '4', '3', '/', '9', '7', '7', '5', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational240 := by
  rw [parseRational_ofList]
  rfl

theorem rational241_decoded :
    parseRational (String.ofList ['3', '7', '3', '2', '0', '2', '4', '4', '3', '7', '8', '6', '3', '1', '/', '1', '1', '7', '3', '0', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational241 := by
  rw [parseRational_ofList]
  rfl

theorem rational242_decoded :
    parseRational (String.ofList ['1', '7', '6', '4', '0', '1', '0', '8', '3', '3', '3', '4', '0', '2', '7', '/', '5', '8', '6', '5', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational242 := by
  rw [parseRational_ofList]
  rfl

theorem rational243_decoded :
    parseRational (String.ofList ['1', '5', '6', '2', '0', '3', '6', '2', '0', '2', '2', '8', '9', '2', '1', '/', '5', '8', '6', '5', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational243 := by
  rw [parseRational_ofList]
  rfl

theorem rational244_decoded :
    parseRational (String.ofList ['1', '8', '0', '7', '0', '5', '6', '3', '3', '2', '5', '4', '1', '9', '4', '2', '2', '3', '6', '9', '7', '5', '3', '5', '3', '3', '2', '0', '3', '5', '4', '5', '7', '3', '7', '8', '2', '0', '2', '4', '2', '0', '0', '8', '6', '7', '3', '5', '5', '1', '3', '6', '3', '5', '2', '5', '3', '9', '0', '6', '2', '5', '/', '6', '5', '7', '0', '2', '7', '0', '8', '3', '9', '9', '5', '9', '5', '3', '8', '3', '0', '3', '7', '1', '7', '5', '2', '5', '9', '9', '4', '1', '0', '5', '7', '3', '8', '5', '0', '1', '3', '7', '2', '5', '3', '4', '4', '6', '1', '4', '7', '3', '2', '3', '6', '9', '7', '4', '4', '2', '9', '1', '4', '3', '2', '3', '3', '1', '1', '6', '0', '8', '2', '8', '7']) = .ok rational244 := by
  rw [parseRational_ofList]
  rfl

theorem rational245_decoded :
    parseRational (String.ofList ['5', '5', '9', '2', '6', '9', '1', '2', '5', '3', '2', '3', '5', '2', '5', '6', '3', '4', '1', '8', '8', '9', '7', '8', '6', '1', '7', '6', '3', '0', '6', '0', '3', '3', '5', '1', '0', '7', '1', '0', '3', '4', '0', '3', '4', '4', '3', '9', '3', '6', '2', '4', '2', '8', '6', '7', '6', '6', '0', '4', '7', '0', '3', '5', '1', '1', '5', '5', '5', '3', '0', '6', '0', '0', '1', '3', '4', '4', '6', '9', '4', '6', '0', '5', '1', '3', '8', '8', '8', '4', '6', '1', '5', '6', '8', '6', '9', '8', '5', '6', '4', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '9', '5', '1', '6', '1', '8', '7', '4', '6', '1', '1', '6', '1', '6', '7', '7', '3', '1', '2', '1', '6', '5', '5', '4', '7', '2', '4', '1', '1', '5', '1', '6', '1', '7', '9', '8', '9', '6', '8', '4', '1', '6', '7', '0', '8', '1', '8', '0', '6', '5', '7', '5', '8', '5', '3', '2', '3', '3', '9', '2', '6', '8', '6', '1', '2', '6', '9', '9', '0', '4', '9', '9', '8', '2', '8', '3', '8', '5', '5', '6', '6', '3', '4', '1', '8', '3', '1', '3', '7', '6', '4', '3', '6', '8', '4', '0', '5', '1', '4', '4', '8', '4', '5', '2', '2', '2', '2', '7', '6', '5', '5', '3', '8', '9', '7', '8', '9', '1', '2', '2', '4', '9', '4', '2', '0', '6', '1', '3', '4', '7', '0', '8', '7', '1', '5', '7', '0', '7']) = .ok rational245 := by
  rw [parseRational_ofList]
  rfl

theorem rational246_decoded :
    parseRational (String.ofList ['1', '2', '9', '6', '9', '0', '4', '2', '1', '7', '2', '4', '9', '9', '6', '3', '2', '2', '5', '5', '2', '7', '5', '9', '9', '7', '2', '2', '5', '4', '5', '8', '0', '4', '0', '4', '7', '0', '3', '4', '6', '3', '9', '/', '1', '2', '8', '8', '8', '2', '2', '3', '1', '9', '7', '9', '5', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational246 := by
  rw [parseRational_ofList]
  rfl

theorem rational247_decoded :
    parseRational (String.ofList ['5', '3', '2', '4', '2', '1', '3', '6', '5', '3', '9', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational247 := by
  rw [parseRational_ofList]
  rfl

theorem rational248_decoded :
    parseRational (String.ofList ['5', '4', '4', '9', '7', '0', '8', '4', '8', '8', '4', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational248 := by
  rw [parseRational_ofList]
  rfl

theorem rational249_decoded :
    parseRational (String.ofList ['3', '7', '3', '0', '3', '6', '3', '8', '3', '4', '6', '3', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational249 := by
  rw [parseRational_ofList]
  rfl

theorem rational250_decoded :
    parseRational (String.ofList ['5', '0', '0', '0', '5', '9', '3', '9', '8', '4', '3', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational250 := by
  rw [parseRational_ofList]
  rfl

theorem rational251_decoded :
    parseRational (String.ofList ['3', '7', '7', '1', '8', '0', '5', '0', '1', '1', '1', '9', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational251 := by
  rw [parseRational_ofList]
  rfl

theorem rational252_decoded :
    parseRational (String.ofList ['4', '1', '3', '1', '3', '9', '0', '6', '2', '2', '3', '/', '1', '1', '1', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational252 := by
  rw [parseRational_ofList]
  rfl

theorem rational253_decoded :
    parseRational (String.ofList ['2', '4', '8', '0', '0', '3', '0', '9', '6', '1', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational253 := by
  rw [parseRational_ofList]
  rfl

theorem rational254_decoded :
    parseRational (String.ofList ['1', '4', '0', '5', '7', '4', '9', '7', '4', '1', '0', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational254 := by
  rw [parseRational_ofList]
  rfl

theorem rational255_decoded :
    parseRational (String.ofList ['6', '8', '6', '6', '1', '3', '1', '1', '4', '4', '7', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational255 := by
  rw [parseRational_ofList]
  rfl

end ImbalancedChen.P2Saving16Cell01ScalarDecode
