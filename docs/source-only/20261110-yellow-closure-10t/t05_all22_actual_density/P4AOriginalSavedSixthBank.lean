import ImbalancedChen.P4AOriginalSavedSixthCornerIntegral
import Std.Data.HashMap.Basic

/-! Rational finite predicates and the archived Q80 integer floors of
the original grid-400 sixth bank. The three saved columns are the sum
of the 64 scaled gaps and the two scaled residual bounds. -/
namespace ImbalancedChen.P4AOriginalSavedSixthBank
noncomputable section
open scoped BigOperators
open P4AOriginalSavedSixthArchive (Row)
open P4AOriginalSavedSixthWordAccess (word)
open P4AOriginalSavedSixthPlanes

def unit := (102400 : ℚ)
def lo (i : Row) (k : Fin 6) : ℤ := word i ⟨k.val+1,by omega⟩
def ds (i : Row) : ℚ := word i 8
def oldResidual (i : Row) : ℚ := (word i 9 : ℚ)/unit
def newResidual (i : Row) : ℚ := (word i 10 : ℚ)/unit
def budgetQ (i : Row) : ℚ :=
  unit*ds i/(16*(word i 9:ℚ)*(word i 10:ℚ)*∏ j,((lo i j:ℚ)+1))
def floor80 (i : Row) : ℤ := ⌊(2^80:ℚ)*budgetQ i⌋

def h3 : Plane := ((coord 0).plus (coord 1)).plus ((coord 2).scale 3)
def h5 : Plane := (((((coord 0).plus (coord 1)).plus (coord 2)).plus (coord 3)).plus ((coord 4).scale 3))
def thirdMask (j : Fin 6) : ℕ := ![0,1,3,7,5,6] j
def thirdFace (j : Fin 6) (b : Bool) : Plane :=
  if j.val=0 then rescue else tentPlane 5 (thirdMask j) b

def prefix (j : Fin 6) : Plane := ⟨0,fun k => if k<j then 1 else 0⟩
def prefixUnmarked (m : ℕ) (j : Fin 6) : Plane :=
  ⟨0,fun k => if k<j ∧ k ∉ slots 6 m then 1 else 0⟩
def full (j : Fin 6) : Plane := (prefix j).plus ((coord j).scale 2)
def remaining (m : ℕ) (j : Fin 6) : Plane :=
  ((selected 6 m).plus (prefixUnmarked m j)).plus ((coord j).scale 2)

def above (i : Row) (p q : Plane) (d : ℚ) : Prop :=
  d ≤ lowerBound (p.sub q) (lowerQ i) (upperQ i)
def below (i : Row) (p : Plane) (d : ℚ) : Prop :=
  upperBound p (lowerQ i) (upperQ i) ≤ d

instance (i : Row) (p q : Plane) (d : ℚ) : Decidable (above i p q d) := by
  unfold above; infer_instance
instance (i : Row) (p : Plane) (d : ℚ) : Decidable (below i p d) := by
  unfold below; infer_instance

structure Facts (i : Row) : Prop where
  grid : word i 0=400
  left : ∀ j, 8 ≤ lo i j
  right : lo i 0+1 ≤ 78
  order : ∀ j : Fin 5, lo i j.succ+1 ≤ lo i j.castSucc
  mask : 32 ≤ chosenMask i ∧ chosenMask i < 64
  third : ∃ j : Fin 6, ∀ b : Bool, above i (thirdFace j b) h3 (1/1600)
  fifth : ∃ j : Fin 6, ∀ b : Bool, above i (thirdFace j b) h5 (1/1600)
  half : ∀ b : Bool, above i (newFace i b) (constant (1/2)) (1/1600)
  fullGate : ∀ b : Bool, ∀ j : Fin 6, above i (newFace i b) (full j) (1/1600)
  remainingGate : ∀ b : Bool, ∀ j : Fin 6, j ∉ slots 6 (chosenMask i) →
    above i (newFace i b) (remaining (chosenMask i) j) (1/1600)
  cube : ∃ b : Bool, below i (((newFace i b).sub total).sub ((coord 5).scale 3)) 0
  gapSum : ds i = unit * ∑ b : Corner, gapQ i (vertexQ i b)
  oldBound : (∀ m : Fin 32, below i ((oldFace i m).sub total) (oldResidual i)) ∨
    ∃ b : Bool, below i ((newFace i b).sub total) (oldResidual i)
  newBound : ∃ b : Bool, below i ((newFace i b).sub total) (newResidual i)
  oldPos : 0 < word i 9
  newPos : 0 < word i 10

instance (i : Row) : Decidable (Facts i) := by
  apply decidable_of_iff
    (word i 0=400 ∧ (∀ j,8 ≤ lo i j) ∧ lo i 0+1 ≤ 78 ∧
    (∀ j : Fin 5,lo i j.succ+1 ≤ lo i j.castSucc) ∧
    (32 ≤ chosenMask i ∧ chosenMask i < 64) ∧
    (∃ j : Fin 6,∀ b : Bool,above i (thirdFace j b) h3 (1/1600)) ∧
    (∃ j : Fin 6,∀ b : Bool,above i (thirdFace j b) h5 (1/1600)) ∧
    (∀ b : Bool,above i (newFace i b) (constant (1/2)) (1/1600)) ∧
    (∀ b : Bool,∀ j : Fin 6,above i (newFace i b) (full j) (1/1600)) ∧
    (∀ b : Bool,∀ j : Fin 6,j ∉ slots 6 (chosenMask i) → above i (newFace i b) (remaining (chosenMask i) j) (1/1600)) ∧
    (∃ b : Bool,below i (((newFace i b).sub total).sub ((coord 5).scale 3)) 0) ∧
    (ds i = unit*(∑ b : Corner,gapQ i (vertexQ i b))) ∧
    ((∀ m : Fin 32,below i ((oldFace i m).sub total) (oldResidual i)) ∨
      ∃ b : Bool,below i ((newFace i b).sub total) (oldResidual i)) ∧
    (∃ b : Bool,below i ((newFace i b).sub total) (newResidual i)) ∧
    0 < word i 9 ∧ 0 < word i 10)
  constructor
  · rintro ⟨a,b,c,d,e,f,g,h,k,l,m,n,p,q,r,s⟩; exact ⟨a,b,c,d,e,f,g,h,k,l,m,n,p,q,r,s⟩
  · rintro ⟨a,b,c,d,e,f,g,h,k,l,m,n,p,q,r,s⟩; exact ⟨a,b,c,d,e,f,g,h,k,l,m,n,p,q,r,s⟩

abbrev Block := Fin (632104/2048+1)
def index (b : Block) (k : Fin 2048) := 2048*b.val+k.val
def key (i : Row) : List ℤ := List.ofFn (lo i)
def owners : Std.HashMap (List ℤ) ℕ :=
  Std.HashMap.ofList (List.ofFn fun i : Row => (key i,i.val))
def checked (b : Block) : Prop :=
  ∀ k : Fin 2048, ∀ h : index b k<632104, Facts ⟨index b k,h⟩
instance (b : Block) : Decidable (checked b) := by unfold checked; infer_instance

/- The exact 55,625,280-byte input is shared with the actual policy.
Each finite reduction concerns at most 2048 original rows. -/
set_option maxRecDepth 8388608
set_option maxHeartbeats 0
theorem block000 : checked 0 := by decide
theorem block001 : checked 1 := by decide
theorem block002 : checked 2 := by decide
theorem block003 : checked 3 := by decide
theorem block004 : checked 4 := by decide
theorem block005 : checked 5 := by decide
theorem block006 : checked 6 := by decide
theorem block007 : checked 7 := by decide
theorem block008 : checked 8 := by decide
theorem block009 : checked 9 := by decide
theorem block010 : checked 10 := by decide
theorem block011 : checked 11 := by decide
theorem block012 : checked 12 := by decide
theorem block013 : checked 13 := by decide
theorem block014 : checked 14 := by decide
theorem block015 : checked 15 := by decide
theorem block016 : checked 16 := by decide
theorem block017 : checked 17 := by decide
theorem block018 : checked 18 := by decide
theorem block019 : checked 19 := by decide
theorem block020 : checked 20 := by decide
theorem block021 : checked 21 := by decide
theorem block022 : checked 22 := by decide
theorem block023 : checked 23 := by decide
theorem block024 : checked 24 := by decide
theorem block025 : checked 25 := by decide
theorem block026 : checked 26 := by decide
theorem block027 : checked 27 := by decide
theorem block028 : checked 28 := by decide
theorem block029 : checked 29 := by decide
theorem block030 : checked 30 := by decide
theorem block031 : checked 31 := by decide
theorem block032 : checked 32 := by decide
theorem block033 : checked 33 := by decide
theorem block034 : checked 34 := by decide
theorem block035 : checked 35 := by decide
theorem block036 : checked 36 := by decide
theorem block037 : checked 37 := by decide
theorem block038 : checked 38 := by decide
theorem block039 : checked 39 := by decide
theorem block040 : checked 40 := by decide
theorem block041 : checked 41 := by decide
theorem block042 : checked 42 := by decide
theorem block043 : checked 43 := by decide
theorem block044 : checked 44 := by decide
theorem block045 : checked 45 := by decide
theorem block046 : checked 46 := by decide
theorem block047 : checked 47 := by decide
theorem block048 : checked 48 := by decide
theorem block049 : checked 49 := by decide
theorem block050 : checked 50 := by decide
theorem block051 : checked 51 := by decide
theorem block052 : checked 52 := by decide
theorem block053 : checked 53 := by decide
theorem block054 : checked 54 := by decide
theorem block055 : checked 55 := by decide
theorem block056 : checked 56 := by decide
theorem block057 : checked 57 := by decide
theorem block058 : checked 58 := by decide
theorem block059 : checked 59 := by decide
theorem block060 : checked 60 := by decide
theorem block061 : checked 61 := by decide
theorem block062 : checked 62 := by decide
theorem block063 : checked 63 := by decide
theorem block064 : checked 64 := by decide
theorem block065 : checked 65 := by decide
theorem block066 : checked 66 := by decide
theorem block067 : checked 67 := by decide
theorem block068 : checked 68 := by decide
theorem block069 : checked 69 := by decide
theorem block070 : checked 70 := by decide
theorem block071 : checked 71 := by decide
theorem block072 : checked 72 := by decide
theorem block073 : checked 73 := by decide
theorem block074 : checked 74 := by decide
theorem block075 : checked 75 := by decide
theorem block076 : checked 76 := by decide
theorem block077 : checked 77 := by decide
theorem block078 : checked 78 := by decide
theorem block079 : checked 79 := by decide
theorem block080 : checked 80 := by decide
theorem block081 : checked 81 := by decide
theorem block082 : checked 82 := by decide
theorem block083 : checked 83 := by decide
theorem block084 : checked 84 := by decide
theorem block085 : checked 85 := by decide
theorem block086 : checked 86 := by decide
theorem block087 : checked 87 := by decide
theorem block088 : checked 88 := by decide
theorem block089 : checked 89 := by decide
theorem block090 : checked 90 := by decide
theorem block091 : checked 91 := by decide
theorem block092 : checked 92 := by decide
theorem block093 : checked 93 := by decide
theorem block094 : checked 94 := by decide
theorem block095 : checked 95 := by decide
theorem block096 : checked 96 := by decide
theorem block097 : checked 97 := by decide
theorem block098 : checked 98 := by decide
theorem block099 : checked 99 := by decide
theorem block100 : checked 100 := by decide
theorem block101 : checked 101 := by decide
theorem block102 : checked 102 := by decide
theorem block103 : checked 103 := by decide
theorem block104 : checked 104 := by decide
theorem block105 : checked 105 := by decide
theorem block106 : checked 106 := by decide
theorem block107 : checked 107 := by decide
theorem block108 : checked 108 := by decide
theorem block109 : checked 109 := by decide
theorem block110 : checked 110 := by decide
theorem block111 : checked 111 := by decide
theorem block112 : checked 112 := by decide
theorem block113 : checked 113 := by decide
theorem block114 : checked 114 := by decide
theorem block115 : checked 115 := by decide
theorem block116 : checked 116 := by decide
theorem block117 : checked 117 := by decide
theorem block118 : checked 118 := by decide
theorem block119 : checked 119 := by decide
theorem block120 : checked 120 := by decide
theorem block121 : checked 121 := by decide
theorem block122 : checked 122 := by decide
theorem block123 : checked 123 := by decide
theorem block124 : checked 124 := by decide
theorem block125 : checked 125 := by decide
theorem block126 : checked 126 := by decide
theorem block127 : checked 127 := by decide
theorem block128 : checked 128 := by decide
theorem block129 : checked 129 := by decide
theorem block130 : checked 130 := by decide
theorem block131 : checked 131 := by decide
theorem block132 : checked 132 := by decide
theorem block133 : checked 133 := by decide
theorem block134 : checked 134 := by decide
theorem block135 : checked 135 := by decide
theorem block136 : checked 136 := by decide
theorem block137 : checked 137 := by decide
theorem block138 : checked 138 := by decide
theorem block139 : checked 139 := by decide
theorem block140 : checked 140 := by decide
theorem block141 : checked 141 := by decide
theorem block142 : checked 142 := by decide
theorem block143 : checked 143 := by decide
theorem block144 : checked 144 := by decide
theorem block145 : checked 145 := by decide
theorem block146 : checked 146 := by decide
theorem block147 : checked 147 := by decide
theorem block148 : checked 148 := by decide
theorem block149 : checked 149 := by decide
theorem block150 : checked 150 := by decide
theorem block151 : checked 151 := by decide
theorem block152 : checked 152 := by decide
theorem block153 : checked 153 := by decide
theorem block154 : checked 154 := by decide
theorem block155 : checked 155 := by decide
theorem block156 : checked 156 := by decide
theorem block157 : checked 157 := by decide
theorem block158 : checked 158 := by decide
theorem block159 : checked 159 := by decide
theorem block160 : checked 160 := by decide
theorem block161 : checked 161 := by decide
theorem block162 : checked 162 := by decide
theorem block163 : checked 163 := by decide
theorem block164 : checked 164 := by decide
theorem block165 : checked 165 := by decide
theorem block166 : checked 166 := by decide
theorem block167 : checked 167 := by decide
theorem block168 : checked 168 := by decide
theorem block169 : checked 169 := by decide
theorem block170 : checked 170 := by decide
theorem block171 : checked 171 := by decide
theorem block172 : checked 172 := by decide
theorem block173 : checked 173 := by decide
theorem block174 : checked 174 := by decide
theorem block175 : checked 175 := by decide
theorem block176 : checked 176 := by decide
theorem block177 : checked 177 := by decide
theorem block178 : checked 178 := by decide
theorem block179 : checked 179 := by decide
theorem block180 : checked 180 := by decide
theorem block181 : checked 181 := by decide
theorem block182 : checked 182 := by decide
theorem block183 : checked 183 := by decide
theorem block184 : checked 184 := by decide
theorem block185 : checked 185 := by decide
theorem block186 : checked 186 := by decide
theorem block187 : checked 187 := by decide
theorem block188 : checked 188 := by decide
theorem block189 : checked 189 := by decide
theorem block190 : checked 190 := by decide
theorem block191 : checked 191 := by decide
theorem block192 : checked 192 := by decide
theorem block193 : checked 193 := by decide
theorem block194 : checked 194 := by decide
theorem block195 : checked 195 := by decide
theorem block196 : checked 196 := by decide
theorem block197 : checked 197 := by decide
theorem block198 : checked 198 := by decide
theorem block199 : checked 199 := by decide
theorem block200 : checked 200 := by decide
theorem block201 : checked 201 := by decide
theorem block202 : checked 202 := by decide
theorem block203 : checked 203 := by decide
theorem block204 : checked 204 := by decide
theorem block205 : checked 205 := by decide
theorem block206 : checked 206 := by decide
theorem block207 : checked 207 := by decide
theorem block208 : checked 208 := by decide
theorem block209 : checked 209 := by decide
theorem block210 : checked 210 := by decide
theorem block211 : checked 211 := by decide
theorem block212 : checked 212 := by decide
theorem block213 : checked 213 := by decide
theorem block214 : checked 214 := by decide
theorem block215 : checked 215 := by decide
theorem block216 : checked 216 := by decide
theorem block217 : checked 217 := by decide
theorem block218 : checked 218 := by decide
theorem block219 : checked 219 := by decide
theorem block220 : checked 220 := by decide
theorem block221 : checked 221 := by decide
theorem block222 : checked 222 := by decide
theorem block223 : checked 223 := by decide
theorem block224 : checked 224 := by decide
theorem block225 : checked 225 := by decide
theorem block226 : checked 226 := by decide
theorem block227 : checked 227 := by decide
theorem block228 : checked 228 := by decide
theorem block229 : checked 229 := by decide
theorem block230 : checked 230 := by decide
theorem block231 : checked 231 := by decide
theorem block232 : checked 232 := by decide
theorem block233 : checked 233 := by decide
theorem block234 : checked 234 := by decide
theorem block235 : checked 235 := by decide
theorem block236 : checked 236 := by decide
theorem block237 : checked 237 := by decide
theorem block238 : checked 238 := by decide
theorem block239 : checked 239 := by decide
theorem block240 : checked 240 := by decide
theorem block241 : checked 241 := by decide
theorem block242 : checked 242 := by decide
theorem block243 : checked 243 := by decide
theorem block244 : checked 244 := by decide
theorem block245 : checked 245 := by decide
theorem block246 : checked 246 := by decide
theorem block247 : checked 247 := by decide
theorem block248 : checked 248 := by decide
theorem block249 : checked 249 := by decide
theorem block250 : checked 250 := by decide
theorem block251 : checked 251 := by decide
theorem block252 : checked 252 := by decide
theorem block253 : checked 253 := by decide
theorem block254 : checked 254 := by decide
theorem block255 : checked 255 := by decide
theorem block256 : checked 256 := by decide
theorem block257 : checked 257 := by decide
theorem block258 : checked 258 := by decide
theorem block259 : checked 259 := by decide
theorem block260 : checked 260 := by decide
theorem block261 : checked 261 := by decide
theorem block262 : checked 262 := by decide
theorem block263 : checked 263 := by decide
theorem block264 : checked 264 := by decide
theorem block265 : checked 265 := by decide
theorem block266 : checked 266 := by decide
theorem block267 : checked 267 := by decide
theorem block268 : checked 268 := by decide
theorem block269 : checked 269 := by decide
theorem block270 : checked 270 := by decide
theorem block271 : checked 271 := by decide
theorem block272 : checked 272 := by decide
theorem block273 : checked 273 := by decide
theorem block274 : checked 274 := by decide
theorem block275 : checked 275 := by decide
theorem block276 : checked 276 := by decide
theorem block277 : checked 277 := by decide
theorem block278 : checked 278 := by decide
theorem block279 : checked 279 := by decide
theorem block280 : checked 280 := by decide
theorem block281 : checked 281 := by decide
theorem block282 : checked 282 := by decide
theorem block283 : checked 283 := by decide
theorem block284 : checked 284 := by decide
theorem block285 : checked 285 := by decide
theorem block286 : checked 286 := by decide
theorem block287 : checked 287 := by decide
theorem block288 : checked 288 := by decide
theorem block289 : checked 289 := by decide
theorem block290 : checked 290 := by decide
theorem block291 : checked 291 := by decide
theorem block292 : checked 292 := by decide
theorem block293 : checked 293 := by decide
theorem block294 : checked 294 := by decide
theorem block295 : checked 295 := by decide
theorem block296 : checked 296 := by decide
theorem block297 : checked 297 := by decide
theorem block298 : checked 298 := by decide
theorem block299 : checked 299 := by decide
theorem block300 : checked 300 := by decide
theorem block301 : checked 301 := by decide
theorem block302 : checked 302 := by decide
theorem block303 : checked 303 := by decide
theorem block304 : checked 304 := by decide
theorem block305 : checked 305 := by decide
theorem block306 : checked 306 := by decide
theorem block307 : checked 307 := by decide
theorem block308 : checked 308 := by decide

theorem all_blocks (b : Block) : checked b := by
  fin_cases b
  · exact block000
  · exact block001
  · exact block002
  · exact block003
  · exact block004
  · exact block005
  · exact block006
  · exact block007
  · exact block008
  · exact block009
  · exact block010
  · exact block011
  · exact block012
  · exact block013
  · exact block014
  · exact block015
  · exact block016
  · exact block017
  · exact block018
  · exact block019
  · exact block020
  · exact block021
  · exact block022
  · exact block023
  · exact block024
  · exact block025
  · exact block026
  · exact block027
  · exact block028
  · exact block029
  · exact block030
  · exact block031
  · exact block032
  · exact block033
  · exact block034
  · exact block035
  · exact block036
  · exact block037
  · exact block038
  · exact block039
  · exact block040
  · exact block041
  · exact block042
  · exact block043
  · exact block044
  · exact block045
  · exact block046
  · exact block047
  · exact block048
  · exact block049
  · exact block050
  · exact block051
  · exact block052
  · exact block053
  · exact block054
  · exact block055
  · exact block056
  · exact block057
  · exact block058
  · exact block059
  · exact block060
  · exact block061
  · exact block062
  · exact block063
  · exact block064
  · exact block065
  · exact block066
  · exact block067
  · exact block068
  · exact block069
  · exact block070
  · exact block071
  · exact block072
  · exact block073
  · exact block074
  · exact block075
  · exact block076
  · exact block077
  · exact block078
  · exact block079
  · exact block080
  · exact block081
  · exact block082
  · exact block083
  · exact block084
  · exact block085
  · exact block086
  · exact block087
  · exact block088
  · exact block089
  · exact block090
  · exact block091
  · exact block092
  · exact block093
  · exact block094
  · exact block095
  · exact block096
  · exact block097
  · exact block098
  · exact block099
  · exact block100
  · exact block101
  · exact block102
  · exact block103
  · exact block104
  · exact block105
  · exact block106
  · exact block107
  · exact block108
  · exact block109
  · exact block110
  · exact block111
  · exact block112
  · exact block113
  · exact block114
  · exact block115
  · exact block116
  · exact block117
  · exact block118
  · exact block119
  · exact block120
  · exact block121
  · exact block122
  · exact block123
  · exact block124
  · exact block125
  · exact block126
  · exact block127
  · exact block128
  · exact block129
  · exact block130
  · exact block131
  · exact block132
  · exact block133
  · exact block134
  · exact block135
  · exact block136
  · exact block137
  · exact block138
  · exact block139
  · exact block140
  · exact block141
  · exact block142
  · exact block143
  · exact block144
  · exact block145
  · exact block146
  · exact block147
  · exact block148
  · exact block149
  · exact block150
  · exact block151
  · exact block152
  · exact block153
  · exact block154
  · exact block155
  · exact block156
  · exact block157
  · exact block158
  · exact block159
  · exact block160
  · exact block161
  · exact block162
  · exact block163
  · exact block164
  · exact block165
  · exact block166
  · exact block167
  · exact block168
  · exact block169
  · exact block170
  · exact block171
  · exact block172
  · exact block173
  · exact block174
  · exact block175
  · exact block176
  · exact block177
  · exact block178
  · exact block179
  · exact block180
  · exact block181
  · exact block182
  · exact block183
  · exact block184
  · exact block185
  · exact block186
  · exact block187
  · exact block188
  · exact block189
  · exact block190
  · exact block191
  · exact block192
  · exact block193
  · exact block194
  · exact block195
  · exact block196
  · exact block197
  · exact block198
  · exact block199
  · exact block200
  · exact block201
  · exact block202
  · exact block203
  · exact block204
  · exact block205
  · exact block206
  · exact block207
  · exact block208
  · exact block209
  · exact block210
  · exact block211
  · exact block212
  · exact block213
  · exact block214
  · exact block215
  · exact block216
  · exact block217
  · exact block218
  · exact block219
  · exact block220
  · exact block221
  · exact block222
  · exact block223
  · exact block224
  · exact block225
  · exact block226
  · exact block227
  · exact block228
  · exact block229
  · exact block230
  · exact block231
  · exact block232
  · exact block233
  · exact block234
  · exact block235
  · exact block236
  · exact block237
  · exact block238
  · exact block239
  · exact block240
  · exact block241
  · exact block242
  · exact block243
  · exact block244
  · exact block245
  · exact block246
  · exact block247
  · exact block248
  · exact block249
  · exact block250
  · exact block251
  · exact block252
  · exact block253
  · exact block254
  · exact block255
  · exact block256
  · exact block257
  · exact block258
  · exact block259
  · exact block260
  · exact block261
  · exact block262
  · exact block263
  · exact block264
  · exact block265
  · exact block266
  · exact block267
  · exact block268
  · exact block269
  · exact block270
  · exact block271
  · exact block272
  · exact block273
  · exact block274
  · exact block275
  · exact block276
  · exact block277
  · exact block278
  · exact block279
  · exact block280
  · exact block281
  · exact block282
  · exact block283
  · exact block284
  · exact block285
  · exact block286
  · exact block287
  · exact block288
  · exact block289
  · exact block290
  · exact block291
  · exact block292
  · exact block293
  · exact block294
  · exact block295
  · exact block296
  · exact block297
  · exact block298
  · exact block299
  · exact block300
  · exact block301
  · exact block302
  · exact block303
  · exact block304
  · exact block305
  · exact block306
  · exact block307
  · exact block308

theorem facts (i : Row) : Facts i := by
  let b : Block := ⟨i.val/2048,by dsimp [Block]; omega⟩
  let k : Fin 2048 := ⟨i.val%2048,Nat.mod_lt _ (by decide)⟩
  have he : index b k = i.val := by dsimp [index,b,k]; omega
  have hi : index b k<632104 := by rw [he]; exact i.isLt
  simpa only [he] using all_blocks b k hi

theorem ownerBody : ∀ i : Row, owners.get? (key i) = some i.val := by decide

theorem all_floor_total : (∑ i : Row,floor80 i) = 1163968980828875260040 := by decide

theorem unique_corner {i j : Row} (h : lo i = lo j) : i=j := by
  have hh : key i=key j := by rw [key,key,h]
  have he := ownerBody i
  rw [hh,ownerBody j] at he
  exact Fin.ext (Option.some.inj he).symm

end
end ImbalancedChen.P4AOriginalSavedSixthBank
