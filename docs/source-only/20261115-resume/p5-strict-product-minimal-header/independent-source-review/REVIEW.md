T05 independent header-delta review, 2026-11-15.

Allow the exact 1623-byte source SHA `583f0dc13613c195819114996eeb2d77dc0a8521d037e59510ee731995d6e5b4`, blob `1e374d8f68fa98a4282a2c41c13db7ef45b0836e`, as a source-level header successor of the previously reviewed 1637-byte `69442b656e5357d9d64fc82019967bf24119dc0a5152959af0106c6440823021`. The original mathematical AL `33b4835fd94b4d92fa690301ead03f1f338808ff0b3e5e1142e56ca3d333e497` remains bound to its own old bytes. This new AL separately reviews the import change; it does not automatically transfer the old hash's acceptance.

The frozen T01 package `a3c51b48b6531f7a63f40915c3abcd991da201eea3c4d253a3593ee9ba471164` has a dependency-metadata defect described below. Its source candidate can be approved independently, but its original import table is not approved as a complete or correct graph. No compilation, object reuse, stock qualification, producer configuration or CI action is authorized by this review.

Exact source difference

Independent raw-byte reconstruction verifies that the only edit is the first line:

`import ImbalancedChen.Part5OriginalH430W1PhysicalRoughDictionary`

becomes

`import MathlibNt.Wu2008DoubleSieve.GoldbachWeights`.

Every byte following the first LF is identical, with suffix SHA `0325ead7d49356be5a950021a7150d9020f7284238002ded364ab1c83d1371db`. The second import, InclusiveRoughProduct, is unchanged. Namespace, autoImplicit=false, opens, one theorem's full header, both original memberships, conclusion, proof body, comments and ending commands are unchanged. The old published-source identity and old AL were re-read against the supplied receipt; neither old source nor old freeze was edited.

The strict F<N mathematical argument, original carrier interpretation, N/d/unit/repeated-factor boundaries and absence of new assumptions remain those in the prior T05 review. They are not re-proved or expanded here. Source-level applicability of the new header depends on the actual retained owners, checked next.

Constant owners and reachability

All six explicitly used custom constants resolve to the same exact definitions/theorems from the fixed `09b97db5764ade1246bfb77206baa1b124760958` source selection:

| Constant | Actual defining module | Retained route |
| --- | --- | --- |
| Wu2008DoubleSieve.orderedTriples | MathlibNt.Wu2008DoubleSieve.FiniteWeights | GoldbachWeights directly imports FiniteWeights |
| Wu2008DoubleSieve.primeWindow | MathlibNt.Wu2008DoubleSieve.GoldbachWeights | New direct import |
| Wu2008DoubleSieve.mem_primeWindow | Same GoldbachWeights | New direct import |
| LiLiuPrereqBuchstab.roughNumbers | MathlibNt.SieveTheory.LiLiuPrereqBuchstabCount | InclusiveRoughProduct → InclusiveRoughUniform → NonunitRoughUniform → NonunitRoughUniformCore → LiLiuPrereqBuchstabUniform → Bands → BaseEstimate → Base → Count |
| LiLiuPrereqBuchstab.mem_roughNumbers | Same BuchstabCount | Same retained route |
| Wu2008DoubleSieve.InclusiveRoughUniform.nonunit_gate_iff | MathlibNt.Wu2008DoubleSieve.InclusiveRoughProduct | Unchanged direct import |

For each owner I re-read the actual source fragment, checked it against the bound fragment hash, and checked the real import headers along its route. All six match. The defining namespaces are unchanged; the target's unchanged opens expose Wu2008DoubleSieve and LiLiuPrereqBuchstab. The explicitly qualified product gate retains its original owner. No replacement definition, alias, private declaration or new same-named object is used.

PhysicalRoughDictionary itself declares integerMass, label, private lt_iff, private membership and actual_integer_mass_eq. None occurs in the target statement or proof. Its own file registers no additional instance/export/attribute. The statement's identification with the actual W1 integer and prime-restriction carriers remains supported by the prior exact-source mathematical review; the theorem does not need to import those larger consumers merely to retain that interpretation.

The target's other named constants are the standard Finset membership lemmas, Nat coprimality projection, positivity-from-nonzero and prime coprimality/divisibility lemma. Nat/Real, their casts, right-nested products, Finset membership, arithmetic and order instances are standard. The sole `simp [hD]` goal reduces a natural product with zero left factor to 0≤N; no removed project expression is involved. `ring` rearranges a Nat product for a divisibility witness, and `omega` combines the existing Nat ≤ and ≠ facts. No project-defined tactic is referenced.

FiniteWeights still imports Mathlib.Tactic at line 3. I re-read the local Mathlib/Tactic.lean and Tactic/Basic.lean bytes: they match the frozen T01 fixed-e4c source identities, including the Ring exports. The frozen standard-boundary record supplies the fixed Lean tactic barrel's Omega export. This supports the source-level standard tactic route; it is not an independent execution or a measured compiled owner/load inventory. Standard-source and toolchain compatibility remain later validation boundaries.

Retained attributes and source cone

I independently read all 35 supplied dependency sources: 26 goldbach and nine Architect. Their local bytes and source modes match the frozen records. A separate in-memory scan skips nested comments, line comments and strings and recognizes repeated public/meta prefixes in the import header. It executes no project helper and no Lean code. All 35 custom nodes remain reachable from the new root's two imports, with no ImbalancedChen project node in this source graph.

The 127 supplied attribute/instance context excerpts were each checked against those actual bytes. The relevant arithmetic instances remain standard; the additional custom instances concern tripleSurvives decidability, Circle or Sobolev types. Their simp rules concern rough/prime membership, Fourier/cumsum/nabla, Schwartz and custom function application. They do not supply a missing project rule for the target's elementary zero-product simp goal. Architect's metadata machinery remains in the retained import graph and is not treated as absent or compiled merely because this target does not invoke it.

This inspection shows the source-level imports and explicit owners needed by the unchanged proof remain present. It does not establish equivalence of the old and new elaborated environments, generated/private owner graphs, tactic output, instances selected at runtime, or actual loaded object sets. Those claims require the separate dynamic gates; no old compiled object is inherited.

Explicit correction to the original frozen metadata

The original a3c51 package's PRIMITIVE_SOURCE_CLOSURE records Architect.Basic and Architect.Tactic as importing only Lean at line 3. The exact unchanged sources instead contain:

| Module | Omitted actual import |
| --- | --- |
| Architect.Basic | line 4: `public meta import Batteries.Lean.NameMapAttribute` |
| Architect.Tactic | line 4: `public meta import Batteries.Lean.NameMapAttribute` |
| Architect.Tactic | line 5: `public import Architect.Basic` |

These are executable header imports, not comments. The omission is consistent with a scan ending at the combined public/meta prefix. It does not change the 35-node custom set because Architect.Basic is independently reached from Architect. It does change the import edges and standard boundary. The actual 35-source graph has 39 distinct explicit standard module names; including implicit Init gives 40. The frozen 38-name boundary includes Init but omits Lean and Batteries.Lean.NameMapAttribute. Thus any reading of the frozen report as asserting that all recorded real headers match is incorrect. The independent audit records both recorded and actual headers.

ROOT has authorized separate treatment: approve this exact source/header delta, retain HOLD on the a3c51 dependency metadata, and review any new correction addendum separately. The original a3c51 freeze remains immutable. Its old graph must not be repackaged as an approved complete dependency table. The candidate source itself needs no change for these metadata omissions.

Boundaries

The 14 bound package/provenance records, 35 source byte identities, six owner fragments and 127 context excerpts match. The two recorded header lists do not match and are explicitly held as above. No result about current 407 stock, the proposed 18-source compile set, available objects, ABI/private facets, research-path production, setup, kernel or types/axioms acceptance follows from this source AL. T01's object-search and future configuration material is not approved by this review.

Only the requested T05 review directory was written. No downloads, Lean/Lake/LSP, candidate/fixture/guard/project helper, quota tool, Git/GitHub mutation or agent spawning occurred. compiled=false, ready_to_install=false and formal_credit=0 remain, with no PP, h34, collar, 430/441 or main/J completion claim.
