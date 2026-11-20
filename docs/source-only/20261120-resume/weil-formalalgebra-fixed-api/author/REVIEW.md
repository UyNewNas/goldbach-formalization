# FormalAlgebra actual R4 diagnosis and candidate

Status: frozen source candidate for independent review; not compiled or accepted.

## Exact failing execution

The relevant execution is run 43681964804, job 132714310563, driver dfeabf9b5e88703c8700a388d53277132e586b90, source e364670c1f9a59b64d395be22371ea3d0b406ffc. The fixed environment is Lean 4.33.0-rc1 with mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

The physical stdout member is 5,193 bytes / SHA256 54389ab5c19afe2b233719df0395c7a55a3a4c5a5f2a3310a8bd8707c591181b. It reports nine errors in FormalAlgebra: seven incorrect derivative applications at old lines 44 (two), 69, 116, 117, 171, 172, and two later rewrites at 125 and 179 involving the elaborator's error recovery terms. FormalAlgebra was actually invoked once, pid 65578, exit 1. The outer Stock no-build rejection text is a generic subprocess failure wrapper, not evidence of a pre-source rejection. The earlier job-log-only interpretation is superseded; n09 preserves its historical observation.

The source preimage is 8,645 bytes / SHA256 68e2f08d38b65dd7bec6ba58998849059ffd479fff9e51d39ad3948e7b687915 / Git blob 1560e6494b5987c9c2dfcc7595fe0bd57ac3b2ea. It matches the actual WEIL_STAGE source row and n09 compiler census exactly.

## Root cause and smallest complete candidate

1. At the fixed pin, `PowerSeries.derivative` has an explicit coefficient-ring argument, and the notation `d⁄dX` expands to that declaration. Every existing derivative in this file acts on `ℂ⟦X⟧`. The candidate adds `ℂ` to the file's 13 existing derivative applications.
2. Source inspection also reveals a necessary compatibility defect hidden behind the ill-typed theorem head: fixed-pin Log.lean has `deriv_log`, but no `derivative_log_mul_one_add_X`. The latter is present in the known upstream 56a005 source and cannot be assumed available in the project's old pin. A local `hlog_base` proves the needed identity from the pinned `deriv_log`, coefficient extensionality, and elementary cancellation of adjacent powers of minus one. The original substitution/chain-rule proof then uses this local fact.
3. The two rewrite failures are secondary to the ill-typed derivative expressions. Their proof steps remain unchanged. This diagnosis is not a claim that the repaired file has compiled; a real successful compile may reveal other obligations.

The local coefficient argument is elementary: the constant coefficient of `D(log ℂ) * (1 + X)` is 1. At index `n + 1`, its coefficient is the complex image of `(-1)^(n+1) + (-1)^n = 0`. The candidate expresses this by the fixed-pin `deriv_log`, `ext (_ | n)`, and `simp [mul_add, pow_succ]`. No new number-theoretic result or new generating identity is assumed.

Classification: API expression incompatibility plus a missing old-pin derivation for an existing algebraic identity. There is no identified mathematical gap or manuscript boundary change here. This is an upstream formal-series helper; no manuscript adapter, Carlitz hypothesis, recurrence range, spectral root conclusion, or external theorem boundary changes.

## Declaration and dependency preservation

Two declaration conclusions require surface syntax adaptation, so literal-header invariance would be false. `DECLARATION_CORRESPONDENCE.md` gives the complete before/after text and quantifier, hypothesis, object, and conclusion correspondence. The other 13 declaration headers remain literal matches. Three public imports, 15 names, namespace, module mode, and all original mathematical assumptions remain unchanged.

The candidate is 8,804 bytes / SHA256 202b5832455324f3dd9c060c7ef9e29563e540bb042b095859cd7f25524df528 / Git blob 7727bfdccb9d76b7dc3789e188426ee11cc8a772. `FormalAlgebra.patch` contains the complete diff. All fixed-pin references are exact official repository source GETs with locally recomputed matching Git blob identities. The upstream Log snapshot is comparison only and is not a dependency upgrade or imported proof source.

## Reuse and downstream partition

Reuse n09's independently frozen runtime observations at `../n09-acceptance-review/runtime-r4-light`, freeze SHA256 f6fd49abedaf997540e7720524b26a7a4f078308b1464cca6a1b4c832eacf4ee. Six actual math-source invocations occurred. ClassGhost, RelevantIrreducibles, IrreducibleGhost, NewtonIndex, and NewtonSum succeeded; FormalAlgebra failed; 13 further modules were not reached. The original 15 protected modules had zero source invocations. All 91 fixture tests passed once.

Only after the five successful current objects receive independent physical-byte and current-input qualification may the next useful partition be 20 protected plus 14 necessary fresh. The new five are metadata-only identities in the light artifact and are not automatically ready for reuse. Do not repeat all original 19 fresh modules. No cache/stock/no-cold-fallback/zero-invocation gate or producer protocol is changed by this candidate.

Kernel replay, types/axioms, and whole-34 acceptance remain unperformed. This work grants no proof credit and makes no native6 or full-J closure claim.

## Verification performed and prohibited work avoided

Performed: original/candidate byte hashes and Git blob hashes; original actual-stage identity matching; official fixed-pin API body inspection and blob matching; complete source diff review; a limited static declaration-header extraction and correspondence check; import/name preservation; no sorry/admit/axiom token check. The extraction is explicitly not Lean AST or elaboration.

Not performed: Lean, Lake, LSP, kernel, project helper/setup/stage/guard/fixture execution, CI dispatch, artifact download, Git mutation, or publication. ROOT retains integration and execution control. Independent source review and an authorized real compile are still required.
