# Static assembly reduction (not elaboration acceptance)

For each original input i : Fin127, fin_cases gives literal k in 0..126. Fin.castSucc preserves k and Fin.succ has value k+1. Its goal is therefore rowKey ⟨k,_⟩ < rowKey ⟨k+1,_⟩. Exactly one leaf interval [a,b) contains k; instantiate leaf argument ⟨k-a, by decide⟩ : Fin(b-a). The leaf conclusion reduces to rowKey ⟨a+(k-a),_⟩ < rowKey ⟨a+(k-a)+1,_⟩, with both arithmetic expressions closed natural literals reducing to k and k+1. The Fin bound witnesses are proposition proofs and proof-irrelevant. Every generated case checks these equalities and local-index bounds in the static manifest.

`by decide` is used only for the closed local Fin bound k-a < b-a (maximum7<8, final6<7), never for the grid-key inequality. Grid inequalities retain original `fin_cases` / `norm_num` coordinate unfolding in small leaves. No native_decide or trust bypass. A genuine Lean compile, complete axioms and matching kernel replay remain required.
