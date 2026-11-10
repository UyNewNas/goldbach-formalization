# T08 · Critical scattering on the original cusp space

For every positive level $N$ with trivial nebentypus and every real $t$, the native Eisenstein columns satisfy the physical functional equation at each point of the upper half-plane. Their outgoing constant-term matrix satisfies both unitary identities. The index set is the existing finite quotient of the signed primitive rows, identified with the actual `Γ₀(N)` cusp orbits. Each entry uses the source and observing frames with their own normalized widths.

```
s = ½+it
E_a(z,s) = Σ_b Φ_ab(t) E_b(z,1−s)
Φ(−t) = Φ(t)*      Φ(t)Φ(t)* = Φ(t)*Φ(t) = I
```

## Reciprocity and character reflection

At a fixed positive lower-left entry $c$, a representative $A=g^{-1}γh$ has lower-right residue $d$ modulo $cw_h$. The reverse entry comes from the genuine determinant-one matrix $-A^{-1}$, with lower-right residue $-A_{00}$ modulo $cw_g$. Right translation by the observing width restores the canonical representative. Equal original rows differ by a left integral translation. Membership in the original group forces its exponent to be a multiple of the source width, so the reverse class is independent of the lift. The inverse construction supplies a bijection with the opposite residue set. The initial Dirichlet entries are symmetric as a consequence. Meromorphic uniqueness transfers this symmetry to the regular part of the native family. Conjugation of the original real positive seeds gives Schwarz reflection, both for the physical functions and their height-one observed entries.

For primitive conductor $q>1$, swapping the actual ordered divisor pair implements the signed coefficient reflection `λχ⁻¹(n,1−s)=λχ(n,s)`. The factor at negative $n$ agrees because the parity value is real. The native kernel has even order. Together these yield the functional equation of the completed original series. At $q=1$ the prior completed level-one reflection includes both genuine constant terms. On $t≠0$, the ordinary uncompletion scalar is nonzero by the primitive Gauss transform, nonvanishing of gamma and the Dirichlet zero-free line at $2s≠1$. The proof uses its exact conductor and gamma factors and the regularized reciprocal for principal square. [Young, Proposition 4.2 and equations (4.5)–(4.6)](https://arxiv.org/html/1710.03624v2#S4.SS2)

## Recovering the coefficients of the native equation

The original forward expansion of each ordinary dilation into normalized parabolic functions continues from `Re(s)>1` with its explicit entire coefficient. This holds for every legal $q²B∣N$. Combining it with the actual inverse Young transform shows every native column at $t≠0$ is a finite combination of the native columns at $−t$, with coefficients independent of the spatial point. The proof obtains that relation before identifying any coefficient with a scattering entry. [Young, Theorems 6.1 and 7.1](https://arxiv.org/html/1710.03624v2#S7)

In the normalized chart at $b$, take the unit-period mean of that equality at every $y>0$. The preceding five-source scattering packet gives the two coefficients of $y^s$ and $y^{1-s}$ in each physical mean. Their values and first height derivatives at $y=1$ determine both coefficients since $2s-1=2it≠0$. Comparing the outgoing coefficients identifies the reflected-span coordinate as `Φ_ab(t)`. Comparing the incoming coefficients gives `Σ_b Φ_ab(t)Φ_bc(−t)=δ_ac`. The physical family and every entry depend continuously on real $t$ through the origin. Continuity therefore proves both identities at $t=0$, where the height powers agree. Symmetry and Schwarz reflection then yield the adjoint identity and both unitary products.

## Relation to P3.5

The manuscript invokes the normalized four-spectrum formula at level $z>0$, the continuous cusp sum with one $1/(4π)$, and the formal norm change used by ABL. This packet proves the physical functional equation and scattering unitarity on that continuous cusp family at $N=z$. The preceding global relative ABL inequality, original signed Fourier rows, compact Poincaré pairings and discrete projected Hilbert sum retain their recorded hypotheses. [Classical-input correspondence](../../../../../chen-imbalanced-semiprimes/paper/source/modules/final-classical-input-correspondence-20261010.txt) · [Medium completion §§7–8, 10](../../../../../chen-imbalanced-semiprimes/paper/source/modules/distribution-medium-completion-20261010.txt) · [Young, Proposition 8.2](https://arxiv.org/html/1710.03624v2#S8.SS3) · [Drappeau, Proposition 4.7](https://arxiv.org/pdf/1504.05549v4)

P3.5 remains yellow. The global continuous spectral resolution, with its residual constant and complete spatial normalization, still has to connect the continuous packet to the full quotient inner product. The geometric Bessel test and its inverse, the actual complete holomorphic and oldform Hilbert norms, native Hecke and Kim–Sarnak inputs, and the regular and exceptional estimates on the original coefficient functionals remain open. There is no new evidence of a mathematical omission in the original manuscript. The five additions are source only. Local work consisted of source inspection, lexical checks and SHA-256 comparison. They have zero kernel credit.
