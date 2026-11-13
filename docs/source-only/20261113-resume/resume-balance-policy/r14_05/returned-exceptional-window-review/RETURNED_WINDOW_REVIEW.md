# Exceptional input and return on a fixed native order band

I checked the five frozen source modules against the literal discrete slots in the same-infinity trace, the native single-bump floor, the additive ceiling, the common-prefix estimate and the fixed-level arbitrary-vector sieve. The selected source base is 06f3e98f81031d292c99cee98fd14c78909e3254, together with the exact initial-geometry and provider successors named in the allowlist. The statements concern the conditional order restriction inside a finite sum. They require no assumption that every actual eigenvalue obeys such a restriction.

## Which slots are estimated

At positive level z, retained(T,z) filters the genuine exceptional cusp eigenbasis indices by τ=2√(1/4−λ)≤T, for a fixed 0≤T<1. The slot is the contraction over the same positive interval [a,b) on both marks with conjugate(e(mω)) e(nω), the original native weight and the identity-frame factor conjugate(Rᵢ(m))Rᵢ(n). The native row uses ρᴷ=2R on nonzero marks. Consequently 4 times the original complex slot equals the marked product of the native rows. This also gives 4 times the norm on the output. No absolute value has been inserted into either of the original two linear forms.

At the input, the real part of 4 times the single-bump slot is the real part of its native weight times the square of the norm of the untwisted interval row. The audited lower bound applies to each retained index. For every T there are c_T>0 and Y₀(T)≥1, chosen before Y, all finite level sets, the interval and the common phase. For Y≥Y₀, c_T times the retained Y-weighted energy is at most four times the sum of real parts over exactly those retained indices. The theorem's two sides use the same filter. It contains no positivity or absolute bound for any input term with τ>T and no comparison with the unfiltered trace. When T=0 this is an empty strict exceptional band.

## Mellin normalization and the returned window

On the return the test at m,n is Φ(Yx)Φ(4π√(mn)/(zQx)). The native weight divides the complementary Bessel moment by cos(πτ/2); the moment itself uses dx/x. For any finite set of positive marks, interval_mellin is an equality in ℂ with the real factor 1/(2π), the full real t-line, the actual cutoff density and the phase (4π/(zQ))ⁱᵗ multiplying the transform tested against Φ(Yx)x⁻ⁱᵗ. The conjugate row takes −t/2, the second row takes +t/2. Thus the mark factor in the opened Mellin product is mⁱᵗᐟ²nⁱᵗᐟ². Absolute integrability of the fixed-slot kernel and density justifies the finite row and integral exchanges. Its individual continuity/size bound is used for convergence only.

For fixed T and ε>0, native_additive bounds the normalized transform on the retained indices by K(T,ε)(Y^τ+Y^ε), uniformly in t. In particular cos(πτ/2)≥cos(πT/2)>0. Applying 2uv≤u²+v² to the two row norms leaves 1/(4π). Only after obtaining these nonnegative upper estimates on the selected slots does the proof enlarge the majorant to the full exceptional basis. This use of positivity on the right is valid without a common bound on the orders of the added slots.

Let L_B be the levels B<z≤2B and M=2ʲ−1/2. On 2ʲ≤a≤b≤2ʲ⁺¹, the positive interval satisfies b≤2a. For each half-twist the common-prefix estimate gives (1+|t/2|)² times the maximum of the full untwisted energy at one prefix endpoint. The endpoint is selected after summing over all levels of L_B and all actual exceptional multiplicities. Its set consists of min(b,n+1) for a≤n≤b. This contains every nonempty prefix. Adding the empty prefix of zero energy has no effect. The maximum is finite even when a=b, and empty level windows also give zero.

The unit-weight part applies the genuine fixed-level sieve at X=A=1 to the actual interval coefficients e(mω)mⁱˢ. Their squared norm sum is exactly the length, at most 2M independently of s. The two ρᴷ factors cost four, the arbitrary-vector bound supplies 2·sieveConstant, and #L_B≤2B. Each sign costs at most 32·sieveConstant·(B+M)M. Both together cost 64·sieveConstant·(B+M)M. The additive Y^ε price multiplies this unit-weight term alone.

The fixed fourth-power density decay gives integrable majorants for its norm and for its norm times (1+|t/2|)². After integration, for every fixed T,ε the constants C,Y₀ precede Y≥Y₀, Q,B>0, j,a,b and ω. The result is

$$
4\sum_{z\in L_B}\sum_{i\in\mathrm{retained}(T,z)}|\mathrm{output}_{z,i}|
\le C_{T,\varepsilon}\big(\max_{a\le c\le b} E(L_B,Y,\omega;a,c)+Y^\varepsilon(B+M)M\big).
$$

The density moments are fixed constants. The main returned energy carries no Y-dependent logarithmic multiplier.

## Use in the original induction

Drappeau, proof of (4.29) on p. 17, needs the extraction from the entire first trace and the estimate of every relevant returned component. A common spectral cap T<1 on the actual family would identify retained(T,z) with the full exceptional spectrum for these comparisons. A different route would have to prove separate sign or error bounds on the excluded input and returned terms that suffice for the extraction. Mere positivity of the eigenvalues yields τ<1 at each slot and gives no common c_T, C or Y₀. A maximum chosen after selecting finitely many levels would enter the recursion's constants. The separately required numeric weight transport, the ordinary Maaß and all-incoming Eisenstein errors, and the combined recurrence also remain pending. The original medium §10(v)–(vii) at 9731290e preserves the common interval and phase across levels. Full (4.29), (4.30), Pascadi J and 7/32 receive no closure from this audit. All five modules are unelaborated and unverified by kernel here.
