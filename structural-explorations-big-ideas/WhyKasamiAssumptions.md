# Why assume `gcd(k,n)=1`, `k<n`, and `k' ≡ 1/k (mod n)`?

Here `GF(2^n)` is acted on by the Frobenius automorphism

\[
F(x)=x^2,\qquad F^r(x)=x^{2^r},\qquad F^n=\mathrm{id}.
\]

Consequently, the exponent index `r` matters only modulo `n`.

## 1. `0 < k < n`: choose one Frobenius step

The proof uses the step

\[
F^k:x\longmapsto x^{2^k}.
\]

Because `F^(k+n)=F^k`, replacing `k` by `k mod n` gives the same Frobenius
arrow.  Thus `k<n` is principally a **canonical-representative convention**:
it removes duplicate descriptions of the same step.  Together with `0<k`, it
also excludes the identity step `k=0`.

This periodicity is formalized by
`DobbertinStandalone.frobeniusStep_eq_of_modEq`, while uniqueness of a
representative in `[0,n)` is
`DobbertinStandalone.exponentRepresentative_unique`.

## 2. `gcd(k,n)=1`: make the step traverse one full orbit

Coprimality says that addition by `k` permutes the residue classes modulo `n`:

\[
0,k,2k,\ldots,(n-1)k \pmod n
\]

visits every class exactly once.  This has two decisive algebraic effects in
the proof.

1. It gives
   \[
   \gcd(2^k-1,2^n-1)=2^{\gcd(k,n)}-1=1.
   \]
   Therefore raising a nonzero field element to the power `2^k-1` is
   invertible.  This is what permits the construction of the `Delta` gadget.

2. The fixed points of `F^k` in `GF(2^n)` form `GF(2^gcd(k,n))`.  Under
   coprimality this is just `GF(2)={0,1}`.  Hence the kernel of
   \[
   u\longmapsto u^{2^k}+u
   \]
   is exactly `{0,1}`.  This turns a potentially large family of candidates
   into a two-element pair, which the residual Kasami equation can separate.

If `d=gcd(k,n)>1`, the fixed field is `GF(2^d)` and that kernel has `2^d`
elements.  The pair argument used in the theorem would therefore no longer be
valid as stated.

## 3. `k k' ≡ 1 (mod n)`: choose the reverse step

The number `k'` is the modular inverse of `k`.  It is not a field inverse; it
is an inverse of the **index step** in the cyclic group `Z/nZ`:

\[
k k'\equiv1\pmod n.
\]

It is needed because the generalized Kasami polynomial contains the orbit sum

\[
\sum_{i=1}^{k'}x^{2^{ik}}.
\]

Applying `F^k` shifts its indices.  The endpoint after `k'` steps is

\[
F^{k k'}=F,
\]

where the equality follows from `k k'≡1 (mod n)`.  This is exactly what makes
the sum telescope to the required endpoint and makes the parity
`k' + α n (mod 2)` appear in the final criterion.

The restriction `0<k'<n` chooses the unique positive representative of this
inverse class, so the displayed finite sum and its parity are unambiguous.
The formal uniqueness result is
`DobbertinStandalone.inverseRepresentative_unique`.

## 4. Are the assumptions independent?

No.  The inverse congruence already implies coprimality:

\[
k k'\equiv1\pmod n\quad\Longrightarrow\quad\gcd(k,n)=1.
\]

This is machine-verified as
`DobbertinStandalone.coprime_of_inverse_mod`.

Conversely, for the nondegenerate modulus in the theorem, coprimality ensures
that a modular inverse class exists; the range condition selects its unique
representative.  The headline theorem states both `gcd(k,n)=1` and the chosen
inverse equation because they play different **interface roles** in the
modular proof:

- coprimality is passed directly to fixed-field, kernel, and exponentiation
  lemmas;
- the concrete congruence is passed directly to Frobenius endpoint and
  telescoping lemmas.

So the assumptions can be read structurally as

\[
\boxed{\text{canonical step }k}
\;\longrightarrow\;
\boxed{\text{one full cyclic orbit}}
\;\longrightarrow\;
\boxed{\text{canonical reverse step }k'}.
\]

They prevent duplicate indexing, collapse the Frobenius fixed field to
`GF(2)`, and make the orbit sums close at precisely the endpoint used by the
proof.
