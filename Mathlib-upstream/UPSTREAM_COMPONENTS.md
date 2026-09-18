# Small upstream candidates

This pass separated the application-independent pieces of the Dobbertin
linearization development from local proof glue.  The resulting source files
live under `MathlibExtras/` and use Mathlib-style namespaces, declarations,
docstrings, and narrow imports.

## 1. Geometric sums of additive endomorphisms

File: `MathlibExtras/Algebra/Group/Endomorphism/GeomSum.lean`

Suggested destination: a small geometric-sum companion file for endomorphisms.
This avoids adding a geometric-sum dependency to the foundational
`Mathlib.Algebra.Group.Hom.End` module.

```lean
theorem AddMonoidHom.sum_apply
    (f : ι → A →+ B) (s : Finset ι) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x

theorem AddMonoid.End.apply_mul_geom_sum
    (φ : AddMonoid.End A) (n : ℕ) (x : A) :
    (φ - 1) (∑ i ∈ Finset.range n, (φ ^ i) x) = (φ ^ n - 1) x

theorem AddMonoid.End.apply_sum_pow_sub
    (φ : AddMonoid.End A) (n : ℕ) (x : A) :
    φ (∑ i ∈ Finset.range n, (φ ^ i) x) -
      ∑ i ∈ Finset.range n, (φ ^ i) x = (φ ^ n) x - x

theorem AddMonoid.End.apply_sum_pow_eq_self
    {n : ℕ} (φ : AddMonoid.End A) (hφ : φ ^ n = 1) (x : A) :
    φ (∑ i ∈ Finset.range n, (φ ^ i) x) =
      ∑ i ∈ Finset.range n, (φ ^ i) x
```

Why it is reusable:

- `AddMonoidHom.sum_apply` is the missing additive-hom counterpart of the
  existing `LinearMap.sum_apply`; it assumes only additive commutative monoids;
- the algebraic identity itself is already Mathlib's `mul_geom_sum`, applied in
  the ring `AddMonoid.End A`—no new endomorphism-level algebra theorem is needed;
- `apply_mul_geom_sum` factors out only evaluation/coercion glue, and
  `apply_sum_pow_sub` is then a thin, rewrite-oriented corollary;
- these results are useful for traces, orbit constructions, cyclic actions,
  and additive difference equations, without bespoke induction or `abel`.

### Suggested PR granularity

The strongest first PR is the focused `AddMonoidHom.sum_apply` API gap, placed
near the additive-hom big-operator API and accompanied by examples/tests. A
second PR may add `AddMonoid.End.apply_mul_geom_sum` and its two thin corollaries
in this companion module if multiple consumers justify them. If there is only
one consumer, keeping the evaluated geometric sum downstream is preferable:
`congrArg (fun g ↦ g x) (mul_geom_sum φ n)` already exposes the canonical proof.
No `[simp]` attribute is proposed for the geometric-sum theorem; its orientation
is useful explicitly, but global simplification would be too specialized.

The project now consumes these declarations in `Endomorphism.lean`; its old
local proofs have become thin compatibility wrappers. This demonstrates that
the extraction is usable rather than dead auxiliary code.

## 2. Frobenius periodicity modulo the extension degree

File: `MathlibExtras/FieldTheory/Finite/FrobeniusPeriod.lean`

Suggested destination: `Mathlib.FieldTheory.Finite.Basic`, immediately after
`FiniteField.frobenius_pow`.

```lean
theorem FiniteField.frobenius_pow_eq_pow_mod
    (hcard : Fintype.card K = p ^ n) (m : ℕ) :
    frobenius K p ^ m = frobenius K p ^ (m % n)

theorem FiniteField.iterateFrobenius_mod
    (hcard : Fintype.card K = p ^ n) (m : ℕ) (x : K) :
    iterateFrobenius K p m x = iterateFrobenius K p (m % n) x
```

Why it is reusable:

- Mathlib already proves `FiniteField.frobenius_pow`; reducing arbitrary powers
  modulo the extension degree is its natural generic corollary;
- the first statement is useful for endomorphism algebra, while the second
  avoids forcing pointwise users to rewrite through powers of ring homs; these
  are distinct use cases, so both forms are retained;
- neither theorem needs a `0 < n` hypothesis;
- the proof is just the generic `pow_eq_pow_mod`, so the API has low maintenance
  cost.

## Components deliberately not proposed

Several local declarations were reviewed but should not be upstreamed in their
current form:

- The project-local `frobenius` and `frobeniusEnd` duplicate Mathlib's existing
  `frobenius` and `iterateFrobenius` ring homomorphisms. New generic work should
  use the Mathlib API instead.
- `frobenius_one_fixed_iff_bit` is nearly a specialization of
  `eq_zero_or_one_of_sq_eq_self`; its reverse implication is immediate. A new
  theorem would add little unless Mathlib wants a general iff for idempotents in
  cancellative monoids with zero.
- `linearization_exponent`, `linearization_product`, and the lemmas in
  `CharTwoSteps.lean` are clean and useful locally, but their statements are
  tailored to one exponent pattern or one proof assembly. They do not yet show
  enough independent reuse for Mathlib.
- `absoluteTrace`, `partialTrace`, and `numeratorSum` encode the conventions of
  this application rather than Mathlib's established finite-field trace API.
- `linearize_char_two` is a strong application lemma, not a foundational
  library component.

## Submission shape

The two candidate files are intentionally independent and should be submitted as
separate PRs; the project history likewise records the endomorphism and
finite-field additions in separate commits. Neither requires importing the
Dobbertin development.
`MathlibExtras.lean` is only a project root module collecting both candidates.
The geometric-sum module is exercised by the application through
`Endomorphism.lean`; the Frobenius module is independently build-checked.
