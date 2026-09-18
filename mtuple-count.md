## 1. The objects, in symbols

Fix a finite field `K` of characteristic `2`, `|K| = 2ⁿ`, `n ≥ 2`, and a subset
`S ⊆ K`.

| object | symbols | meaning |
| --- | --- | --- |
| trace | `Tr : K → 𝔽₂` | absolute trace |
| character | `χ(x) = (−1)^{Tr x} ∈ ℤ` | canonical additive character |
| transform | `T̂(u) = ∑_{y ∈ S} χ(u·y) ∈ ℤ` | Fourier/Walsh transform of the indicator of `S` |
| half-size | `Half(S) ⇔ #S = 2ⁿ⁻¹` | equivalently `2·#S = #K` |
| admissible vectors | `𝒜ₘ = { c ∈ Kᵐ : (∀i. cᵢ ≠ 0) ∧ ∑ᵢ cᵢ = 0 }` | |
| count | `Nₘ(c) = #{ x ∈ Sᵐ : ∑ᵢ cᵢ·xᵢ = 0 }` | |
| phase | `Pₘ(c) = ∑_{t ∈ K∖{0}} ∏ᵢ T̂(t·cᵢ) ∈ ℤ` | |
| generic value | `gₙ,ₘ = 2^{(m−1)n−m} = (#S)ᵐ/#K` | |
| deficiency | `Dₘ(c) = Nₘ(c) − gₙ,ₘ` | |

Kasami instance: `dₖ = 2^{2k} − 2^k + 1 = 4^k − 2^k + 1`,
`Δ = Δₖ = { b^{dₖ} + (b+1)^{dₖ} + 1 : b ∈ K }`, and for `v₁ ≠ v₂` both nonzero

```
N(v₁,v₂) = #{ (x,y,z) ∈ Δ³ : v₁x + v₂y + (v₁+v₂)z = 0 }.
```

Note `(v₁, v₂, v₁+v₂) ∈ 𝒜₃` in characteristic `2`, and `g_{n,3} = 2^{2n−3}`; so
`N(v₁,v₂) = N₃(v₁,v₂,v₁+v₂)` with `S = Δ`, and the Carlet/Kasami statement is
exactly the `m = 3` instance of "the count is generic".

---

## 2. The `m`-tuple result in symbols

**(D) Dictionary (Fourier identity + half-size normalisation).**

```
|K|·Nₘ(c) = ∑_{t ∈ K} ∏ᵢ T̂(t·cᵢ)        (any S, any c)
|K|·Dₘ(c) = Pₘ(c)                        (if Half(S), m ≥ 2, n ≥ 2)
Nₘ(c) = gₙ,ₘ  ⟺  Pₘ(c) = 0
```

**(M) Mean identity (the parity dichotomy).** With `g(u) = |K|·1_S(u) − |S|`,
which for a half-size set takes the values `±2ⁿ⁻¹` equally often,

```
|K| · ∑_{c ∈ 𝒜ₘ} ∏ᵢ T̂(cᵢ) = ∑_{u ∈ K} g(u)ᵐ = 2^{n−1}·(2^{n−1})^m·(1 + (−1)^m)

⟹   ∑_{c ∈ 𝒜ₘ} Pₘ(c) = 0      (m odd)
     ∑_{c ∈ 𝒜ₘ} Pₘ(c) > 0      (m even)
```

**(T₊) Odd `m` theorem.** For `n ≥ 2`, `m ≥ 3` odd, `Half(S)`:

```
(∀ c ∈ 𝒜ₘ. Pₘ(c) ≥ 0)   ⟹   ∀ c ∈ 𝒜ₘ. Nₘ(c) = gₙ,ₘ
```

and in fact the hypothesis and the conclusion are *equivalent* (non-negative
integers with zero sum are zero).

**(T₋) Even `m` obstruction.** For `n ≥ 2`, `m ≥ 2` even and **every**
half-size `S`:

```
∃ c ∈ 𝒜ₘ. Nₘ(c) > gₙ,ₘ      (already at every constant c = (a,…,a))
```

so no hypothesis on the phase can give the even analogue of (T₊).

**(SF) The mechanism.** If `T̂ = ε·w` with `w ≥ 0` pointwise, `ε(0) = 1`,
`ε(u+v) = ε(u)ε(v)`, then for `c ∈ 𝒜ₘ` the sign factors cancel
(`∏ᵢ ε(t·cᵢ) = ε(t·∑ᵢcᵢ) = ε(0) = 1`) and `Pₘ(c) ≥ 0`. Additive subgroups,
their cosets and trace hyperplanes have such a factorisation.

**(RIG) Rigidity: the exact reach of the mechanism.** For half-size `S`,

```
HasSignFactorization(S)  ⟺  ∃ u₀ ≠ 0, ∃ d ∈ 𝔽₂. S = { y ∈ K : Tr(u₀y) = d }
```

i.e. the mechanism reaches **exactly** the affine trace hyperplanes.

**(EX) Exact count on the whole reach of the mechanism.** For a half-size
additive subgroup / coset / affine trace hyperplane `V`, every `m ≥ 2`:

```
Nₘ(c) = gₙ,ₘ            for every non-constant c ∈ 𝒜ₘ
Nₘ(c) = 2·gₙ,ₘ          for every constant  c ∈ 𝒜ₘ
```

**(K) Kasami instance.** For `k ≡ ±1 (mod n)` the set `Δₖ` is (a Frobenius
twist of) the image of `b ↦ b² + b`, hence a half-size additive subgroup, so
(EX) applies:

```
∀ m ≥ 3 odd.  ∀ c ∈ 𝒜ₘ.  Nₘ(c) = gₙ,ₘ  on S = Δₖ        (in particular m = 3: 2^{2n−3})
∀ m ≥ 2 even. the m-tuple statement fails
```

**(SEP) Separation of the levels.** There is a half-size `S ⊆ GF(16)` (not a
subgroup) with `N₃(c) = 32 = g_{4,3}` for **every** `c ∈ 𝒜₃` and
`N₅(c') = 2040 ≠ 2048 = g_{4,5}` for some `c' ∈ 𝒜₅`. So the `m = 3` conclusion
does **not** imply the `m = 5` conclusion.

---

reference: https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-04-000005&version=1