import RequestProject.StandaloneDobbertin.Foundation.Frobenius

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace DobbertinStandalone

/-- A congruence `k * kInv ≡ 1 (mod n)` already forces `k` and `n` to be
coprime.  Thus the separate coprimality hypothesis in the headline theorem is
mathematically redundant, although it is useful as an explicit interface for
lemmas about Frobenius kernels and multiplicative exponents. -/
theorem coprime_of_inverse_mod
    (n k kInv : ℕ) (hInv : k * kInv ≡ 1 [MOD n]) :
    Nat.Coprime k n := by
  exact Nat.coprime_of_mul_modEq_one kInv hInv

/-- An inverse representative in the canonical interval `[0,n)` is unique. -/
theorem inverseRepresentative_unique
    (n k kInv₁ kInv₂ : ℕ)
    (hInv₁ : k * kInv₁ ≡ 1 [MOD n])
    (hInv₂ : k * kInv₂ ≡ 1 [MOD n])
    (h₁lt : kInv₁ < n) (h₂lt : kInv₂ < n) :
    kInv₁ = kInv₂ := by
  have hcop : Nat.Coprime k n := Nat.coprime_of_mul_modEq_one kInv₁ hInv₁
  have hm : k * kInv₁ ≡ k * kInv₂ [MOD n] := hInv₁.trans hInv₂.symm
  have hi : kInv₁ ≡ kInv₂ [MOD n] :=
    Nat.ModEq.cancel_left_of_coprime hcop.symm.gcd_eq_one hm
  exact hi.eq_of_lt_of_lt h₁lt h₂lt

/-- Restricting an exponent to `[0,n)` chooses a unique representative of its
congruence class modulo `n`.  In the theorem, `0 < k < n` is therefore a
normalization of the Frobenius step rather than an extra finite-field
identity. -/
theorem exponentRepresentative_unique
    (n k₁ k₂ : ℕ) (hmod : k₁ ≡ k₂ [MOD n])
    (h₁lt : k₁ < n) (h₂lt : k₂ < n) :
    k₁ = k₂ := by
  exact hmod.eq_of_lt_of_lt h₁lt h₂lt

/-- On `GF(2^n)`, Frobenius powers depend only on the exponent modulo `n`.
This is the formal reason that replacing `k` by its canonical representative
does not change the underlying Frobenius arrow. -/
theorem frobeniusStep_eq_of_modEq
    (n k₁ k₂ : ℕ) (x : GF n) (hn : 0 < n)
    (hmod : k₁ ≡ k₂ [MOD n]) :
    x ^ (2 ^ k₁) = x ^ (2 ^ k₂) := by
  exact gf_frobenius_mod n k₁ k₂ x hn hmod

end DobbertinStandalone
