import Mathlib
import DobbertinTheorem1Standalone.Endomorphism

/-! Binary Frobenius specializes the abstract endomorphism orbit. -/

namespace Dobbertin.Theorem1Standalone

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The `r`-fold binary Frobenius. -/
def frobenius (r : ℕ) (x : F) : F := x ^ (2 ^ r)

omit [Fintype F] in
lemma frobenius_add (r : ℕ) (x y : F) :
    frobenius r (x + y) = frobenius r x + frobenius r y :=
  add_pow_char_pow (p := 2) (n := r) x y

omit [Fintype F] [CharP F 2] in
lemma frobenius_comp (a b : ℕ) (x : F) :
    frobenius a (frobenius b x) = frobenius (a + b) x := by
  simp only [frobenius]
  rw [← pow_mul, ← pow_add]
  ring_nf

/-- Frobenius as an additive endomorphism. -/
def frobeniusEnd (r : ℕ) : AddMonoid.End F :=
  AddMonoidHom.mk' (frobenius r) (frobenius_add r)

omit [Fintype F] in
@[simp] lemma frobeniusEnd_apply (r : ℕ) (x : F) :
    frobeniusEnd r x = frobenius r x := rfl

omit [Fintype F] in
lemma frobeniusEnd_pow_apply (step i : ℕ) (x : F) :
    (frobeniusEnd step ^ i) x = frobenius (i * step) x := by
  induction i with
  | zero => simp [frobenius]
  | succ m ih =>
    rw [pow_succ']
    show frobeniusEnd step ((frobeniusEnd step ^ m) x) = _
    rw [ih, frobeniusEnd_apply, frobenius_comp]
    ring_nf

omit [CharP F 2] in
lemma frobenius_periodic {period : ℕ} (field_cardinality : Fintype.card F = 2 ^ period)
    (r : ℕ) (x : F) : frobenius r x = frobenius (r % period) x := by
  simp only [frobenius]
  conv_lhs =>
    rw [show r = period * (r / period) + r % period from
      (Nat.div_add_mod r period).symm, pow_add, pow_mul]
  have step : ∀ j : ℕ, x ^ (2 ^ (period * j)) = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ← field_cardinality,
        FiniteField.pow_card, ih]
  rw [step]

omit [CharP F 2] in
lemma frobenius_full_period {period : ℕ}
    (field_cardinality : Fintype.card F = 2 ^ period) (x : F) :
    frobenius period x = x := by
  simp only [frobenius]
  rw [← field_cardinality]
  exact FiniteField.pow_card x

lemma frobeniusEnd_full_period {period : ℕ}
    (field_cardinality : Fintype.card F = 2 ^ period) :
    frobeniusEnd (F := F) 1 ^ period = 1 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [frobeniusEnd_pow_apply, Nat.mul_one, frobenius_full_period field_cardinality]
  rfl

/-- A step-Frobenius orbit sum. -/
def frobeniusLoop (step length : ℕ) (x : F) : F :=
  orbitSum (frobeniusEnd step) length x

omit [Fintype F] in
/-- Characteristic two turns subtraction in the abstract telescope into addition. -/
lemma frobeniusLoop_telescope (step length : ℕ) (x : F) :
    frobenius step (frobeniusLoop step length x) + frobeniusLoop step length x =
      frobenius (length * step) x + x := by
  have h := orbitSum_telescope (frobeniusEnd (F := F) step) length x
  rw [frobeniusEnd_pow_apply, frobeniusEnd_apply,
    sub_eq_add_neg, sub_eq_add_neg] at h
  simpa [frobeniusLoop, CharTwo.neg_eq] using h

end Dobbertin.Theorem1Standalone
