import DobbertinTheorem1Standalone.Frobenius

/-!
The paper's equation (1) and equation (2), assembled directly from orbit sums.
This is the standalone first step of Dobbertin's Theorem 1.
-/

namespace Dobbertin.Theorem1Standalone

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- Absolute trace, represented by the full Frobenius orbit. -/
def absoluteTrace (period : ℕ) (x : F) : F :=
  frobeniusLoop 1 period x

/-- Partial trace along the step-Frobenius orbit. -/
def partialTrace (step inverseStep : ℕ) (x : F) : F :=
  frobeniusLoop step inverseStep x

/-- The numerator sum in equation (1), obtained by advancing the partial trace. -/
def numeratorSum (step inverseStep : ℕ) (x : F) : F :=
  frobenius step (partialTrace step inverseStep x)

/-- Dobbertin's cleared equation (1). -/
def EquationOne (period step inverseStep traceCoefficient : ℕ) (c x : F) : Prop :=
  c * x ^ (2 ^ step + 1) =
    numeratorSum step inverseStep x + (traceCoefficient : F) * absoluteTrace period x

/-- The affine linearized expression in equation (2). -/
def EquationTwoExpression (step : ℕ) (c x : F) : F :=
  c ^ (2 ^ step) * x ^ (2 ^ (2 * step)) + x ^ (2 ^ step) + c * x + 1

/-- The absolute trace is a bit. -/
theorem absoluteTrace_is_bit {period : ℕ}
    (field_cardinality : Fintype.card F = 2 ^ period) (x : F) :
    absoluteTrace period x = 0 ∨ absoluteTrace period x = 1 := by
  have hfix := orbitSum_fixed (frobeniusEnd (F := F) 1)
    (frobeniusEnd_full_period field_cardinality) x
  rw [frobeniusEnd_apply] at hfix
  have hsq : absoluteTrace period x ^ 2 = absoluteTrace period x := by
    simpa [absoluteTrace, frobeniusLoop, frobenius] using hfix
  have hfactor : absoluteTrace period x * (absoluteTrace period x - 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfactor with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

/-- The partial trace telescope has only the two endpoint terms. -/
theorem partialTrace_telescope {period step inverseStep : ℕ}
    (field_cardinality : Fintype.card F = 2 ^ period)
    (inverse_mod_period : step * inverseStep % period = 1) (x : F) :
    numeratorSum step inverseStep x + partialTrace step inverseStep x = x ^ 2 + x := by
  have h := frobeniusLoop_telescope (F := F) step inverseStep x
  have hend : frobenius (inverseStep * step) x = x ^ 2 := by
    rw [frobenius_periodic field_cardinality, Nat.mul_comm inverseStep step,
      inverse_mod_period]
    simp [frobenius]
  rw [hend] at h
  simpa [numeratorSum, partialTrace] using h

/-- The algebraic core: a solution of equation (1), with a bit in place of its
trace term, satisfies equation (2). -/
theorem linearize_bit_equation {period step inverseStep : ℕ}
    (field_cardinality : Fintype.card F = 2 ^ period)
    (inverse_mod_period : step * inverseStep % period = 1)
    {bit c x : F} (bit_is_bit : bit = 0 ∨ bit = 1) (x_nonzero : x ≠ 0)
    (equation_one : numeratorSum step inverseStep x + bit =
      c * x ^ (2 ^ step + 1)) :
    EquationTwoExpression step c x = 0 := by
  unfold EquationTwoExpression
  set P := partialTrace step inverseStep x
  set S := numeratorSum step inverseStep x
  have hS : S = P ^ (2 ^ step) := rfl
  have hP : S + P = x ^ 2 + x :=
    partialTrace_telescope field_cardinality inverse_mod_period x
  have hbit_pow : bit ^ (2 ^ step) = bit := by
    rcases bit_is_bit with rfl | rfl <;>
      simp [zero_pow (show (2 : ℕ) ^ step ≠ 0 by positivity)]
  have hP_closed : P = (x ^ 2 + x) + c * x ^ (2 ^ step + 1) + bit := by
    rw [hS] at hP
    grind +ring
  have hS_closed : S = (x ^ 2) ^ (2 ^ step) + x ^ (2 ^ step) +
      (c * x ^ (2 ^ step + 1)) ^ (2 ^ step) + bit := by
    rw [hS, hP_closed, add_pow_char_pow, add_pow_char_pow, add_pow_char_pow,
      hbit_pow]
  have hcore : c * x ^ (2 ^ step + 1) =
      (x ^ 2) ^ (2 ^ step) + x ^ (2 ^ step) +
        (c * x ^ (2 ^ step + 1)) ^ (2 ^ step) := by
    grind +ring
  apply mul_left_cancel₀ (pow_ne_zero (2 ^ step) x_nonzero)
  rw [mul_zero]
  have square_term : (x ^ 2) ^ (2 ^ step) = x ^ (2 ^ step) * x ^ (2 ^ step) := by
    rw [← pow_mul, ← pow_add]
    ring_nf
  have exponent_identity : (2 ^ step + 1) * 2 ^ step =
      2 ^ (2 * step) + 2 ^ step := by
    rw [add_mul, one_mul, ← pow_add, two_mul]
  have product_term : (c * x ^ (2 ^ step + 1)) ^ (2 ^ step) =
      c ^ (2 ^ step) * (x ^ (2 ^ (2 * step)) * x ^ (2 ^ step)) := by
    rw [mul_pow, ← pow_mul, exponent_identity, pow_add]
  rw [square_term, product_term] at hcore
  linear_combination (norm := ring_nf) hcore
  simp [CharTwo.two_eq_zero]

/-- **First step of Dobbertin's Theorem 1:** equation (1) implies equation (2)
for every nonzero field element. -/
theorem equationOne_implies_equationTwo {period step inverseStep traceCoefficient : ℕ}
    (field_cardinality : Fintype.card F = 2 ^ period)
    (inverse_mod_period : step * inverseStep % period = 1)
    (traceCoefficient_is_bit : traceCoefficient = 0 ∨ traceCoefficient = 1)
    {c x : F} (x_nonzero : x ≠ 0)
    (h : EquationOne period step inverseStep traceCoefficient c x) :
    EquationTwoExpression step c x = 0 := by
  have trace_term_is_bit :
      (traceCoefficient : F) * absoluteTrace period x = 0 ∨
      (traceCoefficient : F) * absoluteTrace period x = 1 := by
    rcases traceCoefficient_is_bit with rfl | rfl
    · simp
    · simpa using absoluteTrace_is_bit field_cardinality x
  exact linearize_bit_equation field_cardinality inverse_mod_period
    trace_term_is_bit x_nonzero h.symm

end Dobbertin.Theorem1Standalone
