import Mathlib

/-! The one abstract LEGO block: a finite orbit of an additive endomorphism. -/

namespace Dobbertin.Theorem1Standalone

open Finset

variable {A : Type*} [AddCommGroup A]

/-- Sum the first `length` points in the orbit of `x` under `φ`. -/
def orbitSum (φ : AddMonoid.End A) (length : ℕ) (x : A) : A :=
  ∑ i ∈ range length, (φ ^ i) x

/-- The geometric-series telescope; all interior orbit points cancel. -/
theorem orbitSum_telescope (φ : AddMonoid.End A) (length : ℕ) (x : A) :
    φ (orbitSum φ length x) - orbitSum φ length x = (φ ^ length) x - x := by
  induction length with
  | zero => simp [orbitSum]
  | succ m ih =>
    have hcomp : φ ((φ ^ m) x) = (φ ^ (m + 1)) x := by
      rw [pow_succ']
      rfl
    simp only [orbitSum, sum_range_succ, map_add] at *
    rw [hcomp]
    abel_nf
    abel_nf at ih
    linear_combination (norm := abel) ih

/-- A full orbit sum is fixed when the endomorphism has the matching order. -/
theorem orbitSum_fixed {length : ℕ} (φ : AddMonoid.End A) (hφ : φ ^ length = 1)
    (x : A) : φ (orbitSum φ length x) = orbitSum φ length x := by
  have h := orbitSum_telescope φ length x
  rw [hφ] at h
  simpa using sub_eq_zero.mp (by simpa using h)

end Dobbertin.Theorem1Standalone
