import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Ring.GeomSum

/-!
# Geometric sums of additive endomorphisms

This companion to the foundational endomorphism API evaluates the ordinary
ring-level geometric-series identity on an element.  It is kept separate from
`Mathlib.Algebra.Group.Hom.End` because it depends on geometric sums.
-/

namespace AddMonoid.End

open Finset

variable {A : Type*} [AddCommGroup A]

/-- Evaluate the ring-level geometric-series identity for an additive endomorphism. -/
theorem apply_sum_pow_sub (φ : AddMonoid.End A) (n : ℕ) (x : A) :
    φ (∑ i ∈ range n, (φ ^ i) x) - ∑ i ∈ range n, (φ ^ i) x =
      (φ ^ n) x - x := by
  let ev : AddMonoid.End A →+ A :=
    { toFun := fun f => f x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsum : ((∑ i ∈ range n, φ ^ i) x) = ∑ i ∈ range n, (φ ^ i) x :=
    map_sum ev (fun i => φ ^ i) (range n)
  have h := DFunLike.congr_fun (mul_geom_sum φ n) x
  change (φ - 1) ((∑ i ∈ range n, φ ^ i) x) = (φ ^ n - 1) x at h
  rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply] at h
  change φ ((∑ i ∈ range n, φ ^ i) x) - ((∑ i ∈ range n, φ ^ i) x) =
    (φ ^ n) x - x at h
  rwa [hsum] at h

/-- A geometric orbit sum is fixed if the corresponding power of the
endomorphism is the identity. -/
theorem apply_sum_pow_eq_self {n : ℕ} (φ : AddMonoid.End A) (hφ : φ ^ n = 1)
    (x : A) : φ (∑ i ∈ range n, (φ ^ i) x) = ∑ i ∈ range n, (φ ^ i) x := by
  rw [← sub_eq_zero, apply_sum_pow_sub, hφ]
  simp

end AddMonoid.End
