import Mathlib
import DobbertinLego

/-!
# Bridge — the MacLane ladder reaches the same end-to-end result

`DobbertinLego/MacLaneLadder` builds the enrichment ladder from the *bare category*
axioms, starting not from `[Field F] [Fintype F] [CharP F 2]` but from the
object-first data

```
   [Field F] [Algebra (ZMod 2) F] [Module.Finite (ZMod 2) F].
```

There the Frobenius is the arrow `MacLane.frob : Module.End (ZMod 2) F`, its norm
element is `∑_{i<d} frob^i` (with `d = [F : 𝔽₂]`), the telescope is
`MacLane.frob_telescope`, and `MacLane.norm_isBit` shows the norm element is a bit.

This file is the **bridge**: it shows those object-first components are *literally
the same* as the concrete bricks of `DobbertinLego` (`frob`, `loop`, `trace`,
`frobEndo`, `loop_telescope`, `trace_isBit`), and then uses the MacLane ladder to
drive the concrete headline `equation2_of_equation1` all the way to the end.

| MacLane (object-first)                    | concrete brick (`Dobbertin.Lego`)      |
|-------------------------------------------|-----------------------------------------|
| `MacLane.frob`                            | `frob 1` / `frobEndo 1`                 |
| `∑_{i<d} MacLane.frob^i`                  | `trace d = loop 1 d`                    |
| `MacLane.frob_telescope`                  | `loop_telescope 1`                      |
| `MacLane.frob_pow_finrank` (`φ^d = 1`)    | `frobEndo_pow_card` (Fermat)            |
| `MacLane.norm_isBit`                      | `trace_isBit`                           |
| `Bridge.equation2_of_equation1`           | `equation2_of_equation1`                |

The dimension `d = Module.finrank (ZMod 2) F` plays the paper's role of `n`:
`Fintype.card F = 2 ^ d` (`card_eq_two_pow_finrank`).
-/

namespace Dobbertin.Lego.MacLane.Bridge

open Finset Dobbertin.Lego

variable {F : Type} [Field F] [Algebra (ZMod 2) F] [Module.Finite (ZMod 2) F]

/-- The object-first dimension `d = [F : 𝔽₂]` is the paper's `n`:
`|F| = 2^d`.  (`Fintype F` and `CharP F 2` are the derived instances of
`MacLaneLadder`.) -/
theorem card_eq_two_pow_finrank :
    Fintype.card F = 2 ^ Module.finrank (ZMod 2) F := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := F)]; simp [ZMod.card]

omit [Module.Finite (ZMod 2) F] in
/-- **Frobenius arrow = concrete Frobenius.**  Pointwise, MacLane's monoidal
Frobenius `MacLane.frob` is the concrete gadget `frob 1` (`x ↦ x²`). -/
theorem frob_eq_frob_one (x : F) : MacLane.frob (R := F) x = Dobbertin.Lego.frob 1 x := by
  simp [Dobbertin.Lego.frob]

omit [Module.Finite (ZMod 2) F] in
/-- The same identification packaged against the additive endomorphism `frobEndo 1`
that drives the abstract scaffold. -/
theorem frob_eq_frobEndo_one (x : F) : MacLane.frob (R := F) x = frobEndo (1 : ℕ) x := by
  simp [Dobbertin.Lego.frob]

omit [Module.Finite (ZMod 2) F] in
/-- **Norm element = absolute trace.**  MacLane's norm element `∑_{i<d} frob^i`
applied to `x` is exactly the paper's trace `Tr(x) = loop 1 d x`. -/
theorem norm_eq_trace (x : F) :
    (∑ i ∈ range (Module.finrank (ZMod 2) F), MacLane.frob (R := F) ^ i) x
      = trace (Module.finrank (ZMod 2) F) x := by
  rw [LinearMap.sum_apply]
  simp only [MacLane.frob_pow_apply]
  simp [trace, loop, Dobbertin.Lego.frob]

omit [Module.Finite (ZMod 2) F] in
/-- **Telescope = Artin–Schreier telescope.**  MacLane's `frob_telescope`, read
pointwise in characteristic `2`, is the concrete `loop_telescope` at `step = 1`:
`frob(Nₗₑₙ x) + Nₗₑₙ x = frob^len x + x`. -/
theorem frob_telescope_pointwise (len : ℕ) (x : F) :
    MacLane.frob (R := F) ((∑ i ∈ range len, MacLane.frob (R := F) ^ i) x)
        + (∑ i ∈ range len, MacLane.frob (R := F) ^ i) x
      = (MacLane.frob (R := F) ^ len) x + x := by
  have h := MacLane.frob_telescope (R := F) len
  have happ := congrArg (fun (e : Module.End (ZMod 2) F) => e x) h
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    CharTwo.sub_eq_add] at happ
  exact happ

/-- **Fermat / finite order matches.**  MacLane derives `φ^d = 1` from the object's
finite dimension; this is the arrow form of the concrete Fermat input
`frobEndo_pow_card`. -/
theorem frob_pow_finrank_eq_one :
    MacLane.frob (R := F) ^ (Module.finrank (ZMod 2) F) = 1 :=
  MacLane.frob_pow_finrank

omit [Module.Finite (ZMod 2) F] in
/-- **Bridge for "the trace is a bit".**  MacLane's `norm_isBit` and the concrete
`trace_isBit` are the same statement under `norm_eq_trace`. -/
theorem norm_isBit_iff_trace_isBit (x : F) :
    ((∑ i ∈ range (Module.finrank (ZMod 2) F), MacLane.frob (R := F) ^ i) x = 0
        ∨ (∑ i ∈ range (Module.finrank (ZMod 2) F), MacLane.frob (R := F) ^ i) x = 1)
      ↔ (trace (Module.finrank (ZMod 2) F) x = 0
        ∨ trace (Module.finrank (ZMod 2) F) x = 1) := by
  rw [norm_eq_trace]

/-- **End-to-end, driven by the MacLane ladder.**  Step `(1) ⟹ (2)` of
Dobbertin's Theorem 1, stated purely from the object-first data
`[Algebra (ZMod 2) F] [Module.Finite (ZMod 2) F]` with `n = [F : 𝔽₂]`.

The proof reuses the concrete linearization/telescoping (`linearized_eq_zero_of_solution`),
but the "trace is a bit" input is supplied **by the MacLane ladder**
(`MacLane.norm_isBit`, transported along `norm_eq_trace`) rather than by the
concrete `trace_isBit`.  So the MacLane build genuinely reaches the headline. -/
theorem equation2_of_equation1 {k k' α : ℕ}
    (hkk' : k * k' % Module.finrank (ZMod 2) F = 1) (hα : α = 0 ∨ α = 1)
    {c x : F} (hx : x ≠ 0)
    (h : equation1 (Module.finrank (ZMod 2) F) k k' α c x) :
    linearized k c x = 0 := by
  -- collapse `α · Tr(x)` to a bit, using MacLane's `norm_isBit`
  have hbit : (α : F) * trace (Module.finrank (ZMod 2) F) x = 0
      ∨ (α : F) * trace (Module.finrank (ZMod 2) F) x = 1 := by
    have hαcast : (α : F) = 0 ∨ (α : F) = 1 := by rcases hα with rfl | rfl <;> simp
    rcases hαcast with h0 | h1
    · exact Or.inl (by rw [h0, zero_mul])
    · rw [h1, one_mul, ← norm_eq_trace]; exact MacLane.norm_isBit x
  exact linearized_eq_zero_of_solution card_eq_two_pow_finrank hkk' hbit hx h.symm

/-- **Equivalence of the two headlines.**  On the object-first setting, the
MacLane-driven headline is interchangeable with the concrete
`Dobbertin.Lego.equation2_of_equation1`: each hypothesis of one is the hypothesis
of the other, with `n := [F : 𝔽₂]` and `Fintype.card F = 2^n`. -/
theorem equation2_agrees_with_concrete {k k' α : ℕ}
    (hkk' : k * k' % Module.finrank (ZMod 2) F = 1) (hα : α = 0 ∨ α = 1)
    {c x : F} (hx : x ≠ 0)
    (h : equation1 (Module.finrank (ZMod 2) F) k k' α c x) :
    equation2_of_equation1 hkk' hα hx h
      = Dobbertin.Lego.equation2_of_equation1 card_eq_two_pow_finrank hkk' hα hx h :=
  rfl

end Dobbertin.Lego.MacLane.Bridge
