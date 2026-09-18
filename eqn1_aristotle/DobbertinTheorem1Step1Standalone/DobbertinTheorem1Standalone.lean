import DobbertinTheorem1Standalone.Endomorphism
import DobbertinTheorem1Standalone.Frobenius
import DobbertinTheorem1Standalone.Linearization

/-!
# Standalone MVP for the first step of Dobbertin's Theorem 1

The complete dependency path is:

```text
additive endomorphism orbit
  → orbit telescope
  → binary Frobenius orbit
  → trace and partial trace
  → equation (1) implies equation (2)
```

The headline is
`Dobbertin.Theorem1Standalone.equationOne_implies_equationTwo`.
Only Mathlib and the three modules in `DobbertinTheorem1Standalone/` are imported.
-/
