# Dobbertin Theorem 1 — standalone first step

This folder is independent of the earlier `DobbertinLego` and `Dobbertin` proof trees.
It imports only Mathlib and builds the linearization step from first principles:

1. `Endomorphism.lean`: finite orbit sums and the abstract telescope;
2. `Frobenius.lean`: binary Frobenius, finite-field periodicity, and step-orbit loops;
3. `Linearization.lean`: trace, partial trace, equations (1) and (2), and their implication.

Root module: `DobbertinTheorem1Standalone.lean`.

Headline theorem:

```lean
Dobbertin.Theorem1Standalone.equationOne_implies_equationTwo
```

This MVP intentionally formalizes the first step of the proof rather than importing
the later fibre-uniqueness machinery used for the complete permutation criterion.
The visual exposition is in `docs/DobbertinTheorem1Standalone.tex` and `.pdf`.
