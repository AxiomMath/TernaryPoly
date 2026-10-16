module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Rotations

@[expose] public section


/-!
# The weight gap of a cuspidal representation

The common vocabulary of the construction of the `Cohomological` witness for the cuspidal
constituents of the Bergman model.  `WeightGap σ n` says that `σ` has no nonzero vector of rotation
weight of absolute value less than `n + 3`: this is the `K`-type gap of the holomorphic discrete
series of weight `n + 3` (and its conjugate).  It replaces, for the constituents of the model, the
Casimir weight gap that `Cohomological σ n` gives (`cohomological_hilbert_projection_zero`), which
cannot be used while the `Cohomological` witness is being constructed.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers (binaryRotations)

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-- **The weight gap**: a vector of the cuspidal representation `σ` on which the rotations of
`SO(2)` act through the character `a ↦ a ^ m` with `|m| < n + 3` is zero. -/
def WeightGap (σ : CuspidalRepresentation) (n : ℕ) : Prop :=
  ∀ (m : ℤ) (u : σ.H),
    (∀ a : Circle, σ.π (atInfinity (binaryRotations a)) u = (a : ℂ) ^ m • u) →
      |m| < (n : ℤ) + 3 → u = 0

end TernaryPeriodPolynomials.Automorphic.Constituent
