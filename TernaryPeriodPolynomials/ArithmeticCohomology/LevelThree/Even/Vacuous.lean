module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Parity
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Cases

@[expose] public section


/-!
# Even degree: the spherical source inputs are vacuous

A cuspidal representation with a nonzero `GL₂(ℤ̂)`-fixed vector and a nonzero cohomology class in
degree `n` forces `n` to be odd (`Oldform.odd_of_sphericalCusp`).  Hence for even `n` no
inducing datum `D` is spherical, and the two spherical source inputs of the level-three rank lower
bound, `SphericalGoodPlaneSource D` and `SphericalBadLineSource D`, hold for every character
(their hypothesis `SphericalCusp D.cusp` is false).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThreeSource

namespace TernaryPeriodPolynomials.EvenLevelThree

variable {n : ℕ}

/-- **For even degree no cohomological cuspidal representation is spherical.** -/
theorem not_sphericalCusp_of_even {σ : CuspidalRepresentation} (heven : Even n)
    (cohomological : Cohomological σ n) : ¬ SphericalCusp σ := fun hsph =>
  (Nat.not_even_iff_odd.mpr
    (TernaryPeriodPolynomials.Oldform.odd_of_sphericalCusp hsph cohomological))
    heven

/-- **The spherical good-plane source input (N2) for even degree** is vacuous. -/
theorem sphericalGoodPlaneSource_of_even (D : InducingData n) (heven : Even n) :
    SphericalGoodPlaneSource D := fun hsph _ =>
  absurd hsph (not_sphericalCusp_of_even heven D.cohomological)

/-- **The spherical bad-line source input for even degree** is vacuous. -/
theorem sphericalBadLineSource_of_even (D : InducingData n) (heven : Even n) :
    SphericalBadLineSource D := fun hsph _ =>
  absurd hsph (not_sphericalCusp_of_even heven D.cohomological)

end TernaryPeriodPolynomials.EvenLevelThree
