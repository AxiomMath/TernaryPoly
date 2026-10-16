module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineCycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineInvariant

@[expose] public section


/-!
# The twisted good-line edge: vanishing criterion for relative classes

For odd `n`, a relative two-cocycle of the sign-twisted good-line stabilizer is a coboundary exactly
when its edge cocycle (with values in `Sym^{n+1} ⊗ det⁻¹`) is a coboundary of a binary potential
(`goodLineRelativeH2_zero_iff_binaryPotentialT`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

theorem goodLineBinaryEdgeCycle_H1_zero_iffT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ)) :
    groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) (goodLineBinaryEdgeCycleT n χ hχ positive cycle) = 0 ↔
      groupCohomology.H2π (goodLineCoefficientRepT n χ) cycle.val = 0 := by
  rw [goodLineBinaryEdgeCycle_H1T,
    LinearMap.map_eq_zero_iff _ (goodLineBinaryEdge_injective_of_oddT n χ hχ positive odd)]
  constructor
  · intro zero
    exact congrArg Subtype.val zero
  · intro zero
    exact Subtype.ext zero

/-- A relative class of the twisted good-line stabilizer vanishes iff its edge cocycle is the
coboundary of a binary potential in `Sym^{n+1} ⊗ det⁻¹`. -/
theorem goodLineRelativeH2_zero_iff_binaryPotentialT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) (odd : Odd n)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ)) :
    groupCohomology.H2π (goodLineCoefficientRepT n χ) cycle.val = 0 ↔
      ∃ potential : Binary.HomogeneousPoly (n + 1), ∀ matrix : GeneralLinearGroup (Fin 2) ℤ,
        goodLineBinaryEdgeCycleT n χ hχ positive cycle matrix =
          Binary.homogeneousAction (n + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) potential -
            potential := by
  rw [← goodLineBinaryEdgeCycle_H1_zero_iffT n χ hχ positive odd, groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨potential, equality⟩
    exact ⟨potential, fun matrix => (congrFun equality matrix).symm⟩
  · rintro ⟨potential, equality⟩
    exact ⟨potential, funext (fun matrix => (equality matrix).symm)⟩

end TernaryPeriodPolynomials.Twisted
