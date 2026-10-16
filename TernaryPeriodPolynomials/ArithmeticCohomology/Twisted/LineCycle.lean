module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineStab

@[expose] public section


/-!
# The cocycle-level edge formula at the twisted good line

For a relative two-cocycle `c` of the good-line stabilizer with sign-twisted coefficients, the mixed
radical one-cocycle `goodLineRadicalEdgeCycleT n χ c m` of the lower radical lattice is
`u ↦ c(diag(m,1), u(u m)) - c(u(u), diag(m,1))` (`goodLineSplitEdgeCycle_applyT`), and its binary
coordinate is the edge cocycle `goodLineBinaryEdgeCycleT` with values in `Sym^{n+1} ⊗ det⁻¹`
(`goodLineBinaryEdgeCycle_valueT`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Twisted

/-- The mixed radical one-cocycle of a relative two-cocycle, as a cocycle of the lower radical
lattice representation. -/
def goodLineRadicalEdgeCycleT (n : ℕ) (χ : RankOneCharacter)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n) :=
  goodLineCocycleCastT n χ (splitEdgeCycle goodLineSplitting (goodLineCoefficientRepT n χ) matrix cycle)

/-- The edge one-cocycle with values in `Sym^{n+1} ⊗ det⁻¹`. -/
def goodLineBinaryEdgeCycleT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n) :
    relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ) →ₗ[ℂ]
      groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)) :=
  (groupCohomology.mapCocycles₁ (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
    (goodLineRadicalCoordinateIsoT n χ hχ positive).hom).hom.comp
      (splitCocycleEdge goodLineSplitting (goodLineCoefficientRepT n χ))

theorem goodLineBinaryEdgeCycle_applyT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineBinaryEdgeCycleT n χ hχ positive cycle matrix =
      lowerRadicalCocycleCoordinate n (goodLineRadicalEdgeCycleT n χ cycle matrix) := by
  have equality := groupCohomology.mapCocycles₁_comp_i_apply
    (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ)) (goodLineRadicalCoordinateIsoT n χ hχ positive).hom
    (splitCocycleEdge goodLineSplitting (goodLineCoefficientRepT n χ) cycle)
  have value := congrFun equality matrix
  change goodLineBinaryEdgeCycleT n χ hχ positive cycle matrix =
    goodLineRadicalEquivT n χ positive
      (groupCohomology.H1π (goodLineRadicalRepT n χ)
        (splitEdgeCycle goodLineSplitting (goodLineCoefficientRepT n χ) matrix cycle)) at value
  have transport : goodLineRadicalEquivT n χ positive
        (groupCohomology.H1π (goodLineRadicalRepT n χ)
          (splitEdgeCycle goodLineSplitting (goodLineCoefficientRepT n χ) matrix cycle)) =
      lowerRadicalCocycleCoordinate n (goodLineRadicalEdgeCycleT n χ cycle matrix) :=
    (goodLineRadicalEquivT_apply n χ positive _).trans
      ((congrArg (fun cls => lowerRadicalH1Coordinate n positive cls)
        (goodLineH1CastIsoT_apply n χ _)).trans (lowerRadicalH1Coordinate_apply positive _))
  exact value.trans transport

theorem goodLineBinaryEdgeCycle_H1T (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ)) :
    groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) (goodLineBinaryEdgeCycleT n χ hχ positive cycle) =
      goodLineBinaryEdgeT n χ hχ positive
        (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRepT n χ) cycle) := by
  rw [goodLineBinaryEdge_applyT]
  change groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))
      (groupCohomology.mapCocycles₁ (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
        (goodLineRadicalCoordinateIsoT n χ hχ positive).hom
        (splitCocycleEdge goodLineSplitting (goodLineCoefficientRepT n χ) cycle)) =
    groupCohomology.map (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
      (goodLineRadicalCoordinateIsoT n χ hχ positive).hom 1
      (groupCohomology.H1π (splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRepT n χ))
        (splitCocycleEdge goodLineSplitting (goodLineCoefficientRepT n χ) cycle))
  exact (groupCohomology.H1π_comp_map_apply
    (A := splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRepT n χ))
    (B := arithmeticBinaryRep (n + 1) (-1)) (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
    (goodLineRadicalCoordinateIsoT n χ hχ positive).hom
    (splitCocycleEdge goodLineSplitting (goodLineCoefficientRepT n χ) cycle)).symm

theorem goodLineSplitEdgeCycle_applyT (n : ℕ) (χ : RankOneCharacter)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    goodLineRadicalEdgeCycleT n χ cycle matrix radical =
      cycle.val (goodLineLeviSection matrix, goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical)) -
        cycle.val (goodLineRadicalInclusion radical, goodLineLeviSection matrix) := by
  have input : splitRadicalInput goodLineSplitting matrix radical = lowerLeviLatticeInput matrix radical :=
    goodLineSplitting_inverse_action matrix radical
  have edge : splitEdgeCycle goodLineSplitting (goodLineCoefficientRepT n χ) matrix cycle radical =
      cycle.val (goodLineLeviSection matrix, goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical)) -
        cycle.val (goodLineRadicalInclusion radical, goodLineLeviSection matrix) :=
    (splitEdgeCycle_apply goodLineSplitting (goodLineCoefficientRepT n χ) matrix cycle radical).trans
      (congrArg (fun source : RadicalLattice =>
        cycle.val (goodLineLeviSection matrix, goodLineRadicalInclusion source) -
          cycle.val (goodLineRadicalInclusion radical, goodLineLeviSection matrix)) input)
  exact (goodLineCocycleCastT_apply n χ _ radical).trans edge

/-- The actual target edge formula retains the level-three lattice normalization and the determinant
twist `-1`. -/
theorem goodLineBinaryEdgeCycle_valueT (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineBinaryEdgeCycleT n χ hχ positive cycle matrix = lowerRadicalCoordinate n
      (fun coordinate => (lowerRadicalAverageEquiv n coordinate).symm
        (cycle.val (goodLineLeviSection matrix,
            goodLineRadicalInclusion (lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate))) -
          cycle.val (goodLineRadicalInclusion (radicalLatticeGenerator coordinate), goodLineLeviSection matrix))) := by
  rw [goodLineBinaryEdgeCycle_applyT, lowerRadicalCocycleCoordinate_value]
  congr 1
  funext coordinate
  rw [goodLineSplitEdgeCycle_applyT]

end TernaryPeriodPolynomials.Twisted
