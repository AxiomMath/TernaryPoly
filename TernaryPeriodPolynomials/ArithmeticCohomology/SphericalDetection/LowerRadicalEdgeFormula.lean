module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.InvariantH2

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The lower-radical coordinate uses inverse exponential averages of the lattice values. -/
theorem lowerRadicalCocycleCoordinate_value {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    lowerRadicalCocycleCoordinate degree cycle = lowerRadicalCoordinate degree
      (fun coordinate => (lowerRadicalAverageEquiv degree coordinate).symm
        (cycle (radicalLatticeGenerator coordinate))) := rfl

def goodLineBinaryEdgeCycle (degree : ℕ) (positive : 0 < degree) :
    relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree) →ₗ[ℂ]
      groupCohomology.cocycles₁ (arithmeticBinaryRep (degree + 1) 0) :=
  (groupCohomology.mapCocycles₁ (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
    (goodLineRadicalCoordinateIso degree positive).hom).hom.comp
      (splitCocycleEdge goodLineSplitting (goodLineCoefficientRep degree))

def goodLineRadicalEdgeCycle (degree : ℕ)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree) :=
  splitEdgeCycle goodLineSplitting (goodLineCoefficientRep degree) matrix cycle

theorem goodLineBinaryEdgeCycle_apply (degree : ℕ) (positive : 0 < degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineBinaryEdgeCycle degree positive cycle matrix =
      lowerRadicalCocycleCoordinate degree (goodLineRadicalEdgeCycle degree cycle matrix) := by
  have equality := groupCohomology.mapCocycles₁_comp_i_apply
    (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ)) (goodLineRadicalCoordinateIso degree positive).hom
    (splitCocycleEdge goodLineSplitting (goodLineCoefficientRep degree) cycle)
  have value := congrFun equality matrix
  change goodLineBinaryEdgeCycle degree positive cycle matrix =
    lowerRadicalH1Coordinate degree positive
      (groupCohomology.H1π (lowerRadicalLatticeRep degree)
        (splitEdgeCycle goodLineSplitting (goodLineCoefficientRep degree) matrix cycle)) at value
  exact value.trans (lowerRadicalH1Coordinate_apply positive _)

theorem goodLineBinaryEdgeCycle_H1 (degree : ℕ) (positive : 0 < degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree)) :
    groupCohomology.H1π (arithmeticBinaryRep (degree + 1) 0) (goodLineBinaryEdgeCycle degree positive cycle) =
      goodLineBinaryEdge degree positive
        (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep degree) cycle) := by
  rw [goodLineBinaryEdge_apply]
  change groupCohomology.H1π (arithmeticBinaryRep (degree + 1) 0)
      (groupCohomology.mapCocycles₁ (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
        (goodLineRadicalCoordinateIso degree positive).hom
        (splitCocycleEdge goodLineSplitting (goodLineCoefficientRep degree) cycle)) =
    groupCohomology.map (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
      (goodLineRadicalCoordinateIso degree positive).hom 1
      (groupCohomology.H1π (splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRep degree))
        (splitCocycleEdge goodLineSplitting (goodLineCoefficientRep degree) cycle))
  exact (groupCohomology.H1π_comp_map_apply
    (A := splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRep degree))
    (B := arithmeticBinaryRep (degree + 1) 0) (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
    (goodLineRadicalCoordinateIso degree positive).hom
    (splitCocycleEdge goodLineSplitting (goodLineCoefficientRep degree) cycle)).symm

theorem goodLineSplitEdgeCycle_apply (degree : ℕ)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    goodLineRadicalEdgeCycle degree cycle matrix radical =
      cycle.val (goodLineLeviSection matrix, goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical)) -
        cycle.val (goodLineRadicalInclusion radical, goodLineLeviSection matrix) := by
  exact (splitEdgeCycle_apply goodLineSplitting (goodLineCoefficientRep degree) matrix cycle radical).trans
    (congrArg (fun input : RadicalLattice =>
      cycle.val (goodLineLeviSection matrix, goodLineRadicalInclusion input) -
        cycle.val (goodLineRadicalInclusion radical, goodLineLeviSection matrix))
      (goodLineSplitting_inverse_action matrix radical))

/-- The actual target edge formula retains the level-three lattice normalization and twist zero. -/
theorem goodLineBinaryEdgeCycle_value (degree : ℕ) (positive : 0 < degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineBinaryEdgeCycle degree positive cycle matrix = lowerRadicalCoordinate degree
      (fun coordinate => (lowerRadicalAverageEquiv degree coordinate).symm
        (cycle.val (goodLineLeviSection matrix,
            goodLineRadicalInclusion (lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate))) -
          cycle.val (goodLineRadicalInclusion (radicalLatticeGenerator coordinate), goodLineLeviSection matrix))) := by
  rw [goodLineBinaryEdgeCycle_apply, lowerRadicalCocycleCoordinate_value]
  congr 1
  funext coordinate
  rw [goodLineSplitEdgeCycle_apply]

theorem goodLineBinaryEdgeCycle_H1_zero_iff (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree)) :
    groupCohomology.H1π (arithmeticBinaryRep (degree + 1) 0) (goodLineBinaryEdgeCycle degree positive cycle) = 0 ↔
      groupCohomology.H2π (goodLineCoefficientRep degree) cycle.val = 0 := by
  rw [goodLineBinaryEdgeCycle_H1,
    LinearMap.map_eq_zero_iff _ (goodLineBinaryEdge_injective_of_odd degree positive odd)]
  constructor
  · intro zero
    exact congrArg Subtype.val zero
  · intro zero
    exact Subtype.ext zero

theorem goodLineRelativeH2_zero_iff_binaryPotential (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree)) :
    groupCohomology.H2π (goodLineCoefficientRep degree) cycle.val = 0 ↔
      ∃ potential : Binary.HomogeneousPoly (degree + 1), ∀ matrix : GeneralLinearGroup (Fin 2) ℤ,
        goodLineBinaryEdgeCycle degree positive cycle matrix =
          Binary.homogeneousAction (degree + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) potential - potential := by
  rw [← goodLineBinaryEdgeCycle_H1_zero_iff degree positive odd, groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨potential, equality⟩
    exact ⟨potential, fun matrix => (congrFun equality matrix).symm⟩
  · rintro ⟨potential, equality⟩
    exact ⟨potential, funext (fun matrix => (equality matrix).symm)⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
