module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerActions
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CohomologyEdge

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem identityPlaneSplitCocycleAction (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    splitRadicalCocycleAction identityPlaneSplitting (identityPlaneCoefficientRep degree) matrix cycle =
      upperRadicalCocycleLevi degree matrix cycle := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  exact (splitRadicalCocycleAction_apply identityPlaneSplitting (identityPlaneCoefficientRep degree)
    matrix cycle radical).trans (identityPlaneSplitting_cocycle_action degree matrix cycle radical).symm

theorem goodLineSplitCocycleAction (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    splitRadicalCocycleAction goodLineSplitting (goodLineCoefficientRep degree) matrix cycle =
      lowerRadicalCocycleLevi degree matrix cycle := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  exact (splitRadicalCocycleAction_apply goodLineSplitting (goodLineCoefficientRep degree)
    matrix cycle radical).trans (goodLineSplitting_cocycle_action degree matrix cycle radical).symm

theorem identityPlaneSplitH1Action (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    splitRadicalH1Action identityPlaneSplitting (identityPlaneCoefficientRep degree) matrix =
      upperRadicalH1Levi degree matrix := by
  apply LinearMap.ext
  intro cohomology
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (upperRadicalLatticeRep degree) cohomology
  exact (splitRadicalH1Action_apply identityPlaneSplitting (identityPlaneCoefficientRep degree) matrix cycle).trans
    ((congrArg (fun cocycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree) =>
      groupCohomology.H1π (upperRadicalLatticeRep degree) cocycle)
      (identityPlaneSplitCocycleAction degree matrix cycle)).trans (upperRadicalH1Levi_apply matrix cycle).symm)

theorem goodLineSplitH1Action (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    splitRadicalH1Action goodLineSplitting (goodLineCoefficientRep degree) matrix =
      lowerRadicalH1Levi degree matrix := by
  apply LinearMap.ext
  intro cohomology
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (lowerRadicalLatticeRep degree) cohomology
  exact (splitRadicalH1Action_apply goodLineSplitting (goodLineCoefficientRep degree) matrix cycle).trans
    ((congrArg (fun cocycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree) =>
      groupCohomology.H1π (lowerRadicalLatticeRep degree) cocycle)
      (goodLineSplitCocycleAction degree matrix cycle)).trans (lowerRadicalH1Levi_apply matrix cycle).symm)

def arithmeticBinaryRep (degree : ℕ) (twist : ℤ) : Rep ℂ (GeneralLinearGroup (Fin 2) ℤ) :=
  Rep.of ((Binary.homogeneousAction degree twist).comp (GeneralLinearGroup.map (Int.castRingHom ℂ)))

def identityPlaneRadicalCoordinateIso (degree : ℕ) :
    splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRep degree) ≅
      arithmeticBinaryRep (degree + 1) (-1) :=
  Rep.mkIso (Representation.Equiv.mk (upperRadicalH1Coordinate degree) (by
    intro matrix
    apply LinearMap.ext
    intro cohomology
    change groupCohomology.H1 (upperRadicalLatticeRep degree) at cohomology
    change upperRadicalH1Coordinate degree
        (splitRadicalH1Action identityPlaneSplitting (identityPlaneCoefficientRep degree) matrix cohomology) =
      Binary.homogeneousAction (degree + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (upperRadicalH1Coordinate degree cohomology)
    rw [identityPlaneSplitH1Action]
    exact upperRadicalH1Coordinate_equivariant matrix cohomology))

def goodLineRadicalCoordinateIso (degree : ℕ) (positive : 0 < degree) :
    splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRep degree) ≅
      arithmeticBinaryRep (degree + 1) 0 :=
  Rep.mkIso (Representation.Equiv.mk (lowerRadicalH1Coordinate degree positive) (by
    intro matrix
    apply LinearMap.ext
    intro cohomology
    change groupCohomology.H1 (lowerRadicalLatticeRep degree) at cohomology
    change lowerRadicalH1Coordinate degree positive
        (splitRadicalH1Action goodLineSplitting (goodLineCoefficientRep degree) matrix cohomology) =
      Binary.homogeneousAction (degree + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (lowerRadicalH1Coordinate degree positive cohomology)
    rw [goodLineSplitH1Action]
    exact lowerRadicalH1Coordinate_equivariant positive matrix cohomology))

def identityPlaneLeviCohomologyIso (degree : ℕ) :
    groupCohomology.H1 (splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRep degree)) ≅
      groupCohomology.H1 (arithmeticBinaryRep (degree + 1) (-1)) :=
  (groupCohomology.functor ℂ (GeneralLinearGroup (Fin 2) ℤ) 1).mapIso (identityPlaneRadicalCoordinateIso degree)

def goodLineLeviCohomologyIso (degree : ℕ) (positive : 0 < degree) :
    groupCohomology.H1 (splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRep degree)) ≅
      groupCohomology.H1 (arithmeticBinaryRep (degree + 1) 0) :=
  (groupCohomology.functor ℂ (GeneralLinearGroup (Fin 2) ℤ) 1).mapIso (goodLineRadicalCoordinateIso degree positive)

/-- The source stabilizer edge, with its actual determinant-twisted binary target. -/
def identityPlaneBinaryEdge (degree : ℕ) :
    (twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree)).ker →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (degree + 1) (-1)) :=
  (identityPlaneLeviCohomologyIso degree).hom.hom.comp
    (splitCohomologyEdge identityPlaneSplitting (identityPlaneCoefficientRep degree))

/-- The target stabilizer edge, with the distinct lower-radical binary twist. -/
def goodLineBinaryEdge (degree : ℕ) (positive : 0 < degree) :
    (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep degree)).ker →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (degree + 1) 0) :=
  (goodLineLeviCohomologyIso degree positive).hom.hom.comp
    (splitCohomologyEdge goodLineSplitting (goodLineCoefficientRep degree))

theorem identityPlaneBinaryEdge_apply (degree : ℕ)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree)) :
    identityPlaneBinaryEdge degree
        (relativeTwoCocycleClass identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree) cycle) =
      (identityPlaneLeviCohomologyIso degree).hom
        (groupCohomology.H1π (splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRep degree))
          (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRep degree) cycle)) := by
  exact congrArg (fun cohomology => (identityPlaneLeviCohomologyIso degree).hom cohomology)
    (splitCohomologyEdge_apply identityPlaneSplitting (identityPlaneCoefficientRep degree) cycle)

theorem goodLineBinaryEdge_apply (degree : ℕ) (positive : 0 < degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree)) :
    goodLineBinaryEdge degree positive
        (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep degree) cycle) =
      (goodLineLeviCohomologyIso degree positive).hom
        (groupCohomology.H1π (splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRep degree))
          (splitCocycleEdge goodLineSplitting (goodLineCoefficientRep degree) cycle)) := by
  exact congrArg (fun cohomology => (goodLineLeviCohomologyIso degree positive).hom cohomology)
    (splitCohomologyEdge_apply goodLineSplitting (goodLineCoefficientRep degree) cycle)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
