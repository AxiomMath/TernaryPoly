module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneRestriction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem linearMap_nilpotentAverage {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (projection : V →ₗ[ℂ] W) (operator : Module.End ℂ V)
    (kills : ∀ vector, projection (operator vector) = 0) (cutoff : ℕ) (vector : V) :
    projection (nilpotentExponentialAverage operator (cutoff + 1) vector) = projection vector := by
  have remainder := congrArg (fun value : Module.End ℂ V => projection (value vector))
    (nilpotentExponentialAverage_remainder operator cutoff)
  change projection (nilpotentExponentialAverage operator (cutoff + 1) vector - vector) =
    projection (operator _) at remainder
  rw [map_sub, kills] at remainder
  exact sub_eq_zero.mp remainder

theorem upperRadicalCocyclePair_restrict {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) (coordinate : Fin 2) :
    binaryHomogeneousRestrict degree (upperRadicalCocyclePair degree cycle coordinate) =
      binaryHomogeneousRestrict degree (cycle (radicalLatticeGenerator coordinate)) := by
  have average := linearMap_nilpotentAverage (binaryHomogeneousRestrict degree)
    (upperRadicalGenerator degree coordinate) (binaryHomogeneousRestrict_upperGenerator degree coordinate)
    degree (upperRadicalCocyclePair degree cycle coordinate)
  exact average.symm.trans (congrArg (binaryHomogeneousRestrict degree) (upperRadicalCocyclePair_average cycle coordinate))

/-- On upper-radical H1 the binary coordinate only uses the two generator values. -/
theorem upperRadicalCocycleCoordinate_value {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    (upperRadicalCocycleCoordinate degree cycle).val = (degree + 1 : ℂ)⁻¹ •
      (X 0 * binaryPolynomialRestrict (cycle radicalLatticeFirst).val +
        X 1 * binaryPolynomialRestrict (cycle radicalLatticeSecond).val) := by
  have first := congrArg Subtype.val (upperRadicalCocyclePair_restrict cycle 0)
  have second := congrArg Subtype.val (upperRadicalCocyclePair_restrict cycle 1)
  change binaryPolynomialRestrict (upperRadicalCocyclePair degree cycle 0).val =
    binaryPolynomialRestrict (cycle radicalLatticeFirst).val at first
  change binaryPolynomialRestrict (upperRadicalCocyclePair degree cycle 1).val =
    binaryPolynomialRestrict (cycle radicalLatticeSecond).val at second
  change (degree + 1 : ℂ)⁻¹ •
    (X 0 * binaryPolynomialRestrict (upperRadicalCocyclePair degree cycle 0).val +
      X 1 * binaryPolynomialRestrict (upperRadicalCocyclePair degree cycle 1).val) = _
  rw [first, second]

def identityPlaneBinaryEdgeCycle (degree : ℕ) :
    relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree) →ₗ[ℂ]
      groupCohomology.cocycles₁ (arithmeticBinaryRep (degree + 1) (-1)) :=
  (groupCohomology.mapCocycles₁ (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
    (identityPlaneRadicalCoordinateIso degree).hom).hom.comp
      (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRep degree))

def identityPlaneRadicalEdgeCycle (degree : ℕ)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree) :=
  splitEdgeCycle identityPlaneSplitting (identityPlaneCoefficientRep degree) matrix cycle

theorem identityPlaneBinaryEdgeCycle_apply (degree : ℕ)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    identityPlaneBinaryEdgeCycle degree cycle matrix =
      upperRadicalCocycleCoordinate degree (identityPlaneRadicalEdgeCycle degree cycle matrix) := by
  have equality := groupCohomology.mapCocycles₁_comp_i_apply
    (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ)) (identityPlaneRadicalCoordinateIso degree).hom
    (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRep degree) cycle)
  have value := congrFun equality matrix
  change identityPlaneBinaryEdgeCycle degree cycle matrix =
    upperRadicalH1Coordinate degree
      (groupCohomology.H1π (upperRadicalLatticeRep degree)
        (splitEdgeCycle identityPlaneSplitting (identityPlaneCoefficientRep degree) matrix cycle)) at value
  exact value.trans (upperRadicalH1Coordinate_apply _)

theorem identityPlaneBinaryEdgeCycle_H1 (degree : ℕ)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree)) :
    groupCohomology.H1π (arithmeticBinaryRep (degree + 1) (-1)) (identityPlaneBinaryEdgeCycle degree cycle) =
      identityPlaneBinaryEdge degree
        (relativeTwoCocycleClass identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree) cycle) := by
  rw [identityPlaneBinaryEdge_apply]
  change groupCohomology.H1π (arithmeticBinaryRep (degree + 1) (-1))
      (groupCohomology.mapCocycles₁ (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
        (identityPlaneRadicalCoordinateIso degree).hom
        (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRep degree) cycle)) =
    groupCohomology.map (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
      (identityPlaneRadicalCoordinateIso degree).hom 1
      (groupCohomology.H1π (splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRep degree))
        (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRep degree) cycle))
  exact (groupCohomology.H1π_comp_map_apply
    (A := splitRadicalH1Representation identityPlaneSplitting (identityPlaneCoefficientRep degree))
    (B := arithmeticBinaryRep (degree + 1) (-1)) (MonoidHom.id (GeneralLinearGroup (Fin 2) ℤ))
    (identityPlaneRadicalCoordinateIso degree).hom
    (splitCocycleEdge identityPlaneSplitting (identityPlaneCoefficientRep degree) cycle)).symm

theorem identityPlaneSplitEdgeCycle_apply (degree : ℕ)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    identityPlaneRadicalEdgeCycle degree cycle matrix radical =
      cycle.val (identityPlaneLeviSection matrix, identityPlaneRadicalInclusion (upperLeviLatticeInput matrix radical)) -
        cycle.val (identityPlaneRadicalInclusion radical, identityPlaneLeviSection matrix) := by
  exact (splitEdgeCycle_apply identityPlaneSplitting (identityPlaneCoefficientRep degree) matrix cycle radical).trans
    (congrArg (fun input : RadicalLattice =>
      cycle.val (identityPlaneLeviSection matrix, identityPlaneRadicalInclusion input) -
        cycle.val (identityPlaneRadicalInclusion radical, identityPlaneLeviSection matrix))
      (identityPlaneSplitting_inverse_action matrix radical))

theorem identityPlaneBinaryEdgeCycle_value (degree : ℕ)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (identityPlaneBinaryEdgeCycle degree cycle matrix).val = (degree + 1 : ℂ)⁻¹ •
      (X 0 * binaryPolynomialRestrict
        (cycle.val (identityPlaneLeviSection matrix, identityPlaneRadicalInclusion (upperLeviLatticeInput matrix radicalLatticeFirst)) -
          cycle.val (identityPlaneRadicalInclusion radicalLatticeFirst, identityPlaneLeviSection matrix)).val +
       X 1 * binaryPolynomialRestrict
        (cycle.val (identityPlaneLeviSection matrix, identityPlaneRadicalInclusion (upperLeviLatticeInput matrix radicalLatticeSecond)) -
          cycle.val (identityPlaneRadicalInclusion radicalLatticeSecond, identityPlaneLeviSection matrix)).val) := by
  rw [identityPlaneBinaryEdgeCycle_apply]
  have formula := upperRadicalCocycleCoordinate_value
    (identityPlaneRadicalEdgeCycle degree cycle matrix)
  have first := congrArg (fun polynomial : HomogeneousPoly degree => binaryPolynomialRestrict polynomial.val)
    (identityPlaneSplitEdgeCycle_apply degree cycle matrix radicalLatticeFirst)
  have second := congrArg (fun polynomial : HomogeneousPoly degree => binaryPolynomialRestrict polynomial.val)
    (identityPlaneSplitEdgeCycle_apply degree cycle matrix radicalLatticeSecond)
  rw [first, second] at formula
  exact formula

theorem identityPlaneFullBinaryEdge_relative (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree)) :
    identityPlaneFullBinaryEdge degree positive odd (groupCohomology.H2π (identityPlaneCoefficientRep degree) cycle.val) =
      groupCohomology.H1π (arithmeticBinaryRep (degree + 1) (-1)) (identityPlaneBinaryEdgeCycle degree cycle) := by
  rw [identityPlaneBinaryEdgeCycle_H1]
  rfl

/-- The remaining vanishing condition is an ordinary binary-polynomial coboundary on integral GL2. -/
theorem identityPlaneRelativeH2_zero_iff_binaryPotential (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree)) :
    groupCohomology.H2π (identityPlaneCoefficientRep degree) cycle.val = 0 ↔
      ∃ potential : Binary.HomogeneousPoly (degree + 1), ∀ matrix : GeneralLinearGroup (Fin 2) ℤ,
        identityPlaneBinaryEdgeCycle degree cycle matrix =
          Binary.homogeneousAction (degree + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) potential - potential := by
  rw [← identityPlaneFullBinaryEdge_zero_iff degree positive odd, identityPlaneFullBinaryEdge_relative,
    groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨potential, equality⟩
    exact ⟨potential, fun matrix => (congrFun equality matrix).symm⟩
  · rintro ⟨potential, equality⟩
    exact ⟨potential, funext (fun matrix => (equality matrix).symm)⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
