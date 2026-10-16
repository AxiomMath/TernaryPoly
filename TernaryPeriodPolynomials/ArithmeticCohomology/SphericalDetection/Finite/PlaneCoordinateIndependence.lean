module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PlaneParabolicBinaryProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finitePlaneInductionCoordinates_parabolic (finite : FiniteGL) (coords : FinitePlaneInductionCoordinates finite) :
    finite = (planeInductionParabolic coords.first coords.second coords.scalar coords.block).val *
      GeneralLinearGroup.map integralEmbedding coords.compact := by
  change finite = (planeUnipotent coords.first coords.second * (planeLevi 1 coords.scalar * planeLevi coords.block 1)) * _
  simpa only [mul_assoc] using coords.factorization

theorem finitePlaneInductionBlocks_same_coset (finite : FiniteGL)
    (first second : FinitePlaneInductionCoordinates finite) :
    first.block⁻¹ * second.block ∈ finiteIntegralGLLevel 2 := by
  let first_parabolic := planeInductionParabolic first.first first.second first.scalar first.block
  let second_parabolic := planeInductionParabolic second.first second.second second.scalar second.block
  have first_factors : finite = first_parabolic.val * GeneralLinearGroup.map integralEmbedding first.compact :=
    finitePlaneInductionCoordinates_parabolic finite first
  have second_factors : finite = second_parabolic.val * GeneralLinearGroup.map integralEmbedding second.compact :=
    finitePlaneInductionCoordinates_parabolic finite second
  have transition : (first_parabolic⁻¹ * second_parabolic).val =
      GeneralLinearGroup.map integralEmbedding first.compact * (GeneralLinearGroup.map integralEmbedding second.compact)⁻¹ := by
    change first_parabolic.val⁻¹ * second_parabolic.val = _
    calc
      first_parabolic.val⁻¹ * second_parabolic.val =
          first_parabolic.val⁻¹ * (second_parabolic.val * GeneralLinearGroup.map integralEmbedding second.compact) *
            (GeneralLinearGroup.map integralEmbedding second.compact)⁻¹ := by group
      _ = first_parabolic.val⁻¹ * (first_parabolic.val * GeneralLinearGroup.map integralEmbedding first.compact) *
            (GeneralLinearGroup.map integralEmbedding second.compact)⁻¹ :=
        congrArg (fun value : FiniteGL => first_parabolic.val⁻¹ * value *
          (GeneralLinearGroup.map integralEmbedding second.compact)⁻¹) (second_factors.symm.trans first_factors)
      _ = _ := by group
  have integral : (first_parabolic⁻¹ * second_parabolic).val ∈ finiteIntegralGLLevel 3 := by
    rw [transition]
    exact (finiteIntegralGLLevel 3).mul_mem ⟨first.compact, rfl⟩
      ((finiteIntegralGLLevel 3).inv_mem ⟨second.compact, rfl⟩)
  have projected := planeParabolicBinary_finite_integral (first_parabolic⁻¹ * second_parabolic) integral
  simpa only [map_mul, map_inv, first_parabolic, second_parabolic, planeParabolicBinary_induction] using projected

theorem finitePlaneInductionBlocks_exists_integral (finite : FiniteGL)
    (first second : FinitePlaneInductionCoordinates finite) :
    ∃ integral : GeneralLinearGroup (Fin 2) IntegralAdeles,
      second.block = first.block * GeneralLinearGroup.map integralEmbedding integral := by
  obtain ⟨integral, equality⟩ := finitePlaneInductionBlocks_same_coset finite first second
  refine ⟨integral, ?_⟩
  rw [equality, mul_inv_cancel_left]

theorem finitePlaneInductionBlocks_normPower (finite : FiniteGL)
    (first second : FinitePlaneInductionCoordinates finite) (exponent : ℂ) :
    normPower (finiteAdeleUnit (GeneralLinearGroup.det first.block)) exponent =
      normPower (finiteAdeleUnit (GeneralLinearGroup.det second.block)) exponent := by
  obtain ⟨integral, equality⟩ := finitePlaneInductionBlocks_exists_integral finite first second
  rw [equality, map_mul, finiteAdeleUnit_mul, normPower_mul, generalLinearGroup_det_map]
  have normalized : normPower (finiteAdeleUnit
      (Units.map integralEmbedding.toMonoidHom (GeneralLinearGroup.det integral))) exponent = 1 :=
    normPower_finiteIntegralUnit _ _
  rw [normalized, mul_one]

theorem cuspSpherical_realize_right (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (block : BinaryFiniteGL)
    (integral : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    cusp.realize vector (atFinite (block * GeneralLinearGroup.map integralEmbedding integral)) =
      cusp.realize vector (atFinite block) := by
  have fixed : (⟨cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding integral)) vector.val,
      cusp.smooth_stable _ vector.val vector.property⟩ : cusp.smooth) = vector := Subtype.ext (spherical integral)
  rw [atFinite_mul, ← cusp.equivariant, fixed]

def finiteSphericalPlaneValue (cusp : CuspidalRepresentation) (vector : cusp.smooth) (exponent : ℂ)
    {finite : FiniteGL} (coords : FinitePlaneInductionCoordinates finite) : ℂ :=
  normPower (finiteAdeleUnit (GeneralLinearGroup.det coords.block)) exponent *
    cusp.realize vector (atFinite coords.block)

/-- Both the determinant weight and the spherical cusp value are unchanged by the finite Iwasawa choice. -/
theorem finiteSphericalPlaneValue_independent (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (exponent : ℂ) (finite : FiniteGL)
    (first second : FinitePlaneInductionCoordinates finite) :
    finiteSphericalPlaneValue cusp vector exponent first = finiteSphericalPlaneValue cusp vector exponent second := by
  have weight := finitePlaneInductionBlocks_normPower finite first second exponent
  obtain ⟨integral, equality⟩ := finitePlaneInductionBlocks_exists_integral finite first second
  unfold finiteSphericalPlaneValue
  rw [weight, equality, cuspSpherical_realize_right cusp vector spherical]

theorem goodLineFiniteVectorIntegral_eq_coordinates (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (coordinates : ∀ finite : FiniteAwayThree × FiniteAwayThree,
      FinitePlaneInductionCoordinates (standardGoodLineFiniteArgument finite)) :
    goodLineFiniteVectorIntegral degree cusp parameter vector =
      ∫ finite : FiniteAwayThree × FiniteAwayThree,
        finiteSphericalPlaneValue cusp vector ((degree : ℂ) / 2 + 3 + parameter) (coordinates finite)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  apply integral_congr_ae
  filter_upwards [] with finite
  rw [standardGoodLineFiniteCuspWeight_det]
  exact finiteSphericalPlaneValue_independent cusp vector spherical _ _
    (finitePlaneLevelInductionCoordinates _ (standardGoodLineFiniteCoordinates finite)) (coordinates finite)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
