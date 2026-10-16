module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteCuspIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteAdeleUnit_mul (first second : FiniteAdelesˣ) :
    finiteAdeleUnit (first * second) = finiteAdeleUnit first * finiteAdeleUnit second := by
  apply Units.ext
  apply Prod.ext <;> simp [finiteAdeleUnit]

theorem generalLinearGroup_det_map {dimension : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (matrix : GeneralLinearGroup (Fin dimension) R) :
    GeneralLinearGroup.det (GeneralLinearGroup.map hom matrix) =
      Units.map hom.toMonoidHom (GeneralLinearGroup.det matrix) := by
  apply Units.ext
  exact (hom.map_det matrix.val).symm

theorem planeInduction_det_unit {R : Type*} [CommRing R]
    (first second : R) (scalar : Rˣ) (block : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup.det (planeUnipotent first second * (planeLevi 1 scalar * planeLevi block 1)) =
      GeneralLinearGroup.det block * scalar := by
  apply Units.ext
  simp only [GeneralLinearGroup.val_det_apply, Matrix.det_mul, Units.val_mul]
  simp [planeUnipotent, planeLevi, planeBlock, Matrix.det_fin_three, Matrix.det_fin_two, mul_comm]

theorem standardGoodLineFiniteArgument_val (finite : FiniteAwayThree × FiniteAwayThree) :
    (standardGoodLineFiniteArgument finite).val = !![0,1,0;1,0,0;finite.2.val,finite.1.val,1] := by
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [standardGoodLineFiniteArgument, weyl, lineUnipotent, upperUnipotent, rationalFinite, rationalGoodLine,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem standardGoodLineFiniteArgument_det (finite : FiniteAwayThree × FiniteAwayThree) :
    GeneralLinearGroup.det (standardGoodLineFiniteArgument finite) = -1 := by
  apply Units.ext
  change (standardGoodLineFiniteArgument finite).val.det = -1
  rw [standardGoodLineFiniteArgument_val]
  simp [Matrix.det_fin_three]

theorem finitePlaneLevelCoordinates_det (finite : FiniteGL) (coords : FinitePlaneLevelCoordinates finite) :
    GeneralLinearGroup.det finite = GeneralLinearGroup.det coords.block * coords.scalar *
      GeneralLinearGroup.det coords.compact.val := by
  have factors : finite = (planeUnipotent coords.first coords.second *
      (planeLevi 1 coords.scalar * planeLevi coords.block 1)) * coords.compact.val := by
    calc
      finite = planeUnipotent coords.first coords.second *
          (planeLevi 1 coords.scalar * (planeLevi coords.block 1 * coords.compact.val)) := coords.factorization
      _ = _ := by simp only [mul_assoc]
  have equality := congrArg GeneralLinearGroup.det factors
  rw [map_mul, planeInduction_det_unit] at equality
  exact equality

theorem standardGoodLineFiniteCoordinates_normPower (finite : FiniteAwayThree × FiniteAwayThree) (exponent : ℂ) :
    normPower (finiteAdeleUnit (GeneralLinearGroup.det (standardGoodLineFiniteCoordinates finite).block *
      (standardGoodLineFiniteCoordinates finite).scalar)) exponent = 1 := by
  let coords := standardGoodLineFiniteCoordinates finite
  have compact_norm : normPower (finiteAdeleUnit (GeneralLinearGroup.det coords.compact.val)) exponent = 1 := by
    rw [← finiteLevelIntegralLift_spec coords.compact, generalLinearGroup_det_map]
    exact normPower_finiteIntegralUnit _ _
  have matrix_norm : normPower (finiteAdeleUnit (GeneralLinearGroup.det (standardGoodLineFiniteArgument finite))) exponent = 1 := by
    rw [standardGoodLineFiniteArgument_det]
    have minus_one : Units.map integralEmbedding.toMonoidHom (-1 : IntegralAdelesˣ) = -1 := by
      apply Units.ext
      simp
    rw [← minus_one]
    exact normPower_finiteIntegralUnit (-1) exponent
  have equality := congrArg (fun unit : FiniteAdelesˣ => normPower (finiteAdeleUnit unit) exponent)
    (finitePlaneLevelCoordinates_det (standardGoodLineFiniteArgument finite) coords)
  rw [finiteAdeleUnit_mul, normPower_mul, compact_norm, mul_one, matrix_norm] at equality
  exact equality.symm

/-- The scalar block cancels against the binary determinant for the determinant-minus-one standard argument. -/
theorem standardGoodLineFiniteCuspWeight_det (degree : ℕ) (parameter : ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    standardGoodLineFiniteCuspWeight degree parameter finite =
      normPower (finiteAdeleUnit (GeneralLinearGroup.det (standardGoodLineFiniteCoordinates finite).block))
        ((degree : ℂ) / 2 + 3 + parameter) := by
  let coords := standardGoodLineFiniteCoordinates finite
  let exponent := inductionExponent .plane parameter
  have negative : -(2 * exponent) = -2 * exponent := by ring
  have product : normPower (finiteAdeleUnit coords.scalar * finiteAdeleUnit (GeneralLinearGroup.det coords.block))
      (-2 * exponent) = 1 := by
    rw [← finiteAdeleUnit_mul, mul_comm]
    exact standardGoodLineFiniteCoordinates_normPower finite (-2 * exponent)
  have cancellation := normPower_mul_neg_cancel (finiteAdeleUnit coords.scalar)
    (finiteAdeleUnit (GeneralLinearGroup.det coords.block)) (2 * exponent)
  rw [negative, product, mul_one] at cancellation
  have total : binaryInductionExponent degree .plane parameter + 2 * exponent = (degree : ℂ) / 2 + 3 + parameter := by
    unfold binaryInductionExponent exponent inductionExponent
    ring
  change normPower (finiteAdeleUnit (GeneralLinearGroup.det coords.block)) (binaryInductionExponent degree .plane parameter) *
    normPower (finiteAdeleUnit coords.scalar) (-2 * exponent) = _
  rw [← cancellation, ← normPower_add_exponents, total]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
