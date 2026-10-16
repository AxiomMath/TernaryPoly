module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneWeight
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IntegralAdelicNorm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem combineGL_mul {dimension : ℕ}
    (first_real second_real : GeneralLinearGroup (Fin dimension) ℝ)
    (first_finite second_finite : GeneralLinearGroup (Fin dimension) FiniteAdeles) :
    combineGL (first_real * second_real) (first_finite * second_finite) =
      combineGL first_real first_finite * combineGL second_real second_finite := by
  apply Units.ext
  funext row column
  apply Prod.ext <;>
    simp [combineGL, pairMatrix, Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum]

theorem combineGL_planeUnipotent (real_first real_second : ℝ) (finite_first finite_second : FiniteAdeles) :
    combineGL (planeUnipotent real_first real_second) (planeUnipotent finite_first finite_second) =
      planeUnipotent (real_first, finite_first) (real_second, finite_second) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem combineGL_planeLevi (real_block : BinaryRealGL) (real_scalar : ℝˣ)
    (finite_block : BinaryFiniteGL) (finite_scalar : FiniteAdelesˣ) :
    combineGL (planeLevi real_block real_scalar) (planeLevi finite_block finite_scalar) =
      planeLevi (combineGL real_block finite_block) (realAdeleUnit real_scalar * finiteAdeleUnit finite_scalar) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [combineGL, pairMatrix, planeLevi, planeBlock, realAdeleUnit, finiteAdeleUnit]

theorem binary_det_combineGL (real : BinaryRealGL) (finite : BinaryFiniteGL) :
    GeneralLinearGroup.det (combineGL real finite) =
      realAdeleUnit (GeneralLinearGroup.det real) * finiteAdeleUnit (GeneralLinearGroup.det finite) := by
  apply Units.ext
  apply Prod.ext <;>
    simp [GeneralLinearGroup.val_det_apply, combineGL, pairMatrix, realAdeleUnit, finiteAdeleUnit, Matrix.det_fin_two]

structure FinitePlaneInductionCoordinates (argument : FiniteGL) where
  first : FiniteAdeles
  second : FiniteAdeles
  scalar : FiniteAdelesˣ
  block : BinaryFiniteGL
  compact : GeneralLinearGroup (Fin 3) IntegralAdeles
  factorization : argument = planeUnipotent first second *
    (planeLevi 1 scalar * (planeLevi block 1 * GeneralLinearGroup.map integralEmbedding compact))

def finitePlaneInductionCoordinates (argument : FiniteGL) : FinitePlaneInductionCoordinates argument :=
  Classical.choice (by
    obtain ⟨parabolic, compact, factors⟩ := finiteGL_parabolic_compact_factorization argument
    obtain ⟨first, second, scalar, block, parabolic_factors⟩ := planeParabolic_exists_decomposition parabolic
    exact ⟨⟨first, second, scalar, block, compact,
      factors.trans (by rw [parabolic_factors, mul_assoc, mul_assoc])⟩⟩)

def finitePlaneFlatWeight (parameter : ℂ) (argument : FiniteGL) : ℂ :=
  normPower (finiteAdeleUnit (GeneralLinearGroup.det (finitePlaneInductionCoordinates argument).block))
      (inductionExponent .plane parameter) *
    normPower (finiteAdeleUnit (finitePlaneInductionCoordinates argument).scalar)
      (-2 * inductionExponent .plane parameter)

theorem finitePlaneFlatWeight_ne_zero (parameter : ℂ) (argument : FiniteGL) :
    finitePlaneFlatWeight parameter argument ≠ 0 := mul_ne_zero (normPower_ne_zero _ _) (normPower_ne_zero _ _)

theorem finitePlaneFlatWeight_endpoint (argument : FiniteGL) :
    finitePlaneFlatWeight cohomologicalPoint argument = 1 := by
  have exponent : inductionExponent .plane cohomologicalPoint = 0 := by
    unfold inductionExponent cohomologicalPoint
    ring
  simp [finitePlaneFlatWeight, exponent, normPower_zero_exponent]

theorem flatSection_value_real_finite_coordinates {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → AdelicGL → ℂ) (section_mem : IsFlatSection data flat)
    (parameter : ℂ) (real : RealGL3) (finite : FiniteGL) (coords : FinitePlaneInductionCoordinates finite) :
    flat parameter (combineGL real finite) =
      (realPlaneFlatWeight parameter real *
        (normPower (finiteAdeleUnit (GeneralLinearGroup.det coords.block)) (inductionExponent .plane parameter) *
          normPower (finiteAdeleUnit coords.scalar) (-2 * inductionExponent .plane parameter))) *
        flat cohomologicalPoint (combineGL real finite) := by
  obtain ⟨parabolic, compact, orthogonal, factors⟩ := realGL_parabolic_compact_factorization real
  obtain ⟨first, second, scalar, block, parabolic_factors⟩ := planeParabolic_exists_decomposition parabolic
  have real_factors : real = planeUnipotent first second * (planeLevi 1 scalar * (planeLevi block 1 * compact)) := by
    rw [factors, parabolic_factors, mul_assoc, mul_assoc]
  let joined_compact := combineGL compact (GeneralLinearGroup.map integralEmbedding coords.compact)
  have joined_compact_mem : inMaximalCompact joined_compact := by
    constructor
    · exact (realGroup_combineGL _ _ ▸ orthogonal)
    · exact ⟨coords.compact, (finiteGroup_combineGL _ _).symm⟩
  have combine_one : combineGL (1 : BinaryRealGL) (1 : BinaryFiniteGL) = 1 := by
    apply Units.ext
    funext row column
    fin_cases row <;> fin_cases column <;> rfl
  have scalar_one : realAdeleUnit 1 * finiteAdeleUnit 1 = 1 := by
    apply Units.ext
    simp [realAdeleUnit, finiteAdeleUnit]
  have joined_factors : combineGL real finite =
      planeUnipotent (first, coords.first) (second, coords.second) *
        (planeLevi 1 (realAdeleUnit scalar * finiteAdeleUnit coords.scalar) *
          (planeLevi (combineGL block coords.block) 1 * joined_compact)) := by
    conv_lhs => rw [real_factors, coords.factorization]
    rw [combineGL_mul, combineGL_mul, combineGL_mul, combineGL_planeUnipotent,
      combineGL_planeLevi, combineGL_planeLevi, combine_one, scalar_one]
  have value := flatSection_value_inductionCoordinates data flat section_mem parameter
    (first, coords.first) (second, coords.second)
    (realAdeleUnit scalar * finiteAdeleUnit coords.scalar) (combineGL block coords.block)
    joined_compact joined_compact_mem
  rw [← joined_factors, binary_det_combineGL, normPower_mul, normPower_mul] at value
  have real_weight := realPlaneFlatWeight_inductionCoordinates parameter first second scalar block compact orthogonal
  rw [← real_factors] at real_weight
  rw [value, real_weight]
  ring

theorem flatSection_value_real_finite {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → AdelicGL → ℂ) (section_mem : IsFlatSection data flat)
    (parameter : ℂ) (real : RealGL3) (finite : FiniteGL) :
    flat parameter (combineGL real finite) =
      (realPlaneFlatWeight parameter real * finitePlaneFlatWeight parameter finite) *
        flat cohomologicalPoint (combineGL real finite) :=
  flatSection_value_real_finite_coordinates data flat section_mem parameter real finite
    (finitePlaneInductionCoordinates finite)

def finiteIntegralPlaneCoordinates (compact : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    FinitePlaneInductionCoordinates (GeneralLinearGroup.map integralEmbedding compact) where
  first := 0
  second := 0
  scalar := 1
  block := 1
  compact := compact
  factorization := by
    have radical : planeUnipotent (0 : FiniteAdeles) 0 = 1 := by
      apply Units.ext
      funext row column
      fin_cases row <;> fin_cases column <;> rfl
    have levi : planeLevi (1 : BinaryFiniteGL) 1 = 1 := (planeLeviHom FiniteAdeles).map_one
    rw [radical, levi, one_mul, one_mul, one_mul]

theorem flatSection_value_real_integral {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → AdelicGL → ℂ) (section_mem : IsFlatSection data flat)
    (parameter : ℂ) (real : RealGL3) (compact : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    flat parameter (combineGL real (GeneralLinearGroup.map integralEmbedding compact)) =
      realPlaneFlatWeight parameter real *
        flat cohomologicalPoint (combineGL real (GeneralLinearGroup.map integralEmbedding compact)) := by
  have unit : finiteAdeleUnit 1 = 1 := by
    apply Units.ext
    rfl
  simpa only [finiteIntegralPlaneCoordinates, map_one, unit, normPower_one, mul_one] using
    flatSection_value_real_finite_coordinates data flat section_mem parameter real
      (GeneralLinearGroup.map integralEmbedding compact) (finiteIntegralPlaneCoordinates compact)

theorem polynomialFlatSection_value_real_finite {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (parameter : ℂ) (vertices : Fin 3 → RealGL3) (real : RealGL3) (finite : FiniteGL) :
    flat parameter vertices (combineGL real finite) =
      (realPlaneFlatWeight parameter real * finitePlaneFlatWeight parameter finite) •
        flat cohomologicalPoint vertices (combineGL real finite) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using
    flatSection_value_real_finite data _ (sections vertices monomial) parameter real finite

theorem polynomialFlatSection_value_real_integral {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (parameter : ℂ) (vertices : Fin 3 → RealGL3) (real : RealGL3)
    (compact : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    flat parameter vertices (combineGL real (GeneralLinearGroup.map integralEmbedding compact)) =
      realPlaneFlatWeight parameter real •
        flat cohomologicalPoint vertices (combineGL real (GeneralLinearGroup.map integralEmbedding compact)) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using
    flatSection_value_real_integral data _ (sections vertices monomial) parameter real compact

end TernaryPeriodPolynomials.SphericalDetection.Helpers
