module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.BinaryNormalForm

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Homogeneous Matrix MvPolynomial

def badRadical (first second : ℤ) : badLineSubgroup :=
  ⟨(integralRadical first second).val, (integralRadical first second).property, ⟨rfl, rfl⟩⟩

theorem badRadical_val (first second : ℤ) :
    (badRadical first second).val = Adelic.lineUnipotent (first : ℚ) (second : ℚ) :=
  integralRadical_val first second

theorem badRadical_mul (first second third fourth : ℤ) :
    badRadical first second * badRadical third fourth =
      badRadical (first + third) (second + fourth) := by
  apply Subtype.ext
  change (integralRadical first second).val * (integralRadical third fourth).val =
    (integralRadical (first + third) (second + fourth)).val
  exact congrArg (fun matrix : rationalLevel => matrix.val)
    (integralRadical_mul first second third fourth)

theorem lineClass_zero_exists_binaryPrimitive {degree : ℕ} (degree_positive : 0 < degree)
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (pure : PureMixedBadLine cocycle)
    (zero_class : (globalCoordinates degree trivialCharacter cocycle).2 = 0) :
    ∃ (primitive : badLineSubgroup → HomogeneousPoly degree)
      (first_binary second_binary : HomogeneousPoly degree),
      (∀ first second : badLineSubgroup,
        cocycle.val.val ![1, first.val, (first * second).val] =
          rationalCoefficientComponent degree trivialCharacter first.val (primitive second) -
            primitive (first * second) + primitive first) ∧
      pderiv 0 first_binary.val = 0 ∧ pderiv 0 second_binary.val = 0 ∧
      ∀ first second : ℤ,
        primitive (badRadical first second) = first • first_binary + second • second_binary := by
  obtain ⟨primitive, differential, radical_crossed⟩ :=
    lineClass_zero_radicalCocycle cocycle pure zero_class
  have crossed (first second third fourth : ℤ) :
      primitive (badRadical (first + third) (second + fourth)) =
        rationalCoefficientComponent degree trivialCharacter (integralRadical first second).val
          (primitive (badRadical third fourth)) + primitive (badRadical first second) := by
    rw [← badRadical_mul]
    exact radical_crossed first second third fourth
  obtain ⟨first_binary, second_binary, correction, first_derivative, second_derivative, normal⟩ :=
    radicalCrossed_binary_normalForm degree_positive
      (fun first second => primitive (badRadical first second)) crossed
  let corrected (matrix : badLineSubgroup) : HomogeneousPoly degree := primitive matrix -
    (rationalCoefficientComponent degree trivialCharacter matrix.val correction - correction)
  refine ⟨corrected, first_binary, second_binary, ?_, first_derivative, second_derivative, ?_⟩
  · intro first second
    rw [differential]
    simp only [corrected, map_sub, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    abel
  · intro first second
    change primitive (badRadical first second) -
      (rationalCoefficientComponent degree trivialCharacter (badRadical first second).val correction -
        correction) = _
    rw [normal]
    change first • first_binary + second • second_binary +
      (rationalCoefficientComponent degree trivialCharacter (integralRadical first second).val correction -
        correction) -
      (rationalCoefficientComponent degree trivialCharacter (integralRadical first second).val correction -
        correction) = _
    abel

def radicalContractionMap (degree : ℕ) :
    (HomogeneousPoly degree × HomogeneousPoly degree) →ₗ[ℂ] Poly where
  toFun pair := X 2 * bernoulliOperator degree (X 1) pair.1.val -
    X 1 * bernoulliOperator degree (X 2) pair.2.val
  map_add' first second := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, bernoulliOperator_add]
    ring
  map_smul' scalar pair := by
    change X 2 * bernoulliOperator degree (X 1) (scalar • pair.1.val) -
      X 1 * bernoulliOperator degree (X 2) (scalar • pair.2.val) = _
    rw [bernoulliOperator_smul, bernoulliOperator_smul]
    simp only [MvPolynomial.smul_eq_C_mul, RingHom.id_apply]
    ring

theorem radicalContractionMap_coboundary (degree : ℕ) (primitive : HomogeneousPoly degree) :
    radicalContractionMap degree
      (rationalCoefficientComponent degree trivialCharacter (Adelic.lineUnipotent 1 0) primitive -
        primitive,
       rationalCoefficientComponent degree trivialCharacter (Adelic.lineUnipotent 0 1) primitive -
        primitive) = 0 :=
  radicalContraction_groupCoboundary degree primitive

theorem mixedBernoulliCoordinate_of_binaryPrimitive {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : badLineSubgroup → HomogeneousPoly degree)
    (differential : ∀ first second : badLineSubgroup,
      cocycle.val.val ![1, first.val, (first * second).val] =
        rationalCoefficientComponent degree trivialCharacter first.val (primitive second) -
          primitive (first * second) + primitive first)
    (first_binary second_binary : HomogeneousPoly degree)
    (normal : ∀ first second : ℤ,
      primitive (badRadical first second) = first • first_binary + second • second_binary)
    (levi : badLineSubgroup) (first second third fourth : ℤ)
    (conjugate_first : levi⁻¹ * badRadical 1 0 * levi = badRadical first second)
    (conjugate_second : levi⁻¹ * badRadical 0 1 * levi = badRadical third fourth) :
    mixedBernoulliCoordinate cocycle levi.val =
      radicalContractionMap degree
        (rationalCoefficientComponent degree trivialCharacter levi.val
          (first • first_binary + second • second_binary) - first_binary,
         rationalCoefficientComponent degree trivialCharacter levi.val
          (third • first_binary + fourth • second_binary) - second_binary) := by
  have first_value := mixedBarEdge_of_linePrimitive cocycle primitive differential levi (badRadical 1 0)
  have second_value := mixedBarEdge_of_linePrimitive cocycle primitive differential levi (badRadical 0 1)
  rw [conjugate_first, normal, normal] at first_value
  rw [conjugate_second, normal, normal] at second_value
  simp only [one_smul, zero_smul, add_zero, zero_add, badRadical_val,
    Int.cast_one, Int.cast_zero] at first_value second_value
  let values : HomogeneousPoly degree × HomogeneousPoly degree :=
    (rationalCoefficientComponent degree trivialCharacter levi.val
        (first • first_binary + second • second_binary) - first_binary,
     rationalCoefficientComponent degree trivialCharacter levi.val
        (third • first_binary + fourth • second_binary) - second_binary)
  let coboundary : HomogeneousPoly degree × HomogeneousPoly degree :=
    (rationalCoefficientComponent degree trivialCharacter (Adelic.lineUnipotent 1 0)
        (primitive levi) - primitive levi,
     rationalCoefficientComponent degree trivialCharacter (Adelic.lineUnipotent 0 1)
        (primitive levi) - primitive levi)
  have value : mixedBernoulliCoordinate cocycle levi.val =
      radicalContractionMap degree (values - coboundary) := by
    rw [mixedBernoulliCoordinate, first_value, second_value]
    rfl
  rw [value, map_sub, radicalContractionMap_coboundary, sub_zero]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
