module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CuspidalValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem atInfinity_mul {dimension : ℕ}
    (first second : GeneralLinearGroup (Fin dimension) ℝ) :
    atInfinity (first * second) = atInfinity first * atInfinity second := by
  apply Units.ext
  funext row column
  apply Prod.ext
  · simp [atInfinity, combineGL, pairMatrix, Matrix.mul_apply, Prod.fst_sum]
  · simp only [atInfinity, combineGL, pairMatrix, GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Prod.snd_sum, Prod.snd_mul, GeneralLinearGroup.coe_one]
    simp only [← Matrix.mul_apply, one_mul]

def atInfinityMonoidHom (dimension : ℕ) :
    GeneralLinearGroup (Fin dimension) ℝ →* GeneralLinearGroup (Fin dimension) Adeles where
  toFun := atInfinity
  map_one' := atInfinity_one
  map_mul' := atInfinity_mul

theorem atInfinity_inv {dimension : ℕ} (matrix : GeneralLinearGroup (Fin dimension) ℝ) :
    atInfinity matrix⁻¹ = (atInfinity matrix)⁻¹ := map_inv (atInfinityMonoidHom dimension) matrix

theorem atInfinity_commute_atFinite {dimension : ℕ}
    (real : GeneralLinearGroup (Fin dimension) ℝ)
    (finite : GeneralLinearGroup (Fin dimension) FiniteAdeles) :
    Commute (atInfinity real) (atFinite finite) := by
  apply Units.ext
  funext row column
  apply Prod.ext
  · simp only [atInfinity, atFinite, combineGL, pairMatrix, GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Prod.fst_sum, Prod.fst_mul, GeneralLinearGroup.coe_one]
    simp only [← Matrix.mul_apply, mul_one, one_mul]
  · simp only [atInfinity, atFinite, combineGL, pairMatrix, GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Prod.snd_sum, Prod.snd_mul, GeneralLinearGroup.coe_one]
    simp only [← Matrix.mul_apply, mul_one, one_mul]

theorem atInfinity_continuous {dimension : ℕ} :
    Continuous (atInfinity (m := dimension)) := by
  have matrix_continuous : Continuous
      (fun matrix : GeneralLinearGroup (Fin dimension) ℝ => matrix.val) := Units.continuous_val
  have inverse_continuous : Continuous
      (fun matrix : GeneralLinearGroup (Fin dimension) ℝ => matrix⁻¹.val) :=
    matrix_continuous.comp continuous_inv
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    change Continuous (fun matrix : GeneralLinearGroup (Fin dimension) ℝ =>
      (matrix.val row column, (1 : Matrix (Fin dimension) (Fin dimension) FiniteAdeles) row column))
    exact ((continuous_apply column).comp ((continuous_apply row).comp matrix_continuous)).prodMk
      continuous_const
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    change Continuous (fun matrix : GeneralLinearGroup (Fin dimension) ℝ =>
      (matrix⁻¹.val row column, (1 : Matrix (Fin dimension) (Fin dimension) FiniteAdeles) row column))
    exact ((continuous_apply column).comp
      ((continuous_apply row).comp inverse_continuous)).prodMk continuous_const

theorem binary_det_atInfinity (matrix : BinaryRealGL) :
    GeneralLinearGroup.det (atInfinity matrix) =
      realAdeleUnit (GeneralLinearGroup.det matrix) := by
  apply Units.ext
  apply Prod.ext
  · simp [GeneralLinearGroup.val_det_apply, atInfinity, combineGL, pairMatrix,
      realAdeleUnit, Matrix.det_fin_two]
  · simp [GeneralLinearGroup.val_det_apply, atInfinity, combineGL, pairMatrix,
      realAdeleUnit, Matrix.det_fin_two]

theorem binary_normalizingFactor_eq (matrix : BinaryRealGL) (exponent : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity matrix)) exponent =
      Complex.exp (exponent * (Real.log matrix.val.det : ℂ)) := by
  rw [binary_det_atInfinity, normPower, adeleNorm_realAdeleUnit,
    GeneralLinearGroup.val_det_apply, Real.log_abs]

theorem normPower_one (exponent : ℂ) : normPower 1 exponent = 1 := by
  simp [normPower]

theorem normPower_mul (first second : Adelesˣ) (exponent : ℂ) :
    normPower (first * second) exponent = normPower first exponent * normPower second exponent := by
  have first_positive : (0 : ℝ) < adeleNorm first := adeleNorm_pos first
  have second_positive : (0 : ℝ) < adeleNorm second := adeleNorm_pos second
  rw [normPower, map_mul, NNReal.coe_mul,
    Real.log_mul (ne_of_gt first_positive) (ne_of_gt second_positive),
    Complex.ofReal_add, mul_add, Complex.exp_add]
  rfl

def binaryCohomologicalOperator (degree : ℕ) (matrix : BinaryRealGL) :
    Module.End ℂ (BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) where
  toFun := binaryCohomologicalAction degree matrix
  map_add' first second := by
    funext argument
    simp only [binaryCohomologicalAction, Pi.add_apply, map_add, smul_add]
  map_smul' scalar values := by
    funext argument
    exact binaryCohomologicalAction_smul degree matrix values scalar argument

theorem binaryCohomologicalOperator_one (degree : ℕ) :
    binaryCohomologicalOperator degree 1 = 1 := by
  apply LinearMap.ext
  intro values
  funext argument
  simp [binaryCohomologicalOperator, binaryCohomologicalAction,
    binaryCoefficient, atInfinity_one, normPower_one]

theorem binaryCohomologicalOperator_mul (degree : ℕ) (first second : BinaryRealGL) :
    binaryCohomologicalOperator degree (first * second) =
      binaryCohomologicalOperator degree first * binaryCohomologicalOperator degree second := by
  apply LinearMap.ext
  intro values
  funext argument
  simp only [binaryCohomologicalOperator, binaryCohomologicalAction, LinearMap.coe_mk,
    AddHom.coe_mk, Module.End.mul_apply, atInfinity_mul, map_mul, normPower_mul,
    binaryCoefficient, map_smul, smul_smul, mul_assoc]

def binaryAmbientRepresentation (degree : ℕ) :
    Representation ℂ BinaryRealGL (BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) where
  toFun := binaryCohomologicalOperator degree
  map_one' := binaryCohomologicalOperator_one degree
  map_mul' := binaryCohomologicalOperator_mul degree

def binaryCuspidalRepresentation (cusp : CuspidalRepresentation) (degree : ℕ) :
    Representation ℂ BinaryRealGL (binaryCuspidalValues cusp degree) :=
  (binaryAmbientRepresentation degree).subrepresentation (binaryCuspidalValues cusp degree)
    (fun matrix values cuspidal => binaryValues_cohomologicalAction cusp values cuspidal matrix)

theorem binaryCuspidalRepresentation_apply (cusp : CuspidalRepresentation) (degree : ℕ)
    (matrix : BinaryRealGL) (values : binaryCuspidalValues cusp degree) :
    (binaryCuspidalRepresentation cusp degree matrix values).val =
      binaryCohomologicalAction degree matrix values.val := rfl

def binaryRightTranslation (cusp : CuspidalRepresentation) (degree : ℕ)
    (matrix : BinaryAdelicGL) : Module.End ℂ (binaryCuspidalValues cusp degree) where
  toFun values := ⟨fun argument => values.val (argument * matrix),
    binaryValues_right_translate cusp values.val values.property matrix⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem binaryRightTranslation_one (cusp : CuspidalRepresentation) (degree : ℕ) :
    binaryRightTranslation cusp degree 1 = 1 := by
  apply LinearMap.ext
  intro values
  apply Subtype.ext
  funext argument
  exact congrArg values.val (mul_one argument)

theorem binaryRightTranslation_mul (cusp : CuspidalRepresentation) (degree : ℕ)
    (first second : BinaryAdelicGL) :
    binaryRightTranslation cusp degree (first * second) =
      binaryRightTranslation cusp degree first * binaryRightTranslation cusp degree second := by
  apply LinearMap.ext
  intro values
  apply Subtype.ext
  funext argument
  exact congrArg values.val (mul_assoc argument first second).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
