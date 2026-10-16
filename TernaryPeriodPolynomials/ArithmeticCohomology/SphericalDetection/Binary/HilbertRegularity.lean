module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HilbertModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CoefficientRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.Tensor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryHilbertCoefficient (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrix : BinaryRealGL) : (index → cusp.H) →L[ℂ] (index → cusp.H) :=
  finiteTensorOperator basis (binaryCoefficient degree matrix)

theorem binaryHilbertCoefficient_one (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    binaryHilbertCoefficient cusp basis 1 = ContinuousLinearMap.id ℂ (index → cusp.H) := by
  simp only [binaryHilbertCoefficient, binaryCoefficient, map_one, finiteTensorOperator_one]

theorem binaryHilbertCoefficient_mul (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (first second : BinaryRealGL) :
    binaryHilbertCoefficient cusp basis (first * second) =
      (binaryHilbertCoefficient cusp basis first).comp (binaryHilbertCoefficient cusp basis second) := by
  simp only [binaryHilbertCoefficient, binaryCoefficient, map_mul, finiteTensorOperator_mul]

theorem binaryHilbertOperator_factor (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrix : BinaryRealGL) (vectors : index → cusp.H) :
    binaryHilbertOperator cusp basis matrix vectors =
      normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
        binaryHilbertCoefficient cusp basis matrix (binaryHilbertTranslation cusp (atInfinity matrix) vectors) := by
  funext position
  simp only [binaryHilbertOperator_apply, Pi.smul_apply, binaryHilbertCoefficient,
    finiteTensorOperator_apply, binaryHilbertTranslation_apply]

theorem binaryHilbertTranslation_eq (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrix : BinaryRealGL) (vectors : index → cusp.H) :
    binaryHilbertTranslation cusp (atInfinity matrix) vectors =
      (normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2))⁻¹ •
        binaryHilbertCoefficient cusp basis matrix⁻¹ (binaryHilbertOperator cusp basis matrix vectors) := by
  have combined :
      binaryHilbertCoefficient cusp basis matrix⁻¹ (binaryHilbertOperator cusp basis matrix vectors) =
        normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
          binaryHilbertTranslation cusp (atInfinity matrix) vectors := by
    rw [binaryHilbertOperator_factor, map_smul, ← ContinuousLinearMap.comp_apply,
      ← binaryHilbertCoefficient_mul, inv_mul_cancel, binaryHilbertCoefficient_one,
      ContinuousLinearMap.id_apply]
  have nonzero : normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix))
      (((degree : ℂ) + 3) / 2) ≠ 0 := Complex.exp_ne_zero _
  rw [combined, smul_smul, inv_mul_cancel₀ nonzero, one_smul]

theorem binaryHilbertCoefficient_contDiffOn {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {domain : Set P} {order : WithTop ℕ∞}
    (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrices : P → Matrix (Fin 2) (Fin 2) ℝ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (invertible : ∀ point ∈ domain, (matrices point).det ≠ 0)
    (vectors : P → (index → cusp.H)) (regular : ContDiffOn ℝ order vectors domain) :
    ContDiffOn ℝ order
      (fun point => binaryHilbertCoefficient cusp basis (invertibleMatrix (matrices point)) (vectors point))
      domain := by
  apply contDiffOn_pi.mpr
  intro position
  simp only [binaryHilbertCoefficient, finiteTensorOperator_apply]
  exact ContDiffOn.sum (fun source _ =>
    (binaryCoefficient_functional_contDiffOn matrices entries invertible
      (basis source) (basis.coord position)).smul (contDiffOn_pi.mp regular source))

theorem binaryHilbertTranslation_contDiffOn_of_operator {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {domain : Set P} {order : WithTop ℕ∞}
    (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (matrices : P → Matrix (Fin 2) (Fin 2) ℝ)
    (entries : ∀ row column, ContDiffOn ℝ order (fun point => matrices point row column) domain)
    (invertible : ∀ point ∈ domain, (matrices point).det ≠ 0)
    (vector : index → cusp.H)
    (regular : ContDiffOn ℝ order
      (fun point => binaryHilbertOperator cusp basis (invertibleMatrix (matrices point)) vector) domain) :
    ContDiffOn ℝ order
      (fun point => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix (matrices point))) vector)
      domain := by
  have inverse_regular := binaryHilbertCoefficient_contDiffOn cusp basis
    (fun point => (matrices point)⁻¹) (binary_matrix_inv_contDiffOn matrices entries invertible)
    (fun point member => by
      simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero (invertible point member))
    _ regular
  have scalar_regular := (binary_normalizingFactor_contDiffOn matrices entries invertible
    (((degree : ℂ) + 3) / 2)).inv (fun _ _ => Complex.exp_ne_zero _)
  apply (scalar_regular.smul inverse_regular).congr
  intro point member
  change binaryHilbertTranslation cusp (atInfinity (invertibleMatrix (matrices point))) vector =
    (normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (matrices point))))
      (((degree : ℂ) + 3) / 2))⁻¹ •
        binaryHilbertCoefficient cusp basis (invertibleMatrix (matrices point)⁻¹)
          (binaryHilbertOperator cusp basis (invertibleMatrix (matrices point)) vector)
  rw [binaryHilbertTranslation_eq cusp basis, invertibleMatrix_inv _ (invertible point member)]

theorem binaryHilbertPrimitive_smooth (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : BinaryRealGL → (index → cusp.H))
    (regular : Smooth (fun point : Fin 1 → BinaryRealGL => cycle (point 0)))
    (vector : index → cusp.H)
    (boundary : ∀ matrix, cycle matrix = binaryHilbertOperator cusp basis matrix vector - vector) :
    Smooth (fun point : Fin 1 → BinaryRealGL =>
      binaryHilbertTranslation cusp (atInfinity (point 0)) vector) := by
  have operator_regular : ContDiffOn ℝ ⊤
      (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        binaryHilbertOperator cusp basis (invertibleMatrix (point 0)) vector)
      {point | ∀ position, (point position).det ≠ 0} := by
    apply (regular.add (contDiffOn_const (c := vector))).congr
    intro point _
    change binaryHilbertOperator cusp basis (invertibleMatrix (point 0)) vector =
      cycle (invertibleMatrix (point 0)) + vector
    rw [boundary, sub_add_cancel]
  apply binaryHilbertTranslation_contDiffOn_of_operator
    (domain := {point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ |
      ∀ position, (point position).det ≠ 0}) cusp basis
    (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ => point 0) _
    (fun _ member => member 0) vector operator_regular
  intro row column
  fun_prop

theorem binaryHilbertPrimitive_mem_range (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : BinaryRealGL → (index → cusp.H))
    (regular : Smooth (fun point : Fin 1 → BinaryRealGL => cycle (point 0)))
    (vector : index → cusp.H)
    (boundary : ∀ matrix, cycle matrix = binaryHilbertOperator cusp basis matrix vector - vector)
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ element : level, ∀ position, cusp.π (atFinite element.val) (vector position) = vector position) :
    vector ∈ Set.range (binaryHilbertEmbedding cusp basis) := by
  have smooth := binaryHilbertPrimitive_smooth cusp basis cycle regular vector boundary
  have membership (position : index) : vector position ∈ cusp.smooth := by
    apply (cusp.smooth_exact (vector position)).mpr
    refine ⟨contDiffOn_pi.mp smooth position, level, level_open, level_compact, ?_⟩
    intro element
    exact fixed element position
  obtain ⟨values, coordinates⟩ := binarySmoothCoordinates_surjective cusp basis
    (fun position => ⟨vector position, membership position⟩)
  refine ⟨values, ?_⟩
  funext position
  exact congrArg Subtype.val (congrFun coordinates position)

theorem binaryHilbertOperator_continuous (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vector : index → cusp.H) :
    Continuous (fun matrix => binaryHilbertOperator cusp basis matrix vector) := by
  have scalar : Continuous (fun matrix : BinaryRealGL =>
      normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2)) := by
    apply realGL_continuous_of_contDiffOn
    apply binary_normalizingFactor_contDiffOn (fun matrix => matrix) _ (fun _ member => member)
    intro row column
    fun_prop
  have coefficients (position source : index) : Continuous (fun matrix : BinaryRealGL =>
      basis.coord position (binaryCoefficient degree matrix (basis source))) := by
    apply realGL_continuous_of_contDiffOn
    apply binaryCoefficient_functional_contDiffOn (fun matrix => matrix) _
      (fun _ member => member) (basis source) (basis.coord position)
    intro row column
    fun_prop
  apply continuous_pi
  intro position
  simp only [binaryHilbertOperator_apply]
  apply scalar.smul
  exact continuous_finsetSum _ (fun source _ =>
    (coefficients position source).smul ((cusp.continuous (vector source)).comp atInfinity_continuous))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
