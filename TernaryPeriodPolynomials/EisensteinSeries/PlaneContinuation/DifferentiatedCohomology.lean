module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.SmoothAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CocycleDifferential
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientSmoothAction TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCocycle
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.DifferentiatedCohomology

noncomputable def residual (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree) (vectors : Vectors data degree)
    (matrix : BinaryRealGL) : Vectors data degree :=
  cocycle matrix - coefficientAction data degree matrix vectors + vectors

theorem constant_family_joint_smooth (data : CuspidalRepresentation) (vector : data.smooth) :
    Smooth (fun x : Fin 2 → BinaryRealGL => (smoothTranslate data (x 1) vector).val) := by
  change ContDiffOn ℝ ⊤ (fun matrices : Fin 2 → BinaryMatrix =>
    realOrbit data vector.val (matrices 1)) {matrices | ∀ position, (matrices position).det ≠ 0}
  exact (smooth_orbit_contDiffOn data vector).comp (contDiff_apply ℝ BinaryMatrix 1).contDiffOn
    (fun _ membership => membership 1)

theorem residual_smooth (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (vectors : Vectors data degree) (index : Index (degree + 1)) :
    Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (residual data degree cocycle vectors (x 0) index)).val) := by
  have smoothDifference := ((regularity index).sub (coefficientAction_joint_smooth data degree vectors index)).add
    (constant_family_joint_smooth data (vectors index))
  change ContDiffOn ℝ ⊤ _ _
  convert smoothDifference using 1
  funext matrices
  change (smoothTranslate data (invertibleMatrix (matrices 1))
    (cocycle (invertibleMatrix (matrices 0)) index -
      coefficientAction data degree (invertibleMatrix (matrices 0)) vectors index + vectors index)).val = _
  simp only [map_add, map_sub, Submodule.coe_add, Submodule.coe_sub]

theorem residual_equation (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (vectors : Vectors data degree) (first second : BinaryRealGL) :
    residual data degree cocycle vectors (first * second) = residual data degree cocycle vectors first +
      coefficientAction data degree first (residual data degree cocycle vectors second) := by
  unfold residual
  rw [equation, coefficientAction_mul, Module.End.mul_apply, map_add, map_sub]
  abel

theorem residual_differential (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (vectors : Vectors data degree) :
    hilbertDifferential data degree (residual data degree cocycle vectors) = hilbertDifferential data degree cocycle -
      fderiv ℝ (fun matrix : BinaryMatrix =>
        hilbertAction data degree (invertibleMatrix matrix) (fun index => (vectors index).val)) 1 := by
  have cocycleRegular : DifferentiableAt ℝ (matrixCocycle data degree cocycle) 1 :=
    (matrixCocycle_contDiffAt data degree cocycle regularity 1).differentiableAt (by simp)
  have orbitRegular := (coefficient_orbit_contDiffAt_one data degree vectors).differentiableAt (by simp)
  have derivative := (cocycleRegular.hasFDerivAt.sub orbitRegular.hasFDerivAt).add_const
    (fun index => (vectors index).val)
  have equality : (fun matrix : BinaryMatrix => matrixCocycle data degree cocycle matrix -
      hilbertAction data degree (invertibleMatrix matrix) (fun index => (vectors index).val) +
      (fun index => (vectors index).val)) = matrixCocycle data degree (residual data degree cocycle vectors) := by
    funext matrix
    rw [hilbertAction_coefficientAction]
    rfl
  simp only [Pi.sub_apply] at derivative
  rw [equality] at derivative
  exact derivative.fderiv

/-- If the differentiated cocycle is an infinitesimal coboundary, the original group cocycle is a coboundary. -/
theorem coboundary_of_differential_coboundary (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (vectors : Vectors data degree)
    (infinitesimalCoboundary : ∀ direction, hilbertDifferential data degree cocycle direction =
      infinitesimalAction data degree direction (fun index => (vectors index).val)) :
    ∃ primitive : Vectors data degree, ∀ matrix,
      cocycle matrix = coefficientAction data degree matrix primitive - primitive := by
  have zeroDifferential : hilbertDifferential data degree (residual data degree cocycle vectors) = 0 := by
    rw [residual_differential data degree cocycle regularity vectors]
    apply ContinuousLinearMap.ext
    intro direction
    change hilbertDifferential data degree cocycle direction -
      infinitesimalAction data degree direction (fun index => (vectors index).val) = 0
    exact sub_eq_zero.mpr (infinitesimalCoboundary direction)
  obtain ⟨primitive, primitiveEquality⟩ := ZeroCocycleDifferential.coboundary_of_differential_zero data degree
    (residual data degree cocycle vectors) (residual_smooth data degree cocycle regularity vectors)
    (residual_equation data degree cocycle equation vectors) zeroDifferential
  refine ⟨primitive + vectors, ?_⟩
  intro matrix
  calc
    cocycle matrix = residual data degree cocycle vectors matrix + coefficientAction data degree matrix vectors - vectors := by
      unfold residual
      abel
    _ = _ := by
      rw [primitiveEquality, map_add]
      abel

theorem differential_not_coboundary (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (nontrivialClass : ¬ ∃ vectors : Vectors data degree, ∀ matrix,
      cocycle matrix = coefficientAction data degree matrix vectors - vectors) :
    ¬ ∃ vectors : Vectors data degree, ∀ direction,
      hilbertDifferential data degree cocycle direction =
        infinitesimalAction data degree direction (fun index => (vectors index).val) := by
  rintro ⟨vectors, infinitesimalCoboundary⟩
  exact nontrivialClass (coboundary_of_differential_coboundary data degree cocycle regularity equation vectors infinitesimalCoboundary)

theorem exists_nontrivial_differential {degree : ℕ} (data : InducingData degree) :
    ∃ differential : BinaryMatrix →L[ℝ] HilbertVectors data.cusp degree,
      (∀ direction index, differential direction index ∈ data.cusp.smooth) ∧
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ ∀ direction index,
          differential direction index ∈ fixedSubspace data.cusp level) ∧
      (∀ first second, infinitesimalAction data.cusp degree first (differential second) -
        infinitesimalAction data.cusp degree second (differential first) = differential (first * second - second * first)) ∧
      ¬ ∃ vectors : Vectors data.cusp degree, ∀ direction,
        differential direction = infinitesimalAction data.cusp degree direction (fun index => (vectors index).val) := by
  obtain ⟨cocycle, regularity, ⟨level, openness, compactness, fixed⟩, equation, nontrivialClass⟩ :=
    exists_lifted_cocycle data
  have fixedCoordinates (matrix : BinaryRealGL) (index : Index (degree + 1)) :
      (cocycle matrix index).val ∈ fixedSubspace data.cusp level := fun element => fixed element matrix index
  refine ⟨hilbertDifferential data.cusp degree cocycle, ?_, ⟨level, openness, compactness, ?_⟩,
    cocycle_identity data.cusp degree cocycle regularity equation,
    differential_not_coboundary data.cusp degree cocycle regularity equation nontrivialClass⟩
  · intro direction index
    rw [hilbertDifferential_apply data.cusp degree cocycle regularity]
    exact SmoothParameterDerivative.derivative_mem_smooth data.cusp (fun matrix => cocycle matrix index)
      (regularity index) level openness compactness (fun matrix => fixedCoordinates matrix index) direction
  · intro direction index
    rw [hilbertDifferential_apply data.cusp degree cocycle regularity]
    exact SmoothParameterDerivative.derivative_fixed data.cusp (fun matrix => cocycle matrix index)
      (regularity index) level (fun matrix => fixedCoordinates matrix index) direction

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.DifferentiatedCohomology
