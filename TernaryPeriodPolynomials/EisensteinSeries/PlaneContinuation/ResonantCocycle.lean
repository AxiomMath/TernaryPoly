module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.Rotation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientLieAction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ResonantCocycle

noncomputable def primitive (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree) : Vectors data degree :=
  CoefficientRotation.primitive data degree 0 (differential rotationMatrix)

noncomputable def normalized (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree) : BinaryMatrix →ₗ[ℝ] Vectors data degree :=
  differential - infinitesimalCoboundary data degree (primitive data degree differential)

theorem normalized_rotation (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree) :
    normalized data degree differential rotationMatrix =
      CoefficientRotation.projection data degree 0 (differential rotationMatrix) := by
  have equality : operator data degree rotationMatrix (primitive data degree differential) =
      differential rotationMatrix - CoefficientRotation.projection data degree 0 (differential rotationMatrix) := by
    simpa only [primitive, CoefficientRotation.shifted, Int.cast_zero, mul_zero, zero_smul, sub_zero] using
      CoefficientRotation.primitive_identity data degree 0 (differential rotationMatrix)
  change differential rotationMatrix - operator data degree rotationMatrix (primitive data degree differential) = _
  rw [equality]
  abel

theorem normalized_rotation_eigen (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree) :
    operator data degree rotationMatrix (normalized data degree differential rotationMatrix) = 0 := by
  rw [normalized_rotation]
  simpa only [CoefficientRotation.shifted, Int.cast_zero, mul_zero, zero_smul, sub_zero] using
    CoefficientRotation.projection_eigen data degree 0 (differential rotationMatrix)

theorem normalized_equation (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first))
    (first second : BinaryMatrix) :
    operator data degree first (normalized data degree differential second) -
      operator data degree second (normalized data degree differential first) =
        normalized data degree differential (first * second - second * first) :=
  CoefficientLieAction.residual_equation data degree differential equation (primitive data degree differential) first second

theorem normalized_not_coboundary (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (nontrivialClass : ¬ ∃ vectors : Vectors data degree, ∀ direction,
      differential direction = operator data degree direction vectors) :
    ¬ ∃ vectors : Vectors data degree, ∀ direction,
      normalized data degree differential direction = operator data degree direction vectors := by
  rintro ⟨vectors, equation⟩
  apply nontrivialClass
  refine ⟨vectors + primitive data degree differential, fun direction => ?_⟩
  have equality : differential direction - operator data degree direction (primitive data degree differential) =
      operator data degree direction vectors := equation direction
  rw [map_add]
  exact sub_eq_iff_eq_add.mp equality

theorem normalized_fixed (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ direction index, (differential direction index).val ∈ fixedSubspace data level)
    (direction : BinaryMatrix) (index : Index (degree + 1)) :
    (normalized data degree differential direction index).val ∈ fixedSubspace data level := by
  exact (fixedSubspace data level).sub_mem (fixed direction index)
    (operator_preserves_fixed data degree level direction (primitive data degree differential)
      (fun other => CoefficientRotation.primitive_fixed data degree 0 (differential rotationMatrix)
        level openness compactness (fixed rotationMatrix) other) index)

/-- Subtracting an actual smooth coboundary leaves only the resonant rotation component. -/
theorem exists_resonant_cocycle {degree : ℕ} (data : InducingData degree) :
    ∃ differential : BinaryMatrix →ₗ[ℝ] Vectors data.cusp degree,
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ ∀ direction index,
          (differential direction index).val ∈ fixedSubspace data.cusp level) ∧
      (∀ first second, operator data.cusp degree first (differential second) -
        operator data.cusp degree second (differential first) = differential (first * second - second * first)) ∧
      operator data.cusp degree rotationMatrix (differential rotationMatrix) = 0 ∧
      ¬ ∃ vectors : Vectors data.cusp degree, ∀ direction,
        differential direction = operator data.cusp degree direction vectors := by
  obtain ⟨differential, ⟨level, openness, compactness, fixed⟩, equation, nontrivialClass⟩ :=
    exists_nontrivial_smooth_cocycle data
  exact ⟨normalized data.cusp degree differential,
    ⟨level, openness, compactness, normalized_fixed data.cusp degree differential level openness compactness fixed⟩,
    normalized_equation data.cusp degree differential equation,
    normalized_rotation_eigen data.cusp degree differential,
    normalized_not_coboundary data.cusp degree differential nontrivialClass⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ResonantCocycle
