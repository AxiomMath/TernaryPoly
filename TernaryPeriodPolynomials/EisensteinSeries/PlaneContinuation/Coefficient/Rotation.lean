module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.LieAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientCoordinates
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationPrimitive TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientRotation

def weight (degree : ℕ) (target : ℤ) (index : Index (degree + 1)) : ℤ := target + index.val 0 - index.val 1

theorem weight_scalar (degree : ℕ) (target : ℤ) (index : Index (degree + 1)) :
    Complex.I * ((index.val 1 : ℂ) - index.val 0) - Complex.I * target =
      -(Complex.I * weight degree target index) := by
  simp only [weight, Int.cast_sub, Int.cast_add, Int.cast_natCast]
  ring

noncomputable def shifted (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) : Module.End ℂ (Vectors data degree) :=
  operator data degree rotationMatrix - (Complex.I * target) • LinearMap.id

theorem shifted_toMonomials (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (vectors : Vectors data degree) :
    shifted data degree target (toMonomials data degree vectors) =
      toMonomials data degree (fun index => rotationOperator data (vectors index) -
        (Complex.I * weight degree target index) • vectors index) := by
  change operator data degree rotationMatrix (toMonomials data degree vectors) -
    (Complex.I * target) • toMonomials data degree vectors = _
  rw [rotation_toMonomials, ← map_smul, ← map_sub]
  congr 1
  funext index
  change rotationOperator data (vectors index) + (Complex.I * ((index.val 1 : ℂ) - index.val 0)) • vectors index -
    (Complex.I * target) • vectors index = _
  have equality := weight_scalar degree target index
  calc
    _ = rotationOperator data (vectors index) +
        (Complex.I * ((index.val 1 : ℂ) - index.val 0) - Complex.I * target) • vectors index := by module
    _ = _ := by rw [equality, neg_smul, sub_eq_add_neg]

noncomputable def projection (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) :
    Module.End ℂ (Vectors data degree) :=
  (toMonomials data degree).comp ((LinearMap.pi (fun index =>
    (smoothMode data (weight degree target index)).comp (LinearMap.proj index))).comp (fromMonomials data degree))

theorem projection_apply (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (vectors : Vectors data degree) :
    projection data degree target vectors = toMonomials data degree
      (fun index => smoothMode data (weight degree target index) (fromMonomials data degree vectors index)) := rfl

noncomputable def primitive (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (vectors : Vectors data degree) :
    Vectors data degree := toMonomials data degree (fun index =>
      rotationPrimitive data (weight degree target index) (fromMonomials data degree vectors index))

theorem primitive_identity (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (vectors : Vectors data degree) :
    shifted data degree target (primitive data degree target vectors) = vectors - projection data degree target vectors := by
  rw [primitive, shifted_toMonomials]
  simp only [rotationPrimitive_identity]
  change toMonomials data degree
    (fromMonomials data degree vectors - (fun index => smoothMode data (weight degree target index)
      (fromMonomials data degree vectors index))) = _
  rw [map_sub, to_from]
  rfl

theorem projection_eigen (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (vectors : Vectors data degree) :
    shifted data degree target (projection data degree target vectors) = 0 := by
  rw [projection_apply, shifted_toMonomials]
  have equality : (fun index => rotationOperator data (smoothMode data (weight degree target index)
      (fromMonomials data degree vectors index)) - (Complex.I * weight degree target index) •
        smoothMode data (weight degree target index) (fromMonomials data degree vectors index)) = 0 := by
    funext index
    apply sub_eq_zero.mpr
    exact (rotation_eigen_iff data _ _).mpr (modeVector_eigen data (weight degree target index)
      (fromMonomials data degree vectors index).val)
  rw [equality, map_zero]

theorem projection_fixed (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (vectors : Vectors data degree)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ index, (vectors index).val ∈ fixedSubspace data level) (index : Index (degree + 1)) :
    (projection data degree target vectors index).val ∈ fixedSubspace data level := by
  apply lift_fixed data degree _ level _ _ index
  intro other
  exact (modeVector_preserves_fixedSmooth data (weight degree target other) level openness compactness
    (fromMonomials data degree vectors other) (lift_fixed data degree _ level vectors fixed other)).2

theorem primitive_fixed (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (vectors : Vectors data degree)
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ index, (vectors index).val ∈ fixedSubspace data level) (index : Index (degree + 1)) :
    (primitive data degree target vectors index).val ∈ fixedSubspace data level := by
  apply lift_fixed data degree _ level _ _ index
  intro other
  exact rotationPrimitive_fixed data (weight degree target other) (fromMonomials data degree vectors other)
    level openness compactness (lift_fixed data degree _ level vectors fixed other)

theorem projection_shifted_zero (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (vectors : Vectors data degree) :
    projection data degree target (shifted data degree target vectors) = 0 := by
  have equality := shifted_toMonomials data degree target (fromMonomials data degree vectors)
  rw [to_from] at equality
  rw [equality, projection_apply, from_to]
  simp only [smoothMode_shifted_zero]
  exact map_zero (toMonomials data degree)

theorem projection_eq_self (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (vectors : Vectors data degree)
    (eigen : shifted data degree target vectors = 0) : projection data degree target vectors = vectors := by
  have equality := congrArg (fromMonomials data degree)
    (shifted_toMonomials data degree target (fromMonomials data degree vectors))
  rw [to_from, eigen, map_zero, from_to] at equality
  have coordinates (index : Index (degree + 1)) :
      smoothMode data (weight degree target index) (fromMonomials data degree vectors index) =
        fromMonomials data degree vectors index := by
    have coordinateEigen : rotationOperator data (fromMonomials data degree vectors index) =
        (Complex.I * weight degree target index) • fromMonomials data degree vectors index :=
      sub_eq_zero.mp (congrFun equality index).symm
    apply Subtype.ext
    exact modeVector_eq_self_of_eigen data (weight degree target index) _
      ((rotation_eigen_iff data _ _).mp coordinateEigen)
  rw [projection_apply]
  simp only [coordinates]
  exact to_from data degree vectors

/-- The range of a shifted rotation operator has zero intersection with its eigenspace. -/
theorem shifted_range_eigen_zero (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ)
    (source value : Vectors data degree) (equation : shifted data degree target source = value)
    (eigen : shifted data degree target value = 0) : value = 0 := by
  have equality := congrArg (projection data degree target) equation
  rw [projection_shifted_zero, projection_eq_self data degree target value eigen] at equality
  exact equality.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientRotation
