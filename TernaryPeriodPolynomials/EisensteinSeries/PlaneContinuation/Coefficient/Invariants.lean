module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.StandardCoefficient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientDerivative
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientTensor TernaryPeriodPolynomials.PlaneEisensteinContinuation.StandardCoefficient TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInvariants

theorem balanced_index_unique (degree : ℕ) (first second : Index degree)
    (firstBalanced : first.val 0 = first.val 1) (secondBalanced : second.val 0 = second.val 1) : first = second := by
  have firstDegree := CoefficientCoordinates.index_degree degree first
  have secondDegree := CoefficientCoordinates.index_degree degree second
  have firstEquality : first.val 0 = second.val 0 := by omega
  have secondEquality : first.val 1 = second.val 1 := by omega
  apply Subtype.ext
  ext position
  fin_cases position
  · exact firstEquality
  · exact secondEquality

theorem invariant_tensor (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (invariant : operator data degree diagonalMatrix vectors = 0) (index : Index (degree + 1))
    (balanced : index.val 0 = index.val 1) : vectors = tensor data degree (basisMonomial index).val (vectors index) := by
  classical
  funext other
  simp only [tensor, basisMonomial, MvPolynomial.coeff_monomial, Subtype.val_inj]
  by_cases same : index = other
  · subst other
    simp
  · have unbalanced : other.val 0 ≠ other.val 1 := fun equality =>
      same (balanced_index_unique (degree + 1) index other balanced equality)
    simp only [ite_eq_right same, zero_smul]
    exact unbalanced_coordinate_zero data degree vectors invariant other unbalanced

theorem rotation_first : PolynomialLadder.rotation (MvPolynomial.X 0) = MvPolynomial.X 1 := by
  simp [PolynomialLadder.rotation, PolynomialDerivative.variableDerivative, complexDirection,
    rotationMatrix, Binary.linearForm]

theorem rotation_second : PolynomialLadder.rotation (MvPolynomial.X 1) = -MvPolynomial.X 0 := by
  simp [PolynomialLadder.rotation, PolynomialDerivative.variableDerivative, complexDirection,
    rotationMatrix, Binary.linearForm]

theorem rotation_monomial (first second : ℕ) :
    PolynomialLadder.rotation (standardMonomial first second) =
      (first : ℂ) • standardMonomial (first - 1) (second + 1) -
        (second : ℂ) • standardMonomial (first + 1) (second - 1) := by
  rw [standardMonomial, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow,
    rotation_first, rotation_second]
  simp only [smul_eq_mul, standardMonomial, pow_succ, Algebra.smul_def]
  push_cast
  have natMap (number : ℕ) : algebraMap ℕ Binary.Poly number = (number : Binary.Poly) :=
    map_natCast (algebraMap ℕ Binary.Poly) number
  rw [natMap, natMap]
  ring

theorem standard_coefficient (first second row column : ℕ) :
    (standardMonomial first second).coeff (exponents row column) =
      if first = row ∧ second = column then 1 else 0 := by
  classical
  rw [standardMonomial_eq, MvPolynomial.coeff_monomial]
  have equality : exponents first second = exponents row column ↔ first = row ∧ second = column := by
    constructor
    · intro same
      exact ⟨by simpa only [exponents_zero] using congrArg (fun monomial : Fin 2 →₀ ℕ => monomial 0) same,
        by simpa only [exponents_one] using congrArg (fun monomial : Fin 2 →₀ ℕ => monomial 1) same⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [equality]

theorem balanced_neighbor_coefficient (power : ℕ) :
    (standardMonomial power power).coeff (exponents (power + 1) (power - 1)) = 0 := by
  rw [standard_coefficient]
  simp

theorem rotation_balanced_neighbor (power : ℕ) :
    (PolynomialLadder.rotation (standardMonomial power power)).coeff (exponents (power + 1) (power - 1)) = -(power : ℂ) := by
  rw [rotation_monomial]
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, standard_coefficient, smul_eq_mul]
  have different : power - 1 ≠ power + 1 := by omega
  simp [different]

/-- A positive-degree algebraic coefficient tensor with a unitary representation has no invariant vector. -/
theorem eq_zero_of_invariant (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (diagonalInvariant : operator data degree diagonalMatrix vectors = 0)
    (rotationInvariant : operator data degree rotationMatrix vectors = 0) : vectors = 0 := by
  by_contra nonzero
  have someNonzero : ∃ index, vectors index ≠ 0 := by
    by_contra! vanishing
    exact nonzero (funext vanishing)
  obtain ⟨index, coordinateNonzero⟩ := someNonzero
  have balanced : index.val 1 = index.val 0 := by
    by_contra unequal
    exact coordinateNonzero (unbalanced_coordinate_zero data degree vectors diagonalInvariant index (Ne.symm unequal))
  have degreeEquality := CoefficientCoordinates.index_degree (degree + 1) index
  have positive : 0 < index.val 0 := by omega
  have basisEquality : (basisMonomial index).val = standardMonomial (index.val 0) (index.val 0) := by
    rw [basisMonomial_eq, balanced]
  have homogeneous : (standardMonomial (index.val 0) (index.val 0)).IsHomogeneous (degree + 1) := by
    rw [← basisEquality]
    exact (basisMonomial index).property
  let neighbor : Index (degree + 1) := ⟨exponents (index.val 0 + 1) (index.val 0 - 1), by
    rw [exponents_degree]
    omega⟩
  have singleTensor := invariant_tensor data degree vectors diagonalInvariant index balanced.symm
  rw [basisEquality] at singleTensor
  have equality := congrFun rotationInvariant neighbor
  rw [singleTensor, operator_tensor data degree rotationMatrix _ homogeneous,
    PolynomialLadder.polynomialOperator_rotation] at equality
  change (standardMonomial (index.val 0) (index.val 0)).coeff (exponents (index.val 0 + 1) (index.val 0 - 1)) • rotationOperator data (vectors index) +
    (PolynomialLadder.rotation (standardMonomial (index.val 0) (index.val 0))).coeff (exponents (index.val 0 + 1) (index.val 0 - 1)) • vectors index = 0 at equality
  rw [balanced_neighbor_coefficient, rotation_balanced_neighbor, zero_smul, zero_add] at equality
  exact coordinateNonzero ((smul_eq_zero.mp equality).resolve_left
    (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt positive))))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInvariants
