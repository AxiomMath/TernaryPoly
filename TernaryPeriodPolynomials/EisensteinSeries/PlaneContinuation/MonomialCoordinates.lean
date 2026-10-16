module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RelativePair

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientCoordinates TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientTensor
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.StandardCoefficient TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialCoordinates

noncomputable def indexOf (degree position : ℕ) (bound : position ≤ degree + 1) : Index (degree + 1) :=
  ⟨exponents position (degree + 1 - position), by rw [exponents_degree]; omega⟩

theorem indexOf_zero (degree position : ℕ) (bound : position ≤ degree + 1) :
    (indexOf degree position bound).val 0 = position := exponents_zero _ _

theorem indexOf_one (degree position : ℕ) (bound : position ≤ degree + 1) :
    (indexOf degree position bound).val 1 = degree + 1 - position := exponents_one _ _

theorem position_bound (degree : ℕ) (index : Index (degree + 1)) : index.val 0 ≤ degree + 1 := by
  have equality := index_degree (degree + 1) index
  omega

theorem indexOf_position (degree : ℕ) (index : Index (degree + 1)) :
    indexOf degree (index.val 0) (position_bound degree index) = index := by
  have equality : degree + 1 - index.val 0 = index.val 1 := by
    have degreeEquality := index_degree (degree + 1) index
    omega
  apply Subtype.ext
  change exponents (index.val 0) (degree + 1 - index.val 0) = index.val
  rw [equality, exponents_reconstruct]

theorem indexOf_injective (degree first second : ℕ) (firstBound : first ≤ degree + 1) (secondBound : second ≤ degree + 1) :
    indexOf degree first firstBound = indexOf degree second secondBound ↔ first = second := by
  constructor
  · intro equality
    simpa only [indexOf_zero] using congrArg (fun index : Index (degree + 1) => index.val 0) equality
  · rintro rfl
    rfl

noncomputable def component (data : CuspidalRepresentation) (degree position : ℕ) : Vectors data degree →ₗ[ℂ] data.smooth :=
  if bound : position ≤ degree + 1 then (LinearMap.proj (indexOf degree position bound)).comp (fromMonomials data degree) else 0

theorem component_apply (data : CuspidalRepresentation) (degree position : ℕ) (bound : position ≤ degree + 1)
    (vectors : Vectors data degree) : component data degree position vectors =
      fromMonomials data degree vectors (indexOf degree position bound) := by
  simp only [component, dite_eq_left bound, LinearMap.comp_apply, LinearMap.proj_apply]

theorem component_above (data : CuspidalRepresentation) (degree position : ℕ) (above : degree + 1 < position)
    (vectors : Vectors data degree) : component data degree position vectors = 0 := by
  simp only [component, dite_eq_right (not_le.mpr above), LinearMap.zero_apply]

noncomputable def assemble (data : CuspidalRepresentation) (degree : ℕ) :
    (ℕ → data.smooth) →ₗ[ℂ] Vectors data degree :=
  (toMonomials data degree).comp (LinearMap.pi (fun index => LinearMap.proj (index.val 0)))

theorem component_assemble (data : CuspidalRepresentation) (degree position : ℕ) (bound : position ≤ degree + 1)
    (family : ℕ → data.smooth) : component data degree position (assemble data degree family) = family position := by
  rw [component_apply data degree position bound]
  change fromMonomials data degree (toMonomials data degree (fun index => family (index.val 0)))
    (indexOf degree position bound) = _
  rw [from_to, indexOf_zero]

theorem assemble_components (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    assemble data degree (fun position => component data degree position vectors) = vectors := by
  change toMonomials data degree (fun index => component data degree (index.val 0) vectors) = _
  have equality : (fun index : Index (degree + 1) => component data degree (index.val 0) vectors) =
      fromMonomials data degree vectors := by
    funext index
    rw [component_apply data degree _ (position_bound degree index), indexOf_position]
  rw [equality, to_from]

theorem components_ext (data : CuspidalRepresentation) (degree : ℕ) (first second : Vectors data degree)
    (agreement : ∀ position, position ≤ degree + 1 → component data degree position first = component data degree position second) :
    first = second := by
  have equality : (fun position => component data degree position first) =
      (fun position => component data degree position second) := by
    funext position
    by_cases bound : position ≤ degree + 1
    · exact agreement position bound
    · rw [component_above data degree position (lt_of_not_ge bound), component_above data degree position (lt_of_not_ge bound)]
  rw [← assemble_components data degree first, ← assemble_components data degree second, equality]

noncomputable def basisVector (data : CuspidalRepresentation) (degree position : ℕ) (vector : data.smooth) : Vectors data degree :=
  tensor data degree (PolynomialLadder.monomial position (degree + 1 - position)) vector

theorem basisVector_toMonomials (data : CuspidalRepresentation) (degree position : ℕ) (bound : position ≤ degree + 1)
    (vector : data.smooth) : basisVector data degree position vector =
      toMonomials data degree (tensor data degree (basisMonomial (indexOf degree position bound)).val vector) := by
  change _ = lift data degree (substitute degree changeMatrix) _
  rw [lift_tensor, substitute_basis, indexOf_zero, indexOf_one]
  rfl

theorem component_basisVector (data : CuspidalRepresentation) (degree row column : ℕ)
    (rowBound : row ≤ degree + 1) (columnBound : column ≤ degree + 1) (vector : data.smooth) :
    component data degree row (basisVector data degree column vector) = if column = row then vector else 0 := by
  classical
  rw [component_apply data degree row rowBound, basisVector_toMonomials data degree column columnBound, from_to]
  simp only [tensor, basisMonomial, MvPolynomial.coeff_monomial, Subtype.val_inj,
    indexOf_injective, ite_smul, one_smul, zero_smul]

theorem reconstruct (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree) :
    ∑ position ∈ Finset.range (degree + 2), basisVector data degree position (component data degree position vectors) = vectors := by
  apply components_ext data degree
  intro row rowBound
  rw [map_sum]
  have equality : (∑ position ∈ Finset.range (degree + 2),
      component data degree row (basisVector data degree position (component data degree position vectors))) =
      ∑ position ∈ Finset.range (degree + 2), if position = row then component data degree position vectors else 0 := by
    apply Finset.sum_congr rfl
    intro position membership
    exact component_basisVector data degree row position rowBound (by have := Finset.mem_range.mp membership; omega) _
  rw [equality, Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr (by omega))]

theorem component_fixed (data : CuspidalRepresentation) (degree position : ℕ)
    (vectors : Vectors data degree) (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ index, (vectors index).val ∈ BinaryLevel.fixedSubspace data level) :
    (component data degree position vectors).val ∈ BinaryLevel.fixedSubspace data level := by
  by_cases bound : position ≤ degree + 1
  · rw [component_apply data degree position bound]
    exact lift_fixed data degree _ level vectors fixed _
  · rw [component_above data degree position (lt_of_not_ge bound)]
    exact (BinaryLevel.fixedSubspace data level).zero_mem

theorem assemble_fixed (data : CuspidalRepresentation) (degree : ℕ) (family : ℕ → data.smooth)
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ position, position ≤ degree + 1 → (family position).val ∈ BinaryLevel.fixedSubspace data level)
    (index : Index (degree + 1)) : (assemble data degree family index).val ∈ BinaryLevel.fixedSubspace data level :=
  lift_fixed data degree _ level _ (fun other => fixed (other.val 0) (position_bound degree other)) index

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialCoordinates
