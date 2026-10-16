module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MonomialCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientTensor TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialCoordinates

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialLadder

theorem raising_basis_zero (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth) :
    CoefficientLadder.raising data degree (basisVector data degree 0 vector) =
      basisVector data degree 0 (LieOperators.raising data vector) := by
  have homogeneous : (PolynomialLadder.monomial 0 (degree + 1 - 0)).IsHomogeneous (degree + 1) := by
    simpa only [Nat.sub_zero, Nat.zero_add] using PolynomialLadder.monomial_homogeneous 0 (degree + 1)
  change CoefficientLadder.raising data degree (tensor data degree _ vector) = _
  rw [CoefficientLadder.raising, raising_tensor data degree _ homogeneous, PolynomialLadder.raising_endpoint, tensor_zero, add_zero]
  rfl

theorem raising_basis_succ (data : CuspidalRepresentation) (degree position : ℕ) (bound : position + 1 ≤ degree + 1)
    (vector : data.smooth) :
    CoefficientLadder.raising data degree (basisVector data degree (position + 1) vector) =
      basisVector data degree (position + 1) (LieOperators.raising data vector) +
        (-2 * (position + 1 : ℂ)) • basisVector data degree position vector := by
  have homogeneous : (PolynomialLadder.monomial (position + 1) (degree + 1 - (position + 1))).IsHomogeneous (degree + 1) := by
    convert PolynomialLadder.monomial_homogeneous (position + 1) (degree + 1 - (position + 1)) using 1; omega
  change CoefficientLadder.raising data degree (tensor data degree _ vector) = _
  rw [CoefficientLadder.raising, raising_tensor data degree _ homogeneous, PolynomialLadder.raising_monomial, tensor_smul]
  have equality : degree + 1 - (position + 1) + 1 = degree + 1 - position := by omega
  rw [equality]
  rfl

theorem lowering_basis_last (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth) :
    CoefficientLadder.lowering data degree (basisVector data degree (degree + 1) vector) =
      basisVector data degree (degree + 1) (LieOperators.lowering data vector) := by
  have homogeneous : (PolynomialLadder.monomial (degree + 1) 0).IsHomogeneous (degree + 1) := by
    simpa only [Nat.add_zero] using PolynomialLadder.monomial_homogeneous (degree + 1) 0
  change CoefficientLadder.lowering data degree (tensor data degree _ vector) = _
  simp only [Nat.sub_self]
  rw [CoefficientLadder.lowering, lowering_tensor data degree _ homogeneous, PolynomialLadder.lowering_endpoint, tensor_zero, add_zero]
  simp only [basisVector, Nat.sub_self]

theorem lowering_basis (data : CuspidalRepresentation) (degree position : ℕ) (bound : position < degree + 1)
    (vector : data.smooth) :
    CoefficientLadder.lowering data degree (basisVector data degree position vector) =
      basisVector data degree position (LieOperators.lowering data vector) +
        (-2 * ((degree + 1 - position : ℕ) : ℂ)) • basisVector data degree (position + 1) vector := by
  have homogeneous : (PolynomialLadder.monomial position (degree + 1 - position)).IsHomogeneous (degree + 1) := by
    convert PolynomialLadder.monomial_homogeneous position (degree + 1 - position) using 1; omega
  have split : degree + 1 - position = (degree + 1 - (position + 1)) + 1 := by omega
  change CoefficientLadder.lowering data degree (tensor data degree _ vector) = _
  rw [CoefficientLadder.lowering, lowering_tensor data degree _ homogeneous]
  conv_lhs => arg 2; arg 3; rw [split]
  rw [PolynomialLadder.lowering_monomial, tensor_smul]
  rw [show ((degree + 1 - (position + 1) : ℕ) : ℂ) + 1 = ((degree + 1 - position : ℕ) : ℂ) by
    exact_mod_cast split.symm]
  rfl

theorem component_raising_basis (data : CuspidalRepresentation) (degree row column : ℕ)
    (rowBound : row ≤ degree + 1) (columnBound : column ≤ degree + 1) (vector : data.smooth) :
    component data degree row (CoefficientLadder.raising data degree (basisVector data degree column vector)) =
      (if column = row then LieOperators.raising data vector else 0) -
        (if column = row + 1 then (2 * (column : ℂ)) • vector else 0) := by
  cases column with
  | zero =>
      rw [raising_basis_zero, component_basisVector data degree row 0 rowBound (by omega)]
      simp
  | succ column =>
      rw [raising_basis_succ data degree column columnBound,
        map_add, map_smul, component_basisVector data degree row (column + 1) rowBound columnBound,
        component_basisVector data degree row column rowBound (by omega)]
      by_cases same : column = row
      · subst column
        simp [neg_mul, neg_smul]
      · simp [same]

/-- The exact raising operator is triangular in the rotation-monomial coordinates. -/
theorem component_raising (data : CuspidalRepresentation) (degree position : ℕ) (bound : position ≤ degree + 1)
    (vectors : Vectors data degree) :
    component data degree position (CoefficientLadder.raising data degree vectors) =
      LieOperators.raising data (component data degree position vectors) -
        (2 * (position + 1 : ℂ)) • component data degree (position + 1) vectors := by
  have equality := congrArg (fun value : Vectors data degree => component data degree position (CoefficientLadder.raising data degree value))
    (reconstruct data degree vectors)
  simp only [map_sum] at equality
  have terms : (∑ column ∈ Finset.range (degree + 2),
      component data degree position (CoefficientLadder.raising data degree
        (basisVector data degree column (component data degree column vectors)))) =
      ∑ column ∈ Finset.range (degree + 2),
        ((if column = position then LieOperators.raising data (component data degree column vectors) else 0) -
          (if column = position + 1 then (2 * (column : ℂ)) • component data degree column vectors else 0)) := by
    apply Finset.sum_congr rfl
    intro column membership
    exact component_raising_basis data degree position column bound (by have := Finset.mem_range.mp membership; omega) _
  rw [terms, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_range.mpr (by omega))] at equality
  by_cases nextBound : position + 1 ≤ degree + 1
  · rw [ite_eq_left (Finset.mem_range.mpr (by omega))] at equality
    simpa only [Nat.cast_add, Nat.cast_one] using equality.symm
  · rw [ite_eq_right (by simpa only [Finset.mem_range] using (by omega : ¬ position + 1 < degree + 2))] at equality
    rw [component_above data degree (position + 1) (by omega), smul_zero]
    exact equality.symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialLadder
