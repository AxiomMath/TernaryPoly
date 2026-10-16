module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialParity

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspPeriodParity_not_mem_endpointSpan {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree parity : ℕ) (position : Fin (degree + 1))
    (left : position ≠ 0) (right : position ≠ Fin.last degree)
    (same_parity : Even (parity + degree - position.val))
    (moment_nonzero : cuspImaginaryMoment form (degree - position.val) ≠ 0) :
    binaryParityComponent degree parity (cuspPeriodPolynomial form degree) ∉ binaryEndpointPolynomialSpan degree := by
  intro member
  have vanishing := binaryEndpointPolynomialSpan_coord_zero degree _ member position left right
  rw [binaryParityComponent_coord_preserved degree parity _ position same_parity] at vanishing
  exact cuspPeriodPolynomial_coord_ne_zero form degree position moment_nonzero vanishing

/-- Both parities have a nonzero interior coefficient, so neither can be an endpoint polynomial. -/
theorem levelOneCuspForm_periodParity_nonzero {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree) :
    binaryParityComponent degree 0 (cuspPeriodPolynomial form degree) ∉ binaryEndpointPolynomialSpan degree ∧
      binaryParityComponent degree 1 (cuspPeriodPolynomial form degree) ∉ binaryEndpointPolynomialSpan degree := by
  have large := levelOneCuspForm_weight_ge_twelve form nonzero
  have degree_large : 10 ≤ degree := by omega
  obtain ⟨first_moment, second_moment⟩ := levelOneCuspForm_interiorMoments_ne_zero form nonzero eigenvalues relations
  have first_index : (weight - 4).toNat = degree - 2 := by omega
  have second_index : (weight - 3).toNat = degree - 1 := by omega
  rw [first_index] at first_moment
  rw [second_index] at second_moment
  let first : Fin (degree + 1) := ⟨2, by omega⟩
  let second : Fin (degree + 1) := ⟨1, by omega⟩
  have first_left : first ≠ 0 := by intro equality; have := congrArg Fin.val equality; simp [first] at this
  have first_right : first ≠ Fin.last degree := by
    intro equality
    have := congrArg Fin.val equality
    change 2 = degree at this
    omega
  have second_left : second ≠ 0 := by intro equality; have := congrArg Fin.val equality; simp [second] at this
  have second_right : second ≠ Fin.last degree := by
    intro equality
    have := congrArg Fin.val equality
    change 1 = degree at this
    omega
  constructor
  · apply cuspPeriodParity_not_mem_endpointSpan form degree 0 first first_left first_right _ first_moment
    change Even (0 + degree - 2)
    obtain ⟨half, equality⟩ := even
    exact ⟨half - 1, by omega⟩
  · apply cuspPeriodParity_not_mem_endpointSpan form degree 1 second second_left second_right _ second_moment
    change Even (1 + degree - 1)
    simpa only [Nat.add_sub_cancel_left] using even

end TernaryPeriodPolynomials.SphericalDetection.Helpers
