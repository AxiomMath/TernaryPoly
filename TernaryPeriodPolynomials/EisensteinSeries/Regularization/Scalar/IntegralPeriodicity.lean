module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.HolomorphicDecay
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.Periodicity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryUnipotent_integer_adelic (integer : ℤ) :
    GeneralLinearGroup.map rationalAdele (binaryUnipotent (integer : ℚ)) =
      atInfinity (binaryUnipotent (integer : ℝ)) * atFinite (binaryUnipotent (integer : FiniteAdeles)) := by
  rw [map_binaryUnipotent, map_intCast]
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, atFinite, combineGL, pairMatrix, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two] <;> rfl

theorem cusp_realize_integer_translation (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (integer : ℤ)
    (fixed : cuspSmoothAction cusp (atFinite (binaryUnipotent (integer : FiniteAdeles))) vector = vector)
    (matrix : BinaryRealGL) :
    cusp.realize vector (atInfinity (binaryUnipotent (integer : ℝ)) * atInfinity matrix) =
      cusp.realize vector (atInfinity matrix) := by
  have finite_identity (argument : BinaryAdelicGL) :=
    cusp.equivariant (atFinite (binaryUnipotent (integer : FiniteAdeles))) vector argument
  change ∀ argument, cusp.realize (cuspSmoothAction cusp (atFinite (binaryUnipotent (integer : FiniteAdeles))) vector) argument = _
    at finite_identity
  simp only [fixed] at finite_identity
  calc
    _ = cusp.realize vector ((atInfinity (binaryUnipotent (integer : ℝ)) * atInfinity matrix) *
        atFinite (binaryUnipotent (integer : FiniteAdeles))) := finite_identity _
    _ = cusp.realize vector (GeneralLinearGroup.map rationalAdele (binaryUnipotent (integer : ℚ)) *
        atInfinity matrix) := by
      rw [binaryUnipotent_integer_adelic, mul_assoc, binary_atInfinity_atFinite_commute matrix, ← mul_assoc]
    _ = _ := cusp.leftRational _ vector _

theorem binaryUpperHalfPoint_add_real (point : ℂ) (positive : 0 < point.im) (shift : ℝ) :
    binaryUpperHalfPoint (point + (shift : ℂ)) = binaryUnipotent shift * binaryUpperHalfPoint point := by
  have shifted_positive : 0 < (point + (shift : ℂ)).im := by simpa using positive
  apply Units.ext
  rw [Units.val_mul, binaryUpperHalfPoint_val _ shifted_positive, binaryUpperHalfPoint_val point positive]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUpperHalfMatrix, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem cuspHolomorphicFunction_integer_period (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cusp.smooth) (integer : ℤ)
    (fixed : cuspSmoothAction cusp (atFinite (binaryUnipotent (integer : FiniteAdeles))) vector = vector)
    (point : ℂ) (positive : 0 < point.im) :
    cuspHolomorphicFunction cusp weight vector 1 (point + (integer : ℂ)) =
      cuspHolomorphicFunction cusp weight vector 1 point := by
  have shifted : point + (integer : ℂ) = point + ((integer : ℝ) : ℂ) := by simp
  rw [shifted, cuspHolomorphicFunction, cuspHolomorphicFunction]
  simp only [Complex.add_im, Complex.ofReal_im, add_zero]
  congr 1
  simp only [cuspUpperHalfOrbit_apply, one_mul, binaryUpperHalfPoint_add_real point positive,
    binary_atInfinity_mul, cusp_realize_integer_translation cusp vector integer fixed]

theorem cuspUpperHalfForm_integer_periodic (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cusp.smooth) (integer : ℤ)
    (fixed : cuspSmoothAction cusp (atFinite (binaryUnipotent (integer : FiniteAdeles))) vector = vector) :
    Function.Periodic (cuspUpperHalfForm cusp weight vector 1 ∘ UpperHalfPlane.ofComplex) (integer : ℂ) := by
  intro point
  by_cases positive : 0 < point.im
  · have shifted_positive : 0 < (point + (integer : ℂ)).im := by simpa using positive
    simp only [Function.comp_def, UpperHalfPlane.ofComplex_apply_eq_ite,
      dite_eq_left positive, dite_eq_left shifted_positive, cuspUpperHalfForm, UpperHalfPlane.coe_mk]
    exact cuspHolomorphicFunction_integer_period cusp weight vector integer fixed point positive
  · have shifted_nonpositive : ¬ 0 < (point + (integer : ℂ)).im := by simpa using positive
    simp only [Function.comp_def, UpperHalfPlane.ofComplex_apply_eq_ite,
      dite_eq_right positive, dite_eq_right shifted_nonpositive]

theorem binaryUnipotent_three_mem_principal :
    binaryUnipotent (3 : FiniteAdeles) ∈ binaryPrincipalLevel := by
  refine ⟨binaryUnipotent (3 : IntegralAdeles), ?_, ?_⟩
  · change GeneralLinearGroup.map integralReduction (binaryUnipotent (3 : IntegralAdeles)) = 1
    rw [map_binaryUnipotent, map_ofNat]
    rw [show (3 : ZMod 3) = 0 from by decide]
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [binaryUnipotent]
  · rw [map_binaryUnipotent, map_ofNat]

theorem cuspUpperHalfForm_principal_periodic (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) :
    Function.Periodic (cuspUpperHalfForm cusp weight vector.val 1 ∘ UpperHalfPlane.ofComplex) (3 : ℂ) := by
  have fixed : cuspSmoothAction cusp (atFinite (binaryUnipotent (3 : FiniteAdeles))) vector.val = vector.val :=
    Subtype.ext (vector.property ⟨_, binaryUnipotent_three_mem_principal⟩)
  exact cuspUpperHalfForm_integer_periodic cusp weight vector.val 3 fixed

theorem cohomological_principal_lowest_exp_decay {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ) (weight_positive : 0 < weight)
    (vector : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (rotation : cuspRotationOperator cusp vector.val = (Complex.I * (weight : ℂ)) • vector.val)
    (lowering : cuspLoweringOperator cusp vector.val = 0) :
    cuspUpperHalfForm cusp weight vector.val 1 =O[UpperHalfPlane.atImInfty]
      (fun point => Real.exp (-2 * Real.pi * point.im / 3)) := by
  exact cohomological_upperHalfForm_exp_decay_of_periodic cohomological weight weight_positive
    vector.val rotation lowering 1 3 (by norm_num) (cuspUpperHalfForm_principal_periodic cusp weight vector)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
