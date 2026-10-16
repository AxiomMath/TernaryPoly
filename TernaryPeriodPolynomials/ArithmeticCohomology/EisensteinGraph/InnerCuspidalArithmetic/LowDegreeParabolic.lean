module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.LowDegreeParabolic

open Helpers ArithmeticGenerators

def exponent (first second : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 first + Finsupp.single 1 second

theorem quadratic_expansion (polynomial : Binary.HomogeneousPoly 2) :
    polynomial.val = C (polynomial.val.coeff (exponent 2 0)) * X 0 ^ 2 +
      C (polynomial.val.coeff (exponent 1 1)) * (X 0 * X 1) +
      C (polynomial.val.coeff (exponent 0 2)) * X 1 ^ 2 := by
  have firstSecond : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 ≠ Finsupp.single 0 2 := by
    intro equality
    have coordinate := congrArg (fun value : Fin 2 →₀ ℕ => value 0) equality
    norm_num at coordinate
  have secondThird : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 ≠ Finsupp.single 1 2 := by
    intro equality
    have coordinate := congrArg (fun value : Fin 2 →₀ ℕ => value 0) equality
    norm_num at coordinate
  have firstThird : Finsupp.single (0 : Fin 2) 2 ≠ Finsupp.single 1 2 := by
    intro equality
    have coordinate := congrArg (fun value : Fin 2 →₀ ℕ => value 0) equality
    norm_num at coordinate
  apply MvPolynomial.ext
  intro monomial
  by_cases degree : Finsupp.degree monomial = 2
  · have coordinates : monomial 0 + monomial 1 = 2 := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using degree
    have cases : monomial = exponent 2 0 ∨ monomial = exponent 1 1 ∨ monomial = exponent 0 2 := by
      by_cases first : monomial 0 = 0
      · right
        right
        ext index
        fin_cases index <;> simp [exponent, first, show monomial 1 = 2 by omega]
      · by_cases second : monomial 0 = 1
        · right
          left
          ext index
          fin_cases index <;> simp [exponent, second, show monomial 1 = 1 by omega]
        · left
          ext index
          fin_cases index <;> simp [exponent, show monomial 0 = 2 by omega, show monomial 1 = 0 by omega]
    rcases cases with first | second | third
    · subst monomial
      simp [exponent, X, monomial_mul_monomial, monomial_pow,
        firstSecond, Ne.symm firstThird]
    · subst monomial
      simp [exponent, X, monomial_mul_monomial, monomial_pow,
        Ne.symm firstSecond, Ne.symm secondThird]
    · subst monomial
      simp [exponent, X, monomial_mul_monomial, monomial_pow, firstThird, secondThird]
  · have coefficientZero : polynomial.val.coeff monomial = 0 := by
      have homogeneous := polynomial.property
      rw [← homogeneousComponent_eq_self homogeneous]
      simp [coeff_homogeneousComponent, degree]
    rw [coefficientZero]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, coeff_X_pow]
    have first : Finsupp.single (0 : Fin 2) 2 ≠ monomial := by
      intro equality
      subst monomial
      exact degree (by simp)
    have third : Finsupp.single (1 : Fin 2) 2 ≠ monomial := by
      intro equality
      subst monomial
      exact degree (by simp)
    have second : exponent 1 1 ≠ monomial := by
      intro equality
      subst monomial
      exact degree (by simp [exponent])
    have secondExpanded : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 ≠ monomial := second
    simp only [first, third, ite_false, mul_zero, add_zero, X, monomial_mul_monomial,
      one_mul, coeff_monomial, secondExpanded]

theorem quadratic_action (matrix : binaryArithmeticLevel) (polynomial : Binary.HomogeneousPoly 2) :
    (binaryArithmeticRepresentation 1 matrix polynomial).val =
      C (polynomial.val.coeff (exponent 2 0)) *
        (C (matrix.val.inv 0 0 : ℂ) * X 0 + C (matrix.val.inv 0 1 : ℂ) * X 1) ^ 2 +
      C (polynomial.val.coeff (exponent 1 1)) *
        ((C (matrix.val.inv 0 0 : ℂ) * X 0 + C (matrix.val.inv 0 1 : ℂ) * X 1) *
          (C (matrix.val.inv 1 0 : ℂ) * X 0 + C (matrix.val.inv 1 1 : ℂ) * X 1)) +
      C (polynomial.val.coeff (exponent 0 2)) *
        (C (matrix.val.inv 1 0 : ℂ) * X 0 + C (matrix.val.inv 1 1 : ℂ) * X 1) ^ 2 := by
  change Binary.action 0 (binaryIntegralComplex matrix.val) polynomial.val = _
  rw [Binary.action_apply]
  change (1 : ℂ) • Binary.substitute (binaryIntegralComplex matrix.val)⁻¹.val polynomial.val = _
  rw [one_smul]
  have inverse : (binaryIntegralComplex matrix.val)⁻¹ = binaryIntegralComplex matrix.val⁻¹ :=
    (map_inv binaryIntegralComplex matrix.val).symm
  have entries : ∀ row column, ((binaryIntegralComplex matrix.val)⁻¹).val row column =
      (matrix.val.inv row column : ℂ) := by
    intro row column
    rw [inverse]
    rfl
  have constants : ∀ coefficient : ℂ,
      Binary.substitute ((binaryIntegralComplex matrix.val)⁻¹).val (C coefficient) = C coefficient := by
    intro coefficient
    simp [Binary.substitute]
  conv_lhs => rw [quadratic_expansion]
  simp only [map_add, map_mul, map_pow, constants, Binary.substitute_X,
    Binary.linearForm, Fin.sum_univ_two, entries]

theorem quadratic_coefficients_zero (polynomial : Binary.HomogeneousPoly 2)
    (first : polynomial.val.coeff (exponent 2 0) = 0)
    (second : polynomial.val.coeff (exponent 1 1) = 0)
    (third : polynomial.val.coeff (exponent 0 2) = 0) : polynomial = 0 := by
  apply Subtype.ext
  rw [quadratic_expansion, first, second, third]
  simp

theorem quadratic_upper_reflection_zero (polynomial : Binary.HomogeneousPoly 2)
    (upperFixed : binaryArithmeticRepresentation 1 (upper 1) polynomial = polynomial)
    (reflectionNeg : binaryArithmeticRepresentation 1 reflection polynomial = -polynomial) :
    polynomial = 0 := by
  have upperEquation := congrArg Subtype.val upperFixed
  have reflectionEquation := congrArg Subtype.val reflectionNeg
  rw [quadratic_action] at upperEquation reflectionEquation
  have upperFirst := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → ℂ)) upperEquation
  have upperSecond := congrArg (MvPolynomial.eval (![1, 1] : Fin 2 → ℂ)) upperEquation
  have reflectionThird := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → ℂ)) reflectionEquation
  conv_rhs at upperFirst => rw [quadratic_expansion]
  conv_rhs at upperSecond => rw [quadratic_expansion]
  change _ = MvPolynomial.eval (![0, 1] : Fin 2 → ℂ) (-polynomial.val) at reflectionThird
  conv_rhs at reflectionThird => rw [quadratic_expansion]
  norm_num [upper, reflection] at upperFirst upperSecond reflectionThird
  apply quadratic_coefficients_zero polynomial
  · linear_combination (1 / 2 : ℂ) * upperFirst + (1 / 2 : ℂ) * upperSecond
  · linear_combination - (1 / 2 : ℂ) * upperFirst + (1 / 2 : ℂ) * upperSecond
  · linear_combination (1 / 2 : ℂ) * reflectionThird

private theorem pullback_primitive {Source Target Value : Type} [Group Source] [Group Target]
    [AddCommGroup Value] [Module ℂ Value] (homomorphism : Source →* Target)
    (representation : Representation ℂ Target Value) (cycle : crossedCocycles representation)
    (restricted : crossedPullbackH1 homomorphism representation
      ((crossedBoundaries representation).mkQ cycle) = 0) (element : Source) :
    ∃ primitive : Value,
      cycle.val (homomorphism element) = representation (homomorphism element) primitive - primitive := by
  rw [crossedPullbackH1_mk] at restricted
  obtain ⟨primitive, boundary⟩ := (Submodule.Quotient.mk_eq_zero _).mp restricted
  refine ⟨primitive, ?_⟩
  have pointwise := congrArg
    (fun value : crossedCocycles (representation.comp homomorphism) => value.val element) boundary
  exact pointwise.symm

theorem parabolic_generator_primitive {degree : ℕ}
    (cycle : crossedCocycles (binaryArithmeticRepresentation degree))
    (parabolic : (crossedBoundaries (binaryArithmeticRepresentation degree)).mkQ cycle ∈
      binaryParabolicH1 degree) (frame : GeneralLinearGroup (Fin 2) ℚ)
    (generator : binaryArithmeticLevel) (membership : generator ∈ binaryCuspLevel frame) :
    ∃ primitive : Binary.HomogeneousPoly (degree + 1),
      cycle.val generator = binaryArithmeticRepresentation degree generator primitive - primitive := by
  have restricted := (Submodule.mem_iInf
    (M := CrossedH1 (binaryArithmeticRepresentation degree)) _).mp parabolic frame
  exact pullback_primitive (binaryCuspLevel frame).subtype
    (binaryArithmeticRepresentation degree) cycle restricted ⟨generator, membership⟩

theorem upper_cusp : upper 1 ∈ binaryCuspLevel 1 := by
  apply (mem_binaryCuspLevel_iff _ _).mpr
  simp [upper]

def oppositeFrame : GeneralLinearGroup (Fin 2) ℚ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem lower_cusp : lower (-1) ∈ binaryCuspLevel oppositeFrame := by
  apply (mem_binaryCuspLevel_iff _ _).mpr
  change ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) *
    (!![1, 0; -3, 1] : Matrix (Fin 2) (Fin 2) ℚ) *
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem elliptic_cube : (upper 1 * lower (-1)) ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [pow_succ, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem cocycle_cube {GroupType Value : Type} [Group GroupType] [AddCommGroup Value] [Module ℂ Value]
    (representation : Representation ℂ GroupType Value) (cycle : crossedCocycles representation)
    (element : GroupType) (cube : element ^ 3 = 1) :
    cycle.val element + representation element (cycle.val element) +
      representation (element ^ 2) (cycle.val element) = 0 := by
  have first := cycle.property element element
  have second := cycle.property (element * element) element
  rw [← pow_two] at first
  rw [← pow_two, ← pow_succ, cube, crossedCocycle_one, first] at second
  exact second.symm

private theorem quadratic_eval_zero_one (polynomial : Binary.HomogeneousPoly 2) :
    MvPolynomial.eval (![0, 1] : Fin 2 → ℂ) polynomial.val =
      polynomial.val.coeff (exponent 0 2) := by
  conv_lhs => rw [quadratic_expansion]
  simp only [map_add, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]
  norm_num

theorem lower_cocycle_quadratic_relation
    (cycle : crossedCocycles (binaryArithmeticRepresentation 1))
    (upperZero : cycle.val (upper 1) = 0)
    (parabolic : (crossedBoundaries (binaryArithmeticRepresentation 1)).mkQ cycle ∈ binaryParabolicH1 1) :
    (cycle.val (lower (-1))).val.coeff (exponent 0 2) = 0 ∧
      2 * (cycle.val (lower (-1))).val.coeff (exponent 2 0) =
        3 * (cycle.val (lower (-1))).val.coeff (exponent 1 1) := by
  obtain ⟨primitive, primitiveFormula⟩ := parabolic_generator_primitive cycle parabolic oppositeFrame
    (lower (-1)) lower_cusp
  have trailing := congrArg (fun value : Binary.HomogeneousPoly 2 =>
    MvPolynomial.eval (![0, 1] : Fin 2 → ℂ) value.val) primitiveFormula
  simp only [Submodule.coe_sub, map_sub] at trailing
  rw [quadratic_eval_zero_one, quadratic_action, quadratic_eval_zero_one] at trailing
  norm_num [lower] at trailing
  have ellipticValue := cycle.property (upper 1) (lower (-1))
  rw [upperZero, zero_add] at ellipticValue
  have normZero := cocycle_cube (binaryArithmeticRepresentation 1) cycle _ elliptic_cube
  rw [ellipticValue] at normZero
  have evaluated := congrArg (fun value : Binary.HomogeneousPoly 2 =>
    MvPolynomial.eval (![0, 1] : Fin 2 → ℂ) value.val) normZero
  simp only [Submodule.coe_add, Submodule.coe_zero, map_add, map_zero] at evaluated
  rw [quadratic_action] at evaluated
  have actionProduct (matrix : binaryArithmeticLevel) (polynomial : Binary.HomogeneousPoly 2) :
      binaryArithmeticRepresentation 1 matrix
        (binaryArithmeticRepresentation 1 (upper 1) polynomial) =
      binaryArithmeticRepresentation 1 (matrix * upper 1) polynomial := by
    rw [map_mul, Module.End.mul_apply]
  rw [actionProduct, actionProduct, quadratic_action, quadratic_action] at evaluated
  norm_num [upper, lower, pow_two, Matrix.mul_apply, Fin.sum_univ_two] at evaluated
  have trailing' : (cycle.val (lower (-1))).val.coeff (exponent 0 2) = 0 := by
    simpa [lower] using trailing
  refine ⟨trailing', ?_⟩
  change _ = 0 at evaluated
  have normalized : 2 * (cycle.val (lower (-1))).val.coeff (exponent 2 0) -
      3 * (cycle.val (lower (-1))).val.coeff (exponent 1 1) +
      6 * (cycle.val (lower (-1))).val.coeff (exponent 0 2) = 0 := by
    convert evaluated using 1
    simp [lower]
    ring
  linear_combination normalized - 6 * trailing'

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.LowDegreeParabolic
