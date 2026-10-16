module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.CentralCharacter
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CohomologicalCenter
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.FinitePlaneValues

@[expose] public section


/-!
# Source cocycles are invariant under positive central scaling of all vertices

At the cohomological point the centre of `GL₃(ℝ)` acts trivially on the coefficients of a plane
source cocycle (trivial character, positive real scalars): the induced sections pick up
`λ^{n+3}` and the coefficient representation `λ^{-(n+3)}`. Hence
`c (λ x₀, λ x₁, λ x₂) = c (x₀, x₁, x₂)` for `λ > 0`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Scaling every variable of a homogeneous ternary polynomial. -/
theorem ternary_homogeneous_scale {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (scalar : ℂ) :
    MvPolynomial.bind₁ (fun index : Fin 3 => MvPolynomial.C scalar * MvPolynomial.X index)
      polynomial.val = scalar ^ degree • polynomial.val := by
  classical
  have homogeneous : polynomial.val.IsHomogeneous degree := polynomial.property
  conv_lhs => rw [polynomial.val.as_sum]
  rw [map_sum]
  conv_rhs => rw [polynomial.val.as_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro monomial membership
  rw [MvPolynomial.bind₁_monomial]
  have degreeEquality : ∑ index ∈ monomial.support, monomial index = degree := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using
      homogeneous (MvPolynomial.mem_support_iff.mp membership)
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    Finset.prod_pow_eq_pow_sum, degreeEquality]
  rw [MvPolynomial.monomial_eq, ← MvPolynomial.C_mul']
  change _ = _ * (_ * ∏ index ∈ monomial.support, MvPolynomial.X index ^ monomial index)
  ring

/-- The coefficient representation on a positive real scalar. -/
theorem realCoefficientComponent_scalar (degree : ℕ) (scalar : ℝˣ)
    (polynomial : HomogeneousPoly degree) :
    realCoefficientComponent degree trivialCharacter (GeneralLinearGroup.scalar (Fin 3) scalar)
        polynomial = ((scalar.val : ℂ)⁻¹ ^ (degree + 3)) • polynomial := by
  have character :
      componentCharacter trivialCharacter (GeneralLinearGroup.scalar (Fin 3) scalar) = 1 := rfl
  change componentCharacter trivialCharacter (GeneralLinearGroup.scalar (Fin 3) scalar) •
    realCoefficient degree (GeneralLinearGroup.scalar (Fin 3) scalar) polynomial = _
  rw [character, one_smul]
  change homogeneousAction degree (-1)
    (GeneralLinearGroup.map (algebraMap ℝ ℂ) (GeneralLinearGroup.scalar (Fin 3) scalar))
      polynomial = _
  rw [GeneralLinearGroup.map_scalar]
  apply Subtype.ext
  rw [homogeneousAction_coe, action_apply]
  change (((GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3)
    (Units.map (algebraMap ℝ ℂ) scalar)) : ℂˣ) : ℂ) ^ (-1 : ℤ)) • _ = _
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]
  rw [← (GeneralLinearGroup.scalar (Fin 3)).map_inv, GeneralLinearGroup.coe_scalar]
  simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_map]
  have form : linearForm (Matrix.scalar (Fin 3) ((scalar.val : ℂ)⁻¹)) =
      fun index => MvPolynomial.C ((scalar.val : ℂ)⁻¹) * MvPolynomial.X index := by
    funext index
    fin_cases index <;> simp [linearForm, Matrix.scalar_apply, Matrix.diagonal_apply,
      Fin.sum_univ_three]
  change (((scalar.val : ℂ) ^ 3) ^ (-1 : ℤ)) •
    MvPolynomial.bind₁ (linearForm (Matrix.scalar (Fin 3) ((scalar.val : ℂ)⁻¹))) polynomial.val = _
  rw [form, ternary_homogeneous_scale, smul_smul, zpow_neg_one]
  simp only [← inv_pow]
  congr 1
  rw [← pow_add]
  congr 1
  omega

theorem atInfinity_scalar_three (scalar : ℝˣ) :
    atInfinity (GeneralLinearGroup.scalar (Fin 3) scalar) =
      GeneralLinearGroup.scalar (Fin 3) (realAdeleUnit scalar) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  by_cases equality : row = column <;>
    simp [atInfinity, combineGL, pairMatrix, realAdeleUnit,
      Matrix.GeneralLinearGroup.scalar, Matrix.scalar, equality]

/-- **Positive central scaling of all vertices leaves a plane source cocycle unchanged.** -/
theorem source_scalar_invariant {degree : ℕ} (data : InducingData degree)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (scalar : ℝˣ) (positive : 0 < scalar.val)
    (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    source (fun index => GeneralLinearGroup.scalar (Fin 3) scalar * vertices index) argument =
      source vertices argument := by
  rw [cocycle.2.2.1, atInfinity_scalar_three, ← GeneralLinearGroup.scalar_commute,
    trivial, realCoefficientComponent_scalar]
  have central :=
    cohomological_centralCharacter_positive data.cusp data.cohomological scalar positive
  have norm : normPower (realAdeleUnit scalar) ((degree : ℂ) + 3) =
      (scalar.val : ℂ) ^ (degree + 3) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat, abs_of_pos positive] using
      PlaneEisensteinContinuation.CohomologicalCenter.normPower_real_nat scalar (degree + 3)
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  have value := EisensteinRegularization.Helpers.induced_central_character
    (cocycle.1 vertices monomial) (realAdeleUnit scalar) argument
  rw [trivial, central, norm] at value
  rw [Submodule.coe_smul, MvPolynomial.coeff_smul, value]
  simp only [trivialCharacter, MonoidHom.one_apply, one_mul, smul_eq_mul]
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr scalar.ne_zero),
    one_pow, one_mul]

end TernaryPeriodPolynomials.AnalyticClasses
