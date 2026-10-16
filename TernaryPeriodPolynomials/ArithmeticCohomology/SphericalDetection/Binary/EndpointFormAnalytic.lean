module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointForm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryMonomialBasis_weightExponent (degree : ℕ) (position : Fin (degree + 1)) :
    (binaryMonomialBasis degree (binaryWeightExponent degree position)).val =
      X 0 ^ position.val * X 1 ^ (degree - position.val) := by
  rw [binaryMonomialBasis_coe, monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two,
    binaryWeightExponent_first, binaryWeightExponent_second]

theorem binaryPointPower_expansion (degree : ℕ) (point : ℂ) :
    binaryPointPower degree point =
      ∑ position : Fin (degree + 1),
        (((degree.choose position.val : ℕ) : ℂ) * (-point) ^ (degree - position.val)) •
          binaryMonomialBasis degree (binaryWeightExponent degree position) := by
  apply Subtype.ext
  simp only [binaryPointPower, Submodule.coe_sum, Submodule.coe_smul,
    binaryMonomialBasis_weightExponent, Algebra.smul_def, algebraMap_eq]
  rw [show (X 0 - C point * X 1 : Binary.Poly) = X 0 + C (-point) * X 1 by rw [map_neg]; ring,
    add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro position _
  simp only [mul_pow, map_mul, map_natCast, map_pow]
  ring

theorem binaryPointPower_functional_analytic (degree : ℕ)
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) (point : ℂ) :
    AnalyticAt ℂ (fun argument => functional (binaryPointPower degree argument)) point := by
  have equality : (fun argument => functional (binaryPointPower degree argument)) =
      fun argument => ∑ position : Fin (degree + 1),
        (((degree.choose position.val : ℕ) : ℂ) * (-argument) ^ (degree - position.val)) *
          functional (binaryMonomialBasis degree (binaryWeightExponent degree position)) := by
    funext argument
    rw [binaryPointPower_expansion, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [equality]
  fun_prop

theorem binaryEndpointHolomorphicForm_holomorphic (cusp : CuspidalRepresentation)
    (degree : ℕ) (halfWeight : ℤ) (vector : cusp.H)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet) :
    DifferentiableOn ℂ (binaryEndpointHolomorphicForm cusp degree halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet := by
  intro point member
  apply differentiableWithinAt_pi.mpr
  intro position
  exact (binaryPointPower_functional_analytic (degree + 1)
    ((binaryWeightBasis (degree + 1)).coord position) point).differentiableAt.differentiableWithinAt.smul
      (holomorphic point member)

theorem binaryRelativeLowerEndpoint_holomorphic (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (odd : Odd degree)
    (cohomological : Cohomological cusp degree) (level : Subgroup BinaryFiniteGL)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_mem : ∀ position, lower position ∈ cuspFiniteWeightValues cusp level
      (binaryUnitaryWeight degree (-2) position))
    (upper_mem : ∀ position, upper position ∈ cuspFiniteWeightValues cusp level
      (binaryUnitaryWeight degree 2 position))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper) :
    DifferentiableOn ℂ (binaryEndpointHolomorphicForm cusp degree halfWeight (lower 0).val)
      UpperHalfPlane.upperHalfPlaneSet := by
  have killed := (binaryRelative_endpoint_kernels cusp spherical odd cohomological level
    lower upper lower_mem upper_mem closed).1
  rw [← weight] at killed
  exact binaryEndpointHolomorphicForm_holomorphic cusp degree halfWeight (lower 0).val
    (cuspWeightedAffineOrbit_holomorphic cusp halfWeight (lower 0).val
      ((lower 0).property.differentiableOn (by simp)) (congrArg Subtype.val killed))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
