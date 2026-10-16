module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialParity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PolynomialDerivativeKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ShearExponential

@[expose] public section


open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem homogeneousShear_fixed_iff {degree : ℕ} (coordinate multiplier : Fin 3)
    (distinct : multiplier ≠ coordinate) (scalar : ℂ) (nonzero : scalar ≠ 0)
    (polynomial : HomogeneousPoly degree) :
    MvPolynomial.bind₁
        (fun index => X index + if index = coordinate then C scalar * X multiplier else 0)
        polynomial.val = polynomial.val ↔ pderiv coordinate polynomial.val = 0 := by
  have kernel := nilpotent_difference_kernel
    (scalar • homogeneousShearDerivation degree coordinate multiplier) degree
    (homogeneousShearDerivation_smul_power_zero degree coordinate multiplier scalar distinct) polynomial
  have fixed : (IsNilpotent.exp (scalar • homogeneousShearDerivation degree coordinate multiplier) - 1)
      polynomial = 0 ↔ MvPolynomial.bind₁
        (fun index => X index + if index = coordinate then C scalar * X multiplier else 0)
        polynomial.val = polynomial.val := by
    change _ - polynomial = 0 ↔ _
    rw [sub_eq_zero, Subtype.ext_iff, homogeneousShearDerivation_exponential_coe _ _ _ _ distinct,
      shearPolynomialCurve_eval_one]
  rw [exp_inst_irrel _ Algebra.toModule] at fixed
  refine fixed.symm.trans (kernel.trans ?_)
  constructor
  · intro vanishing
    have value := congrArg Subtype.val vanishing
    change scalar • (X multiplier * pderiv coordinate polynomial.val) = 0 at value
    exact (mul_eq_zero.mp ((smul_eq_zero.mp value).resolve_left nonzero)).resolve_left (X_ne_zero multiplier)
  · intro vanishing
    apply Subtype.ext
    change scalar • (X multiplier * pderiv coordinate polynomial.val) = 0
    rw [vanishing, mul_zero, smul_zero]

theorem binaryPolynomialLift_shear (scalar : ℂ) (polynomial : Binary.Poly) :
    binaryPolynomialLift (Binary.substitute !![1, scalar; 0, 1] polynomial) =
      MvPolynomial.bind₁
        (fun index : Fin 3 => X index + if index = 0 then C scalar * X 1 else 0)
        (binaryPolynomialLift polynomial) := by
  have equality : binaryPolynomialLift.comp (Binary.substitute !![1, scalar; 0, 1]) =
      (MvPolynomial.bind₁
        (fun index : Fin 3 => X index + if index = 0 then C scalar * X 1 else 0)).comp
        binaryPolynomialLift := by
    apply MvPolynomial.algHom_ext
    intro index
    fin_cases index <;>
      simp [binaryPolynomialLift, Binary.substitute, Binary.linearForm, Fin.sum_univ_two]
  exact DFunLike.congr_fun equality polynomial

theorem binaryTranslation_fixed_iff {degree : ℕ} (scalar : ℂ) (nonzero : scalar ≠ 0)
    (polynomial : Binary.HomogeneousPoly degree) :
    Binary.substitute !![1, scalar; 0, 1] polynomial.val = polynomial.val ↔
      pderiv 0 polynomial.val = 0 := by
  have equivalence := homogeneousShear_fixed_iff 0 1 (by decide) scalar nonzero
    (binaryHomogeneousLift degree polynomial)
  have derivative : pderiv (0 : Fin 3) (binaryPolynomialLift polynomial.val) =
      binaryPolynomialLift (pderiv 0 polynomial.val) :=
    pderiv_rename (Fin.castSucc_injective 2) 0 polynomial.val
  change MvPolynomial.bind₁
      (fun index : Fin 3 => X index + if index = 0 then C scalar * X 1 else 0)
      (binaryPolynomialLift polynomial.val) = binaryPolynomialLift polynomial.val ↔
    pderiv (0 : Fin 3) (binaryPolynomialLift polynomial.val) = 0 at equivalence
  rw [← binaryPolynomialLift_shear, derivative, ← map_zero binaryPolynomialLift,
    binaryPolynomialLift_injective.eq_iff, binaryPolynomialLift_injective.eq_iff] at equivalence
  exact equivalence

theorem binaryHomogeneous_pderiv_zero {degree : ℕ} (polynomial : Binary.HomogeneousPoly degree)
    (vanishing : pderiv 0 polynomial.val = 0) :
    polynomial = polynomial.val.coeff (Finsupp.single 1 degree) • binaryStandardBasis degree 0 := by
  have support_single (exponent : Fin 2 →₀ ℕ) (nonzero : polynomial.val.coeff exponent ≠ 0) :
      exponent = Finsupp.single 1 degree := by
    have first := mem_support_notMem_vars_zero (mem_support_iff.mpr nonzero)
      (pderiv_zero_notMem_vars 0 polynomial.val vanishing)
    have equality : exponent = Finsupp.single 1 (exponent 1) := by
      ext coordinate
      fin_cases coordinate <;> simp [first]
    have total : exponent.degree = degree := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using polynomial.property nonzero
    rw [equality, Finsupp.degree_single] at total
    exact equality.trans (congrArg (Finsupp.single 1) total)
  apply Subtype.ext
  simp only [Submodule.coe_smul, binaryStandardBasis_coe, Fin.val_zero, pow_zero, one_mul,
    Nat.sub_zero, Algebra.smul_def, MvPolynomial.algebraMap_eq, C_mul_X_pow_eq_monomial]
  apply MvPolynomial.ext
  intro exponent
  by_cases equal : Finsupp.single 1 degree = exponent
  · subst exponent
    simp
  · have zero : polynomial.val.coeff exponent = 0 := by
      by_contra nonzero
      exact equal (support_single exponent nonzero).symm
    simp only [coeff_monomial, ite_eq_right equal, zero]

theorem binaryTranslation_fixed_iff_scalar {degree : ℕ} (scalar : ℂ) (nonzero : scalar ≠ 0)
    (polynomial : Binary.HomogeneousPoly degree) :
    Binary.substitute !![1, scalar; 0, 1] polynomial.val = polynomial.val ↔
      ∃ constant : ℂ, polynomial = constant • binaryStandardBasis degree 0 := by
  rw [binaryTranslation_fixed_iff scalar nonzero]
  constructor
  · intro vanishing
    exact ⟨_, binaryHomogeneous_pderiv_zero polynomial vanishing⟩
  · rintro ⟨constant, rfl⟩
    simp [binaryStandardBasis_coe]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
