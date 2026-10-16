module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.Norm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem homogeneous_scalar_substitution {indices : Type} {degree : ℕ}
    (polynomial : MvPolynomial indices ℂ) (homogeneous : polynomial.IsHomogeneous degree)
    (scalar : ℂ) :
    aeval (fun index => C scalar * X index) polynomial = scalar ^ degree • polynomial := by
  classical
  conv_lhs => rw [polynomial.as_sum]
  conv_rhs => rw [polynomial.as_sum]
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro monomial supported
  have total_degree := homogeneous.degree_eq_sum_deg_support supported
  rw [aeval_monomial, Algebra.smul_def, MvPolynomial.monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    Finset.prod_pow_eq_pow_sum, ← total_degree, MvPolynomial.algebraMap_eq]
  ring

theorem binary_substitute_scalar {degree : ℕ}
    (polynomial : Binary.HomogeneousPoly degree) (scalar : ℂ) :
    Binary.substitute (Matrix.scalar (Fin 2) scalar) polynomial.val =
      scalar ^ degree • polynomial.val := by
  have forms : Binary.linearForm (Matrix.scalar (Fin 2) scalar) =
      fun index => C scalar * X index := by
    funext index
    fin_cases index <;>
      simp [Binary.linearForm, Matrix.scalar_apply, Matrix.diagonal_apply, Fin.sum_univ_two]
  simpa only [Binary.substitute, ← aeval_eq_bind₁, forms] using
    homogeneous_scalar_substitution polynomial.val polynomial.property scalar

theorem binary_homogeneousAction_scalar {degree : ℕ}
    (polynomial : Binary.HomogeneousPoly degree) (unit : ℂˣ) :
    Binary.homogeneousAction degree (-1) (GeneralLinearGroup.scalar (Fin 2) unit)
      polynomial = (unit.val⁻¹) ^ (degree + 2) • polynomial := by
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, Binary.action_apply,
    ← map_inv, GeneralLinearGroup.coe_scalar, binary_substitute_scalar]
  simp only [Binary.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val, zpow_neg_one,
    Units.val_inv_eq_inv_val, Submodule.coe_smul, smul_smul]
  congr 1
  simp only [inv_pow, pow_add, mul_comm]

theorem atInfinity_scalar {dimension : ℕ} (unit : ℝˣ) :
    atInfinity (GeneralLinearGroup.scalar (Fin dimension) unit) =
      GeneralLinearGroup.scalar (Fin dimension) (realAdeleUnit unit) := by
  apply Units.ext
  funext row column
  change ((GeneralLinearGroup.scalar (Fin dimension) unit).val row column,
      (1 : Matrix (Fin dimension) (Fin dimension) FiniteAdeles) row column) =
    (GeneralLinearGroup.scalar (Fin dimension) (realAdeleUnit unit)).val row column
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases same : row = column <;> simp only [same, ite_true, ite_false] <;> rfl

theorem normPower_pow (unit : Adelesˣ) (power : ℕ) (exponent : ℂ) :
    normPower (unit ^ power) exponent = normPower unit ((power : ℂ) * exponent) := by
  simp only [normPower, map_pow, NNReal.coe_pow, Real.log_pow, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  congr 1
  ring

theorem binary_scalar_normalizingFactor (degree : ℕ) (unit : ℝˣ)
    (positive : 0 < unit.val) :
    normPower (GeneralLinearGroup.det
      (atInfinity (GeneralLinearGroup.scalar (Fin 2) unit))) (((degree : ℂ) + 3) / 2) =
      (unit.val : ℂ) ^ (degree + 3) := by
  rw [atInfinity_scalar, GeneralLinearGroup.det_scalar, Fintype.card_fin, normPower_pow,
    normPower_realAdeleUnit_of_pos unit positive]
  have exponent : (2 : ℂ) * (((degree : ℂ) + 3) / 2) = ((degree + 3 : ℕ) : ℂ) := by
    push_cast
    ring
  norm_num only [Nat.cast_ofNat] at *
  rw [exponent, Complex.cpow_natCast]

theorem binaryValues_central {degree : ℕ} (cusp : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : BinaryValues cusp degree values) (unit : Adelesˣ) (argument : BinaryAdelicGL) :
    values (argument * GeneralLinearGroup.scalar (Fin 2) unit) =
      cusp.centralCharacter unit • values argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rcases cuspidal monomial with ⟨vector, realizes⟩
  have central := cusp.central unit vector argument
  rw [GeneralLinearGroup.scalar_commute] at central
  change (values (argument * GeneralLinearGroup.scalar (Fin 2) unit)).val.coeff monomial =
    (cusp.centralCharacter unit • (values argument).val).coeff monomial
  rw [MvPolynomial.coeff_smul]
  simpa only [realizes, smul_eq_mul] using central

theorem binaryCohomologicalAction_positive_scalar {degree : ℕ}
    (cusp : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : BinaryValues cusp degree values) (unit : ℝˣ) (positive : 0 < unit.val)
    (argument : BinaryAdelicGL) :
    binaryCohomologicalAction degree (GeneralLinearGroup.scalar (Fin 2) unit) values argument =
      cusp.centralCharacter (realAdeleUnit unit) • values argument := by
  unfold binaryCohomologicalAction binaryCoefficient
  rw [binary_scalar_normalizingFactor degree unit positive,
    GeneralLinearGroup.map_scalar, binary_homogeneousAction_scalar, atInfinity_scalar,
    binaryValues_central cusp values cuspidal]
  simp only [Units.coe_map, MonoidHom.coe_ofClass, Complex.coe_algebraMap, Nat.add_assoc,
    show 1 + 2 = 3 by rfl, smul_smul, inv_pow]
  have nonzero : (unit.val : ℂ) ^ (degree + 3) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast unit.ne_zero)
  rw [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]

theorem binaryValues_smul {degree : ℕ} (cusp : CuspidalRepresentation)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : BinaryValues cusp degree values) (scalar : ℂ) :
    BinaryValues cusp degree (fun argument => scalar • values argument) := by
  intro monomial
  have membership : (fun argument => scalar • (values argument).val.coeff monomial) ∈ cuspFunctions cusp :=
    (cuspFunctions cusp).smul_mem scalar (cuspidal monomial)
  simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul] using membership

theorem binaryCohomologicalAction_smul (degree : ℕ) (matrix : BinaryRealGL)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (scalar : ℂ) (argument : BinaryAdelicGL) :
    binaryCohomologicalAction degree matrix (fun argument => scalar • values argument)
      argument = scalar • binaryCohomologicalAction degree matrix values argument := by
  simp only [binaryCohomologicalAction, map_smul]
  exact smul_comm _ _ _

theorem cohomological_centralCharacter_positive {degree : ℕ}
    (cusp : CuspidalRepresentation) (cohomological : Cohomological cusp degree)
    (unit : ℝˣ) (positive : 0 < unit.val) :
    cusp.centralCharacter (realAdeleUnit unit) = 1 := by
  by_contra nontrivial
  rcases cohomological with ⟨cycle, cuspidal, _, _, cocycle, nonboundary⟩
  let central := GeneralLinearGroup.scalar (Fin 2) unit
  let eigenvalue := cusp.centralCharacter (realAdeleUnit unit)
  have difference_nonzero : eigenvalue - 1 ≠ 0 := sub_ne_zero.mpr nontrivial
  apply nonboundary
  refine ⟨fun argument => (eigenvalue - 1)⁻¹ • cycle central argument,
    binaryValues_smul cusp (cycle central) (cuspidal central) _, ?_⟩
  intro matrix argument
  have commutation : cycle central argument + eigenvalue • cycle matrix argument =
      cycle matrix argument + binaryCohomologicalAction degree matrix (cycle central)
        argument := by
    have first := cocycle central matrix argument
    have second := cocycle matrix central argument
    rw [GeneralLinearGroup.scalar_commute unit matrix] at first
    rw [binaryCohomologicalAction_positive_scalar cusp (cycle matrix) (cuspidal matrix)
      unit positive argument] at first
    exact first.symm.trans second
  have scaled : (eigenvalue - 1) • cycle matrix argument =
      binaryCohomologicalAction degree matrix (cycle central) argument -
        cycle central argument := by
    calc
      (eigenvalue - 1) • cycle matrix argument =
          eigenvalue • cycle matrix argument - 1 • cycle matrix argument :=
        sub_smul eigenvalue 1 (cycle matrix argument)
      _ = eigenvalue • cycle matrix argument - cycle matrix argument := by
        rw [one_smul]
      _ = _ := sub_eq_sub_iff_add_eq_add.mpr (by
        simpa only [add_comm] using commutation)
  have inverted := congrArg (fun value => (eigenvalue - 1)⁻¹ • value) scaled
  rw [smul_smul, inv_mul_cancel₀ difference_nonzero, one_smul, smul_sub] at inverted
  rw [binaryCohomologicalAction_smul]
  exact inverted

end TernaryPeriodPolynomials.SphericalDetection.Helpers
