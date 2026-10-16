module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

noncomputable section

open GeneralEisenstein Adelic Matrix

namespace TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers

def realMinus : BinaryRealGL := GeneralLinearGroup.scalar (Fin 2) (-1)

def infinityMinus : Adelesˣ := realAdeleUnit (-1)

def finiteMinus : Adelesˣ := integralAdeleUnit (-1)

theorem infinity_minus_matrix :
    atInfinity realMinus = GeneralLinearGroup.scalar (Fin 2) infinityMinus := by
  apply GeneralLinearGroup.ext
  intro row column
  by_cases same : row = column <;>
  simp [atInfinity, combineGL, pairMatrix, realMinus, infinityMinus,
    GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal, realAdeleUnit, same]

theorem finite_minus_matrix :
    atFinite (GeneralLinearGroup.map integralEmbedding
      (GeneralLinearGroup.scalar (Fin 2) (-1))) =
      GeneralLinearGroup.scalar (Fin 2) finiteMinus := by
  apply GeneralLinearGroup.ext
  intro row column
  by_cases same : row = column <;>
  simp [atFinite, combineGL, pairMatrix, finiteMinus, integralAdeleUnit,
    GeneralLinearGroup.coe_scalar, Matrix.scalar,
    Matrix.diagonal, same]

theorem minus_units_product :
    infinityMinus * finiteMinus = Units.map rationalAdele (-1 : ℚˣ) := by
  apply Units.ext
  apply Prod.ext <;>
    simp [infinityMinus, finiteMinus, realAdeleUnit, integralAdeleUnit, rationalAdele]

theorem realize_nonzero (representation : CuspidalRepresentation)
    (vector : representation.smooth) (nonzero : vector ≠ 0) :
    ∃ point, representation.realize vector point ≠ 0 := by
  by_contra no_point
  apply nonzero
  apply representation.injective
  ext point
  simp only [map_zero]
  exact not_not.mp (not_exists.mp no_point point)

theorem spherical_infinity_character (representation : CuspidalRepresentation)
    (spherical : SphericalCusp representation) :
    representation.centralCharacter infinityMinus = 1 := by
  obtain ⟨vector, nonzero, fixed⟩ := spherical
  obtain ⟨point, value_nonzero⟩ := realize_nonzero representation vector nonzero
  have finite_character : representation.centralCharacter finiteMinus = 1 := by
    have translated := representation.equivariant
      (atFinite (GeneralLinearGroup.map integralEmbedding
        (GeneralLinearGroup.scalar (Fin 2) (-1)))) vector point
    have fixed_vector := fixed (GeneralLinearGroup.scalar (Fin 2) (-1))
    have vector_eq :
        (⟨representation.π (atFinite (GeneralLinearGroup.map integralEmbedding
          (GeneralLinearGroup.scalar (Fin 2) (-1)))) vector.val,
          representation.smooth_stable _ _ vector.property⟩ : representation.smooth) =
        vector := Subtype.ext fixed_vector
    rw [vector_eq, finite_minus_matrix,
      ← GeneralLinearGroup.scalar_commute, representation.central] at translated
    exact (mul_right_cancel₀ value_nonzero
      (translated.symm.trans (one_mul _).symm))
  have rational_character :
      representation.centralCharacter (Units.map rationalAdele (-1 : ℚˣ)) = 1 := by
    have translated := representation.leftRational
      (GeneralLinearGroup.scalar (Fin 2) (-1)) vector point
    rw [GeneralLinearGroup.map_scalar, representation.central] at translated
    exact mul_right_cancel₀ value_nonzero (translated.trans (one_mul _).symm)
  rw [← minus_units_product, map_mul, finite_character, mul_one] at rational_character
  exact rational_character

theorem binary_values_infinity_minus (representation : CuspidalRepresentation)
    (character : representation.centralCharacter infinityMinus = 1)
    (degree : ℕ) (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (belongs : BinaryValues representation degree values) (point : BinaryAdelicGL) :
    values (point * atInfinity realMinus) = values point := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  obtain ⟨vector, realized⟩ := belongs monomial
  change representation.realize vector = _ at realized
  rw [← congrFun realized (point * atInfinity realMinus), ← congrFun realized point,
    infinity_minus_matrix, ← GeneralLinearGroup.scalar_commute,
    representation.central, character, one_mul]

theorem substitute_minus_monomial (exponent : Fin 2 →₀ ℕ) (coefficient : ℂ) :
    Binary.substitute (Matrix.scalar (Fin 2) (-1 : ℂ))
      (MvPolynomial.monomial exponent coefficient) =
      (-1 : ℂ) ^ (∑ index ∈ exponent.support, exponent index) •
        MvPolynomial.monomial exponent coefficient := by
  have forms : Binary.linearForm (Matrix.scalar (Fin 2) (-1 : ℂ)) =
      fun index => MvPolynomial.C (-1) * MvPolynomial.X index := by
    funext index
    fin_cases index <;> simp [Binary.linearForm, Matrix.scalar, Matrix.diagonal]
  simp only [Binary.substitute, forms, MvPolynomial.bind₁_monomial, mul_pow,
    Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
    MvPolynomial.prod_X_pow_eq_monomial, MvPolynomial.smul_eq_C_mul]
  rw [mul_left_comm, MvPolynomial.C_mul_monomial, mul_one]

theorem substitute_minus_homogeneous (degree : ℕ)
    (polynomial : Binary.HomogeneousPoly degree) :
    Binary.substitute (Matrix.scalar (Fin 2) (-1 : ℂ)) polynomial.val =
      (-1 : ℂ) ^ degree • polynomial.val := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff polynomial.val, map_sum]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff polynomial.val, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro exponent supported
  rw [substitute_minus_monomial]
  have homogeneous := (MvPolynomial.mem_homogeneousSubmodule degree polynomial.val).mp
    polynomial.property
  rw [← homogeneous.degree_eq_sum_deg_support supported]

theorem binary_coefficient_minus (degree : ℕ)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    binaryCoefficient degree realMinus polynomial = (-1 : ℂ) ^ (degree + 1) • polynomial := by
  have complex_minus : GeneralLinearGroup.map (algebraMap ℝ ℂ) realMinus =
      GeneralLinearGroup.scalar (Fin 2) (-1 : ℂˣ) := by
    simp [realMinus, GeneralLinearGroup.map_scalar]
  have inverse_minus :
      (GeneralLinearGroup.scalar (Fin 2) (-1 : ℂˣ))⁻¹ =
        GeneralLinearGroup.scalar (Fin 2) (-1 : ℂˣ) := by
    simp [← map_inv]
  apply Subtype.ext
  change Binary.action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) realMinus)
    polynomial.val = _
  rw [complex_minus, Binary.action_apply]
  change ((GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (-1 : ℂˣ)) : ℂˣ) : ℂ)
      ^ (-1 : ℤ) •
      Binary.substitute ((GeneralLinearGroup.scalar (Fin 2) (-1 : ℂˣ))⁻¹ : Binary.GL2)
        polynomial.val = (-1 : ℂ) ^ (degree + 1) • polynomial.val
  simp only [GeneralLinearGroup.det_scalar,
    Fintype.card_fin, neg_one_pow_two, Units.val_one, one_zpow, one_smul,
    inverse_minus, GeneralLinearGroup.coe_scalar]
  exact substitute_minus_homogeneous (degree + 1) polynomial

theorem infinity_minus_determinant :
    GeneralLinearGroup.det (atInfinity realMinus) = 1 := by
  rw [infinity_minus_matrix, GeneralLinearGroup.det_scalar]
  apply Units.ext
  apply Prod.ext <;> simp [infinityMinus, realAdeleUnit]

theorem cohomological_minus_action (representation : CuspidalRepresentation)
    (character : representation.centralCharacter infinityMinus = 1)
    (degree : ℕ) (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (belongs : BinaryValues representation degree values) (point : BinaryAdelicGL) :
    binaryCohomologicalAction degree realMinus values point =
      (-1 : ℂ) ^ (degree + 1) • values point := by
  rw [binaryCohomologicalAction, binary_values_infinity_minus representation character
    degree values belongs point, binary_coefficient_minus, infinity_minus_determinant]
  simp [normPower]

theorem binary_values_smul (representation : CuspidalRepresentation) (degree : ℕ)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (belongs : BinaryValues representation degree values) (scalar : ℂ) :
    BinaryValues representation degree (fun point => scalar • values point) := by
  intro monomial
  have scaled := (cuspFunctions representation).smul_mem scalar (belongs monomial)
  simpa only [Pi.smul_def, Submodule.coe_smul, MvPolynomial.coeff_smul] using scaled

theorem cohomological_action_smul (degree : ℕ) (group_element : BinaryRealGL)
    (values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (scalar : ℂ) (point : BinaryAdelicGL) :
    binaryCohomologicalAction degree group_element (fun point => scalar • values point) point =
      scalar • binaryCohomologicalAction degree group_element values point := by
  simp only [binaryCohomologicalAction, map_smul]
  exact smul_comm _ _ _

theorem cohomological_spherical_odd (degree : ℕ) (representation : CuspidalRepresentation)
    (cohomological : Cohomological representation degree)
    (spherical : SphericalCusp representation) : Odd degree := by
  by_contra not_odd
  have even_degree : Even degree := Nat.not_odd_iff_even.mp not_odd
  have odd_successor : Odd (degree + 1) := even_degree.add_odd odd_one
  have character := spherical_infinity_character representation spherical
  obtain ⟨cocycle, belongs, _, _, cocycle_identity, not_boundary⟩ := cohomological
  apply not_boundary
  refine ⟨fun point => (-(2 : ℂ)⁻¹) • cocycle realMinus point,
    binary_values_smul representation degree (cocycle realMinus) (belongs realMinus) _, ?_⟩
  intro group_element point
  have commuting : realMinus * group_element = group_element * realMinus :=
    GeneralLinearGroup.scalar_commute (-1) group_element
  have first_identity := cocycle_identity realMinus group_element point
  have second_identity := cocycle_identity group_element realMinus point
  have sign_identity : (-1 : ℂ) ^ (degree + 1) = -1 := odd_successor.neg_one_pow
  have negative_identity : (-1 : ℂ) • cocycle group_element point =
      -cocycle group_element point := neg_one_smul ℂ (cocycle group_element point)
  rw [cohomological_minus_action representation character degree
    (cocycle group_element) (belongs group_element) point,
    sign_identity, negative_identity, commuting, second_identity] at first_identity
  have action_identity :
      binaryCohomologicalAction degree group_element (cocycle realMinus) point =
        cocycle realMinus point - (2 : ℂ) • cocycle group_element point := by
    calc
      binaryCohomologicalAction degree group_element (cocycle realMinus) point =
          (cocycle group_element point +
            binaryCohomologicalAction degree group_element (cocycle realMinus) point) -
            cocycle group_element point := by abel
      _ = (cocycle realMinus point + -cocycle group_element point) -
          cocycle group_element point := by rw [first_identity]
      _ = cocycle realMinus point - (2 : ℂ) • cocycle group_element point := by
        rw [two_smul ℂ]
        abel
  rw [cohomological_action_smul, action_identity, smul_sub, smul_smul]
  have scalar_identity : (-(2 : ℂ)⁻¹) * 2 = -1 := by norm_num
  rw [scalar_identity, negative_identity]
  abel

end TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers
