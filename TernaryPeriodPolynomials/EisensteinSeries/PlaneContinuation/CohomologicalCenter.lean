module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AveragingSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Central

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalCenter

theorem binaryValues_smul (data : CuspidalRepresentation) (degree : ℕ)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) (scalar : ℂ) :
    BinaryValues data degree (scalar • function) := by
  intro monomial
  change (fun g => (scalar • function g).val.coeff monomial) ∈ cuspFunctions data
  have equality : (fun g => (scalar • function g).val.coeff monomial) =
      scalar • (fun g => (function g).val.coeff monomial) := by
    ext g
    simp only [Pi.smul_apply, Submodule.coe_smul, MvPolynomial.coeff_smul]
  rw [equality]
  exact (cuspFunctions data).smul_mem scalar (values monomial)

theorem action_smul (degree : ℕ) (matrix : BinaryRealGL) (scalar : ℂ)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) (point : BinaryAdelicGL) :
    binaryCohomologicalAction degree matrix (scalar • function) point =
      scalar • binaryCohomologicalAction degree matrix function point := by
  simp only [binaryCohomologicalAction, Pi.smul_apply, map_smul]
  exact smul_comm _ _ _

theorem central_action_scalar_eq_one {degree : ℕ} (data : InducingData degree)
    (centralMatrix : BinaryRealGL)
    (centrality : ∀ matrix : BinaryRealGL, centralMatrix * matrix = matrix * centralMatrix)
    (scalar : ℂ)
    (scalarAction : ∀ function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1),
      BinaryValues data.cusp degree function → ∀ point,
      binaryCohomologicalAction degree centralMatrix function point = scalar • function point) :
    scalar = 1 := by
  by_contra nontrivialScalar
  have differenceNonzero : scalar - 1 ≠ 0 := sub_ne_zero.mpr nontrivialScalar
  obtain ⟨cocycle, values, _, _, equation, nontrivialClass⟩ := data.cohomological
  apply nontrivialClass
  refine ⟨(scalar - 1)⁻¹ • cocycle centralMatrix,
    binaryValues_smul data.cusp degree _ (values centralMatrix) _, ?_⟩
  intro matrix point
  have first := equation centralMatrix matrix point
  have second := equation matrix centralMatrix point
  rw [centrality, scalarAction _ (values matrix)] at first
  have relation : (scalar - 1) • cocycle matrix point =
      binaryCohomologicalAction degree matrix (cocycle centralMatrix) point -
        cocycle centralMatrix point := by
    rw [second] at first
    rw [sub_smul scalar (1 : ℂ) (cocycle matrix point), one_smul]
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using first.symm)
  rw [action_smul, Pi.smul_apply]
  rw [← smul_sub ((scalar - 1)⁻¹)
    (binaryCohomologicalAction degree matrix (cocycle centralMatrix) point)
    (cocycle centralMatrix point), ← relation, inv_smul_smul₀ differenceNonzero]

theorem homogeneous_scale {degree : ℕ} (polynomial : Binary.HomogeneousPoly degree)
    (scalar : ℂ) :
    MvPolynomial.bind₁ (fun index : Fin 2 => MvPolynomial.C scalar * MvPolynomial.X index)
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
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
    degreeEquality]
  rw [MvPolynomial.monomial_eq, ← MvPolynomial.C_mul']
  change _ = _ * (_ * ∏ index ∈ monomial.support, MvPolynomial.X index ^ monomial index)
  ring

theorem substitute_diagonal {degree : ℕ} (polynomial : Binary.HomogeneousPoly degree)
    (scalar : ℂ) :
    Binary.substitute (Matrix.diagonal (fun _ : Fin 2 => scalar)) polynomial.val =
      scalar ^ degree • polynomial.val := by
  have formEquality : Binary.linearForm (Matrix.diagonal (fun _ : Fin 2 => scalar)) =
      fun index => MvPolynomial.C scalar * MvPolynomial.X index := by
    funext index
    fin_cases index <;> simp [Binary.linearForm, Matrix.diagonal_apply]
  simp only [Binary.substitute, formEquality]
  exact homogeneous_scale polynomial scalar

theorem atInfinity_scalar (scalar : ℝˣ) :
    atInfinity (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (realAdeleUnit scalar) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  by_cases equality : row = column <;>
    simp [atInfinity, combineGL, pairMatrix, realAdeleUnit,
      Matrix.GeneralLinearGroup.scalar, Matrix.scalar, equality]

theorem coefficient_scalar (degree : ℕ) (scalar : ℝˣ)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    binaryCoefficient degree (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar) polynomial =
      ((scalar.val : ℂ)⁻¹ ^ (degree + 3)) • polynomial := by
  change Binary.homogeneousAction (degree + 1) (-1)
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar)) polynomial = _
  rw [Matrix.GeneralLinearGroup.map_scalar]
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, Binary.action_apply]
  change (((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Units.map (algebraMap ℝ ℂ) scalar)) : ℂˣ) : ℂ) ^ (-1 : ℤ)) • _ = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  rw [← (Matrix.GeneralLinearGroup.scalar (Fin 2)).map_inv,
    Matrix.GeneralLinearGroup.coe_scalar]
  simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_map]
  change (((scalar.val : ℂ) ^ 2) ^ (-1 : ℤ)) •
    Binary.substitute (Matrix.diagonal (fun _ : Fin 2 => (scalar.val : ℂ)⁻¹)) polynomial.val = _
  rw [substitute_diagonal, smul_smul, zpow_neg_one]
  simp only [← inv_pow]
  congr 1
  rw [← pow_add]
  congr 1
  omega

theorem binaryValues_central (data : CuspidalRepresentation) (degree : ℕ)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) (scalar : Adelesˣ) (point : BinaryAdelicGL) :
    function (point * Matrix.GeneralLinearGroup.scalar (Fin 2) scalar) =
      data.centralCharacter scalar • function point := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  obtain ⟨vector, realization⟩ := values monomial
  rw [Submodule.coe_smul, MvPolynomial.coeff_smul]
  rw [← congrFun realization, ← congrFun realization]
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalHilbert.scalar_commute, data.central]
  rfl

theorem action_scalar (degree : ℕ) (data : CuspidalRepresentation) (scalar : ℝˣ)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) (point : BinaryAdelicGL) :
    binaryCohomologicalAction degree (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar)
        function point =
      (normPower (realAdeleUnit scalar) ((degree : ℂ) + 3) *
        ((scalar.val : ℂ)⁻¹ ^ (degree + 3)) *
        data.centralCharacter (realAdeleUnit scalar)) • function point := by
  rw [binaryCohomologicalAction, atInfinity_scalar, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Central.normPower_pow, coefficient_scalar,
    binaryValues_central data degree function values, smul_smul, smul_smul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℂ) * (((degree : ℂ) + 3) / 2) = (degree : ℂ) + 3 by ring]

theorem normPower_real_nat (scalar : ℝˣ) (degree : ℕ) :
    normPower (realAdeleUnit scalar) (degree : ℂ) = ((|scalar.val| : ℝ) : ℂ) ^ degree := by
  rw [normPower, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_real]
  rw [Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log (abs_pos.mpr scalar.ne_zero)]

theorem centralCharacter_positiveReal {degree : ℕ} (data : InducingData degree)
    (scalar : ℝˣ) (positivity : 0 < scalar.val) :
    data.cusp.centralCharacter (realAdeleUnit scalar) = 1 := by
  apply central_action_scalar_eq_one data (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar)
    (fun matrix => (Matrix.GeneralLinearGroup.scalar_commute scalar matrix))
  intro function values point
  rw [action_scalar degree data.cusp scalar function values point]
  have normFormula : normPower (realAdeleUnit scalar) ((degree : ℂ) + 3) =
      (scalar.val : ℂ) ^ (degree + 3) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat, abs_of_pos positivity] using
      normPower_real_nat scalar (degree + 3)
  rw [normFormula, ← mul_pow, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr scalar.ne_zero),
    one_pow, one_mul]

theorem centralCharacter_negativeReal {degree : ℕ} (data : InducingData degree)
    (scalar : ℝˣ) (negativity : scalar.val < 0) :
    data.cusp.centralCharacter (realAdeleUnit scalar) = (-1 : ℂ) ^ (degree + 1) := by
  have scalarRelation := central_action_scalar_eq_one data
    (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar)
    (fun matrix => Matrix.GeneralLinearGroup.scalar_commute scalar matrix)
    (normPower (realAdeleUnit scalar) ((degree : ℂ) + 3) *
      ((scalar.val : ℂ)⁻¹ ^ (degree + 3)) * data.cusp.centralCharacter (realAdeleUnit scalar))
    (fun function values point => action_scalar degree data.cusp scalar function values point)
  have normFormula : normPower (realAdeleUnit scalar) ((degree : ℂ) + 3) =
      (-(scalar.val : ℂ)) ^ (degree + 3) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat, abs_of_neg negativity, Complex.ofReal_neg] using
      normPower_real_nat scalar (degree + 3)
  rw [normFormula, ← mul_pow, neg_mul,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr scalar.ne_zero)] at scalarRelation
  have parity : (-1 : ℂ) ^ (degree + 3) = (-1 : ℂ) ^ (degree + 1) := by
    simp only [pow_add]
    norm_num
  rw [parity] at scalarRelation
  apply mul_left_cancel₀ (pow_ne_zero (degree + 1) (neg_ne_zero.mpr one_ne_zero))
  rw [scalarRelation, ← mul_pow]
  norm_num

noncomputable def cuspCharacter {degree : ℕ} (data : InducingData degree) : RankOneCharacter where
  toMonoidHom := data.cusp.centralCharacter
  continuous := TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalHilbert.centralCharacter_continuous data
  unitary := data.cusp.centralUnitary
  rational := TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalHilbert.centralCharacter_rational data
  positiveReal := centralCharacter_positiveReal data

theorem positiveReal_scalar_fixed {degree : ℕ} (data : InducingData degree)
    (scalar : ℝˣ) (positivity : 0 < scalar.val) (vector : data.cusp.H) :
    data.cusp.π (atInfinity (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar)) vector = vector := by
  rw [atInfinity_scalar, TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalHilbert.central,
    centralCharacter_positiveReal data scalar positivity, one_smul]

theorem negativeReal_scalar_action {degree : ℕ} (data : InducingData degree)
    (scalar : ℝˣ) (negativity : scalar.val < 0) (vector : data.cusp.H) :
    data.cusp.π (atInfinity (Matrix.GeneralLinearGroup.scalar (Fin 2) scalar)) vector =
      (-1 : ℂ) ^ (degree + 1) • vector := by
  rw [atInfinity_scalar, TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspidalHilbert.central,
    centralCharacter_negativeReal data scalar negativity]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalCenter
