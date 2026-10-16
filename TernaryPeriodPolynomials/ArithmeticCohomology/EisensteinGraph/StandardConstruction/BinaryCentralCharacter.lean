module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BinaryCentralCoefficient
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.CentralCocycle

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BinaryCentralCharacter

theorem values_smul {degree : ℕ} (data : CuspidalRepresentation)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) (scalar : ℂ) :
    BinaryValues data degree (fun argument => scalar • function argument) := by
  intro index
  simpa only [Submodule.coe_smul, coeff_smul, Pi.smul_def] using
    (cuspFunctions data).smul_mem scalar (values index)

theorem values_central {degree : ℕ} (data : CuspidalRepresentation)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) (unit : Adelesˣ) (argument : BinaryAdelicGL) :
    function (argument * GeneralLinearGroup.scalar (Fin 2) unit) =
      data.centralCharacter unit • function argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro index
  obtain ⟨vector, realization⟩ := values index
  have evaluation := congrFun realization
  rw [Submodule.coe_smul, coeff_smul, smul_eq_mul, ← evaluation, ← evaluation,
    ← GeneralLinearGroup.scalar_commute, data.central]

theorem atInfinity_scalar (unit : ℝˣ) :
    atInfinity (GeneralLinearGroup.scalar (Fin 2) unit) =
      GeneralLinearGroup.scalar (Fin 2) (realAdeleUnit unit) := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;> rfl

def actionLinear (degree : ℕ) (element : BinaryRealGL) :
    (BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) →ₗ[ℂ]
      (BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)) where
  toFun := binaryCohomologicalAction degree element
  map_add' first second := by
    funext argument
    simp only [binaryCohomologicalAction, Pi.add_apply, map_add, smul_add]
  map_smul' scalar function := by
    funext argument
    simp only [binaryCohomologicalAction, Pi.smul_apply, map_smul, RingHom.id_apply]
    exact smul_comm _ _ _

def centralScalar (degree : ℕ) (data : CuspidalRepresentation) (unit : ℝˣ) : ℂ :=
  normPower (GeneralLinearGroup.det (atInfinity (GeneralLinearGroup.scalar (Fin 2) unit)))
      (((degree : ℂ) + 3) / 2) *
    (((unit.val : ℂ) ^ 2) ^ (-1 : ℤ) * (unit.inv : ℂ) ^ (degree + 1)) *
      data.centralCharacter (realAdeleUnit unit)

theorem action_central {degree : ℕ} (data : CuspidalRepresentation)
    (function : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (values : BinaryValues data degree function) (unit : ℝˣ) :
    actionLinear degree (GeneralLinearGroup.scalar (Fin 2) unit) function =
      centralScalar degree data unit • function := by
  funext argument
  change binaryCohomologicalAction degree _ function argument = _
  rw [binaryCohomologicalAction, atInfinity_scalar, values_central data function values]
  unfold binaryCoefficient
  rw [GeneralLinearGroup.map_scalar, BinaryCentralCoefficient.homogeneousAction_scalar]
  simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.inv_eq_val_inv,
    Units.val_inv_eq_inv_val, smul_smul, Pi.smul_apply]
  simp only [centralScalar, atInfinity_scalar, Units.inv_eq_val_inv,
    Units.val_inv_eq_inv_val, Complex.ofReal_inv, mul_assoc]
  rfl

theorem centralScalar_eq_one {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) (unit : ℝˣ) :
    centralScalar degree data unit = 1 := by
  by_contra nontrivial
  obtain ⟨cocycle, values, _, _, closed, notCoboundary⟩ := cohomological
  apply notCoboundary
  refine ⟨(centralScalar degree data unit - 1)⁻¹ •
    cocycle (GeneralLinearGroup.scalar (Fin 2) unit), ?_, ?_⟩
  · exact values_smul data _ (values _) _
  · intro element argument
    exact congrFun (CentralCocycle.coboundary (actionLinear degree) cocycle
      (fun g h => funext (closed g h)) (GeneralLinearGroup.scalar (Fin 2) unit)
      (GeneralLinearGroup.scalar_commute unit) (centralScalar degree data unit)
      (fun g => action_central data (cocycle g) (values g) unit) nontrivial element) argument

theorem scalar_normPower (degree : ℕ) (unit : ℝˣ) :
    normPower (GeneralLinearGroup.det (atInfinity (GeneralLinearGroup.scalar (Fin 2) unit)))
      (((degree : ℂ) + 3) / 2) = ((|unit.val| : ℝ) : ℂ) ^ (degree + 3) := by
  rw [atInfinity_scalar, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  unfold normPower
  rw [map_pow, NNReal.coe_pow, Norms.realUnit_norm, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have exponent : ((degree : ℂ) + 3) / 2 * (((2 : ℝ) * Real.log |unit.val| : ℝ) : ℂ) =
      ((degree + 3 : ℕ) : ℂ) * (Real.log |unit.val| : ℂ) := by push_cast; ring
  rw [exponent, Complex.exp_nat_mul, ← Complex.ofReal_exp,
    Real.exp_log (abs_pos.mpr unit.ne_zero)]

theorem centralScalar_positive (degree : ℕ) (data : CuspidalRepresentation)
    (unit : ℝˣ) (positive : 0 < unit.val) :
    centralScalar degree data unit = data.centralCharacter (realAdeleUnit unit) := by
  rw [centralScalar, scalar_normPower, abs_of_pos positive]
  have nonzero : (unit.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr unit.ne_zero
  rw [zpow_neg_one, Units.inv_eq_val_inv, Units.val_inv_eq_inv_val, Complex.ofReal_inv]
  simp only [pow_succ]
  field_simp
  rw [← mul_pow]
  simp [nonzero]

theorem centralCharacter_positive {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) (unit : ℝˣ) (positive : 0 < unit.val) :
    data.centralCharacter (realAdeleUnit unit) = 1 := by
  rw [← centralScalar_positive degree data unit positive]
  exact centralScalar_eq_one data cohomological unit

theorem centralCharacter_neg_one {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) :
    data.centralCharacter (realAdeleUnit (-1 : ℝˣ)) = (-1 : ℂ) ^ (degree + 3) := by
  have equality := centralScalar_eq_one data cohomological (-1 : ℝˣ)
  norm_num [centralScalar, scalar_normPower, Units.inv_eq_val_inv] at equality
  have parity : (-1 : ℂ) ^ (degree + 3) = (-1 : ℂ) ^ (degree + 1) := by
    rw [show degree + 3 = (degree + 1) + 2 by omega, pow_add]
    norm_num
  rw [parity]
  calc
    _ = (-1 : ℂ) ^ (degree + 1) *
        ((-1 : ℂ) ^ (degree + 1) * data.centralCharacter (realAdeleUnit (-1 : ℝˣ))) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ = _ := by rw [equality, mul_one]

theorem centralCharacter_negative {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) (unit : ℝˣ) (negative : unit.val < 0) :
    data.centralCharacter (realAdeleUnit unit) = (-1 : ℂ) ^ (degree + 3) := by
  have factor : realAdeleUnit unit = realAdeleUnit (-1 : ℝˣ) * realAdeleUnit (-unit) := by
    change realUnitHom unit = realUnitHom (-1 : ℝˣ) * realUnitHom (-unit)
    rw [← map_mul]
    congr 1
    simp
  rw [factor, map_mul, centralCharacter_positive data cohomological (-unit)
    (by simpa using neg_pos.mpr negative), mul_one, centralCharacter_neg_one data cohomological]

theorem centralCharacter_real {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) (unit : ℝˣ) :
    data.centralCharacter (realAdeleUnit unit) =
      if 0 < unit.val then 1 else (-1 : ℂ) ^ (degree + 3) := by
  split_ifs with positive
  · exact centralCharacter_positive data cohomological unit positive
  · exact centralCharacter_negative data cohomological unit
      (lt_of_le_of_ne (le_of_not_gt positive) unit.ne_zero)

theorem exists_realization_nonzero {degree : ℕ} (data : CuspidalRepresentation)
    (cohomological : Cohomological data degree) :
    ∃ (vector : data.smooth) (argument : BinaryAdelicGL), data.realize vector argument ≠ 0 := by
  by_contra! vanishes
  obtain ⟨cocycle, values, _, _, _, notCoboundary⟩ := cohomological
  have zero : ∀ element argument, cocycle element argument = 0 := by
    intro element argument
    apply Subtype.ext
    apply MvPolynomial.ext
    intro index
    obtain ⟨vector, realization⟩ := values element index
    change (cocycle element argument).val.coeff index = 0
    rw [← congrFun realization argument, vanishes]
  apply notCoboundary
  refine ⟨0, ?_, ?_⟩
  · intro index
    simpa only [Pi.zero_apply, Pi.zero_def, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      (cuspFunctions data).zero_mem
  · intro element argument
    rw [zero]
    simp only [binaryCohomologicalAction, Pi.zero_apply, map_zero, smul_zero, sub_zero]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BinaryCentralCharacter
