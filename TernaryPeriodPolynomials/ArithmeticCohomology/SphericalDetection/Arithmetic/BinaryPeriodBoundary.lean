module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TranslationInvariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodParityDetection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerEdge

@[expose] public section


open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem arithmeticBinaryRep_specialLinear_coe (degree : ℕ) (twist : ℤ)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (polynomial : Binary.HomogeneousPoly degree) :
    ((arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL matrix) polynomial).val =
      Binary.substitute ((matrix⁻¹).val.map (Int.castRingHom ℂ)) polynomial.val := by
  change (Binary.homogeneousAction degree twist
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL matrix)) polynomial).val = _
  rw [Binary.homogeneousAction_coe, Binary.action_apply]
  have determinant : Binary.determinantCharacter twist
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL matrix)) = 1 := by
    change ((GeneralLinearGroup.det
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL matrix)) : ℂˣ) : ℂ) ^ twist = 1
    change (matrix.val.map (Int.castRingHom ℂ)).det ^ twist = 1
    erw [← RingHom.map_det]
    change (Int.castRingHom ℂ) (matrix.val.det) ^ twist = 1
    rw [matrix.property, map_one, _root_.one_zpow]
  rw [determinant, one_smul, ← map_inv, ← map_inv]
  rfl

theorem arithmeticBinaryRep_T_coe (degree : ℕ) (twist : ℤ)
    (polynomial : Binary.HomogeneousPoly degree) :
    ((arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL ModularGroup.T) polynomial).val =
      Binary.substitute !![1, -1; 0, 1] polynomial.val := by
  rw [arithmeticBinaryRep_specialLinear_coe]
  have inverse : (ModularGroup.T⁻¹).val = !![1, -1; 0, 1] := by
    rw [SpecialLinearGroup.SL2_inv_expl]
    rfl
  rw [inverse]
  congr 2
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num

theorem arithmeticBinaryRep_T_fixed_iff (degree : ℕ) (twist : ℤ)
    (polynomial : Binary.HomogeneousPoly degree) :
    (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL ModularGroup.T) polynomial = polynomial ↔
      ∃ scalar : ℂ, polynomial = scalar • binaryStandardBasis degree 0 := by
  erw [Subtype.ext_iff, arithmeticBinaryRep_T_coe]
  exact binaryTranslation_fixed_iff_scalar (-1) (by norm_num) polynomial

theorem arithmeticBinaryRep_S_first (degree : ℕ) (twist : ℤ) :
    (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL ModularGroup.S)
      (binaryStandardBasis degree 0) = (-1 : ℂ) ^ degree • binaryStandardBasis degree (Fin.last degree) := by
  apply Subtype.ext
  rw [arithmeticBinaryRep_specialLinear_coe]
  have inverse : ((ModularGroup.S⁻¹).val.map (Int.castRingHom ℂ)) = !![0, 1; -1, 0] := by
    have inverse : (ModularGroup.S⁻¹).val = !![0, 1; -1, 0] := by
      rw [SpecialLinearGroup.SL2_inv_expl]
      rfl
    rw [inverse]
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num
  rw [inverse]
  simp only [binaryStandardBasis_coe, Submodule.coe_smul, Fin.val_zero, pow_zero, one_mul,
    Nat.sub_zero, Fin.val_last, Nat.sub_self, pow_zero, mul_one, map_pow,
    Binary.substitute_X, Binary.linearForm, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_zero,
    map_neg, map_one, zero_mul, add_zero, neg_one_mul, Algebra.smul_def, MvPolynomial.algebraMap_eq,
    map_pow]
  exact neg_pow (X 0) degree

theorem arithmeticBinaryBoundary_S_mem_endpointSpan (degree : ℕ) (twist : ℤ)
    (potential : Binary.HomogeneousPoly degree)
    (translation_zero : oneBoundaryCycle (arithmeticBinaryRep degree twist) potential
      (SpecialLinearGroup.toGL ModularGroup.T) = 0) :
    oneBoundaryCycle (arithmeticBinaryRep degree twist) potential
      (SpecialLinearGroup.toGL ModularGroup.S) ∈ binaryEndpointPolynomialSpan degree := by
  erw [oneBoundaryCycle_apply, sub_eq_zero] at translation_zero
  obtain ⟨scalar, rfl⟩ := (arithmeticBinaryRep_T_fixed_iff degree twist potential).mp translation_zero
  erw [oneBoundaryCycle_apply, map_smul, arithmeticBinaryRep_S_first]
  change scalar • ((-1 : ℂ) ^ degree • binaryStandardBasis degree (Fin.last degree)) -
    scalar • binaryStandardBasis degree 0 ∈ binaryEndpointPolynomialSpan degree
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_insert _ _)

theorem arithmeticBinaryCocycle_S_mem_of_H1_zero (degree : ℕ) (twist : ℤ)
    (cycle : groupCohomology.cocycles₁ (arithmeticBinaryRep degree twist))
    (translation_zero : cycle (SpecialLinearGroup.toGL ModularGroup.T) = 0)
    (class_zero : groupCohomology.H1π (arithmeticBinaryRep degree twist) cycle = 0) :
    cycle (SpecialLinearGroup.toGL ModularGroup.S) ∈ binaryEndpointPolynomialSpan degree := by
  obtain ⟨potential, boundary⟩ := (groupCohomology.H1π_eq_zero_iff cycle).mp class_zero
  have equal : oneBoundaryCycle (arithmeticBinaryRep degree twist) potential = cycle := by
    apply groupCohomology.cocycles₁_ext
    intro element
    exact congrFun boundary element
  rw [← equal] at translation_zero ⊢
  exact arithmeticBinaryBoundary_S_mem_endpointSpan degree twist potential translation_zero

theorem arithmeticBinaryCocycle_H1_ne_zero_of_periodParity {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations weight form eigenvalues)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2)
    (cycle : groupCohomology.cocycles₁ (arithmeticBinaryRep degree twist))
    (translation_zero : cycle (SpecialLinearGroup.toGL ModularGroup.T) = 0)
    (period_value : cycle (SpecialLinearGroup.toGL ModularGroup.S) =
      binaryParityComponent degree parity.val (cuspPeriodPolynomial form degree)) :
    groupCohomology.H1π (arithmeticBinaryRep degree twist) cycle ≠ 0 := by
  intro class_zero
  have member := arithmeticBinaryCocycle_S_mem_of_H1_zero degree twist cycle translation_zero class_zero
  rw [period_value] at member
  obtain ⟨first, second⟩ := levelOneCuspForm_periodParity_nonzero form nonzero eigenvalues relations
    degree weight_eq even
  fin_cases parity
  · exact first member
  · exact second member

end TernaryPeriodPolynomials.SphericalDetection.Helpers
