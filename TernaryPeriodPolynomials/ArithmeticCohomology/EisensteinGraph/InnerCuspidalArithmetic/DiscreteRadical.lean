module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.FiniteDifference

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem radicalInfinitesimal_commute (degree : ℕ) (positive : 0 < degree)
    (first second : Fin 2) :
    Commute (radicalInfinitesimal degree positive first)
      (radicalInfinitesimal degree positive second) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  change X first.succ * pderiv 0 (X second.succ * pderiv 0 polynomial.val) =
    X second.succ * pderiv 0 (X first.succ * pderiv 0 polynomial.val)
  rw [pderiv_mul_binary_X, pderiv_mul_binary_X]
  ring

def radicalGenerator (index : Fin 2) : RationalGL3 :=
  lineUnipotent (if index = 0 then 1 else 0) (if index = 1 then 1 else 0)

def radicalDifference (degree : ℕ) (index : Fin 2) : Module.End ℂ (HomogeneousPoly degree) :=
  rationalCoefficientComponent degree trivialCharacter (radicalGenerator index) - 1

theorem radicalDifference_eq_exp (degree : ℕ) (positive : 0 < degree) (index : Fin 2) :
    radicalDifference degree index =
      IsNilpotent.exp (-(radicalInfinitesimal degree positive index)) - 1 := by
  apply congrArg (fun operator : Module.End ℂ (HomogeneousPoly degree) => operator - 1)
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [← radicalShear_action_exponential degree positive index polynomial]
  change (rationalCoefficientComponent degree trivialCharacter
    (lineUnipotent (if index = 0 then 1 else 0) (if index = 1 then 1 else 0)) polynomial).val = _
  rw [rationalCoefficientComponent_lineUnipotent]
  apply congrArg (fun forms : Fin 3 → Poly => bind₁ forms polynomial.val)
  funext coordinate
  fin_cases index <;> fin_cases coordinate <;> simp

def discreteRadicalDifferentialZero (degree : ℕ) :
    HomogeneousPoly degree →ₗ[ℂ] HomogeneousPoly degree × HomogeneousPoly degree :=
  (radicalDifference degree 0).prod (radicalDifference degree 1)

def discreteRadicalDifferentialOne (degree : ℕ) :
    (HomogeneousPoly degree × HomogeneousPoly degree) →ₗ[ℂ] HomogeneousPoly degree :=
  ((radicalDifference degree 0).comp (LinearMap.snd ℂ _ _)) -
    ((radicalDifference degree 1).comp (LinearMap.fst ℂ _ _))

def discreteRadicalCycles (degree : ℕ) :
    Submodule ℂ (HomogeneousPoly degree × HomogeneousPoly degree) :=
  (discreteRadicalDifferentialOne degree).ker

def radicalDifferenceNormalization (degree : ℕ) (positive : 0 < degree) (index : Fin 2) :
    HomogeneousPoly degree ≃ₗ[ℂ] HomogeneousPoly degree :=
  (finiteExponentialRatioEquiv degree (-(radicalInfinitesimal degree positive index))
    (radicalInfinitesimal_nilpotent degree positive index).neg).symm

def radicalPairNormalization (degree : ℕ) (positive : 0 < degree) :
    (HomogeneousPoly degree × HomogeneousPoly degree) ≃ₗ[ℂ]
      HomogeneousPoly degree × HomogeneousPoly degree :=
  (radicalDifferenceNormalization degree positive 0).prodCongr
    (radicalDifferenceNormalization degree positive 1)

theorem radicalNegativeInfinitesimal_pow_zero (degree : ℕ) (positive : 0 < degree)
    (index : Fin 2) : (-(radicalInfinitesimal degree positive index)) ^ (degree + 1) = 0 := by
  have identity := _root_.neg_pow (radicalInfinitesimal degree positive index) (degree + 1)
  simpa only [radicalInfinitesimal_pow_zero, mul_zero] using identity

theorem radicalPairNormalization_cycle_iff (degree : ℕ) (positive : 0 < degree)
    (pair : HomogeneousPoly degree × HomogeneousPoly degree) :
    pair ∈ discreteRadicalCycles degree ↔
      radicalPairNormalization degree positive pair ∈ radicalKoszulCycles degree positive := by
  change radicalDifference degree 0 pair.2 - radicalDifference degree 1 pair.1 = 0 ↔
    radicalInfinitesimal degree positive 0
        (radicalDifferenceNormalization degree positive 1 pair.2) -
      radicalInfinitesimal degree positive 1
        (radicalDifferenceNormalization degree positive 0 pair.1) = 0
  rw [sub_eq_zero, sub_eq_zero, radicalDifference_eq_exp degree positive 0,
    radicalDifference_eq_exp degree positive 1]
  have normalized := finiteDifference_relation_normalized degree
    (-(radicalInfinitesimal degree positive 0))
    (-(radicalInfinitesimal degree positive 1))
    (radicalInfinitesimal_commute degree positive 0 1).neg_left.neg_right
    (radicalNegativeInfinitesimal_pow_zero degree positive 0)
    (radicalNegativeInfinitesimal_pow_zero degree positive 1) pair.1 pair.2
  simpa only [LinearMap.neg_apply, neg_inj, radicalDifferenceNormalization] using normalized

theorem radicalPairNormalization_cycles (degree : ℕ) (positive : 0 < degree) :
    (discreteRadicalCycles degree).map (radicalPairNormalization degree positive).toLinearMap =
      radicalKoszulCycles degree positive := by
  apply le_antisymm
  · rintro pair ⟨original, cycle, rfl⟩
    exact (radicalPairNormalization_cycle_iff degree positive original).mp cycle
  · intro pair cycle
    refine ⟨(radicalPairNormalization degree positive).symm pair, ?_,
      (radicalPairNormalization degree positive).apply_symm_apply pair⟩
    apply (radicalPairNormalization_cycle_iff degree positive _).mpr
    rw [LinearEquiv.apply_symm_apply]
    exact cycle

def discreteRadicalCycleEquiv (degree : ℕ) (positive : 0 < degree) :
    discreteRadicalCycles degree ≃ₗ[ℂ] radicalKoszulCycles degree positive :=
  (radicalPairNormalization degree positive).ofSubmodules _ _
    (radicalPairNormalization_cycles degree positive)

theorem radicalDifferenceNormalization_difference (degree : ℕ) (positive : 0 < degree)
    (index : Fin 2) (polynomial : HomogeneousPoly degree) :
    radicalDifferenceNormalization degree positive index (radicalDifference degree index polynomial) =
      -(radicalInfinitesimal degree positive index polynomial) := by
  rw [radicalDifference_eq_exp degree positive index]
  exact finiteExponentialRatio_inverse_operator degree
    (-(radicalInfinitesimal degree positive index))
    (radicalNegativeInfinitesimal_pow_zero degree positive index) polynomial

theorem radicalPairNormalization_differentialZero (degree : ℕ) (positive : 0 < degree)
    (polynomial : HomogeneousPoly degree) :
    radicalPairNormalization degree positive (discreteRadicalDifferentialZero degree polynomial) =
      -(radicalKoszulDifferentialZero degree positive polynomial) := by
  apply Prod.ext
  · exact radicalDifferenceNormalization_difference degree positive 0 polynomial
  · exact radicalDifferenceNormalization_difference degree positive 1 polynomial

theorem discreteRadical_differential_squared (degree : ℕ) (positive : 0 < degree)
    (polynomial : HomogeneousPoly degree) :
    discreteRadicalDifferentialOne degree (discreteRadicalDifferentialZero degree polynomial) = 0 := by
  apply (radicalPairNormalization_cycle_iff degree positive _).mpr
  rw [radicalPairNormalization_differentialZero]
  exact (radicalKoszulCycles degree positive).neg_mem
    (radicalKoszulDifferentialOne_differentialZero degree positive polynomial)

def discreteRadicalBoundaryMap (degree : ℕ) (positive : 0 < degree) :
    HomogeneousPoly degree →ₗ[ℂ] discreteRadicalCycles degree :=
  (discreteRadicalDifferentialZero degree).codRestrict _
    (discreteRadical_differential_squared degree positive)

def discreteRadicalBoundaries (degree : ℕ) (positive : 0 < degree) :
    Submodule ℂ (discreteRadicalCycles degree) :=
  (discreteRadicalBoundaryMap degree positive).range

abbrev DiscreteRadicalH1 (degree : ℕ) (positive : 0 < degree) :=
  @HasQuotient.Quotient (discreteRadicalCycles degree)
    (Submodule ℂ (discreteRadicalCycles degree))
    (@Submodule.hasQuotient ℂ (discreteRadicalCycles degree)
      inferInstance inferInstance inferInstance)
    (discreteRadicalBoundaries degree positive)

theorem discreteRadicalCycleEquiv_boundary (degree : ℕ) (positive : 0 < degree)
    (polynomial : HomogeneousPoly degree) :
    discreteRadicalCycleEquiv degree positive (discreteRadicalBoundaryMap degree positive polynomial) =
      -(radicalKoszulBoundaryMap degree positive polynomial) := by
  apply Subtype.ext
  exact radicalPairNormalization_differentialZero degree positive polynomial

theorem discreteRadicalCycleEquiv_boundaries (degree : ℕ) (positive : 0 < degree) :
    (discreteRadicalBoundaries degree positive).map
      (discreteRadicalCycleEquiv degree positive).toLinearMap =
        radicalKoszulBoundaries degree positive := by
  apply le_antisymm
  · rintro cycle ⟨previous, ⟨polynomial, rfl⟩, rfl⟩
    change discreteRadicalCycleEquiv degree positive
      (discreteRadicalBoundaryMap degree positive polynomial) ∈ _
    rw [discreteRadicalCycleEquiv_boundary]
    exact (radicalKoszulBoundaries degree positive).neg_mem ⟨polynomial, rfl⟩
  · rintro cycle ⟨polynomial, rfl⟩
    refine ⟨discreteRadicalBoundaryMap degree positive (-polynomial), ⟨-polynomial, rfl⟩, ?_⟩
    change discreteRadicalCycleEquiv degree positive
      (discreteRadicalBoundaryMap degree positive (-polynomial)) = _
    rw [discreteRadicalCycleEquiv_boundary, map_neg, neg_neg]

def discreteRadicalBinaryEquiv (degree : ℕ) (positive : 0 < degree) :
    DiscreteRadicalH1 degree positive ≃ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (Submodule.Quotient.equiv _ _ (discreteRadicalCycleEquiv degree positive)
    (discreteRadicalCycleEquiv_boundaries degree positive)).trans
      (radicalKoszulBinaryEquiv degree positive)

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
