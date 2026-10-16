module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Radical.Exponential

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {Value : Type} [AddCommGroup Value] [Module ℂ Value]
variable [Module ℚ Value] [IsScalarTower ℚ ℂ Value]

def finiteExponentialRatio (bound : ℕ) (operator : Module.End ℂ Value) : Module.End ℂ Value :=
  ∑ order ∈ Finset.range (bound + 1), ((order + 1).factorial : ℚ)⁻¹ • operator ^ order

theorem finiteExponentialRatio_commute (bound : ℕ) (operator other : Module.End ℂ Value)
    (commuting : Commute operator other) :
    Commute (finiteExponentialRatio bound operator) other := by
  apply Commute.sum_left
  intro order _
  exact (commuting.pow_left order).smul_left _

theorem finiteExponentialRatio_sub_one_nilpotent (bound : ℕ)
    (operator : Module.End ℂ Value) (nilpotent : IsNilpotent operator) :
    IsNilpotent (finiteExponentialRatio bound operator - 1) := by
  have expansion : finiteExponentialRatio bound operator - 1 =
      ∑ order ∈ Finset.range bound,
        ((order + 2).factorial : ℚ)⁻¹ • operator ^ (order + 1) := by
    rw [finiteExponentialRatio, Finset.sum_range_succ']
    simp
  rw [expansion]
  apply Commute.isNilpotent_sum
  · intro order _
    exact (nilpotent.pow_succ order).smul _
  · intro first second _ _
    exact ((Commute.pow_pow_self operator (first + 1) (second + 1)).smul_left _).smul_right _

theorem finiteExponentialRatio_isUnit (bound : ℕ) (operator : Module.End ℂ Value)
    (nilpotent : IsNilpotent operator) : IsUnit (finiteExponentialRatio bound operator) := by
  have unit := (finiteExponentialRatio_sub_one_nilpotent bound operator nilpotent).isUnit_add_one
  simpa only [sub_add_cancel] using unit

def finiteExponentialRatioEquiv (bound : ℕ) (operator : Module.End ℂ Value)
    (nilpotent : IsNilpotent operator) : Value ≃ₗ[ℂ] Value :=
  LinearEquiv.ofBijective (finiteExponentialRatio bound operator)
    ((Module.End.isUnit_iff _).mp (finiteExponentialRatio_isUnit bound operator nilpotent))

theorem finiteExponentialRatioEquiv_apply (bound : ℕ) (operator : Module.End ℂ Value)
    (nilpotent : IsNilpotent operator) (value : Value) :
    finiteExponentialRatioEquiv bound operator nilpotent value =
      finiteExponentialRatio bound operator value := rfl

theorem finiteExponentialRatio_mul (bound : ℕ) (operator : Module.End ℂ Value)
    (vanishing : operator ^ (bound + 1) = 0) :
    finiteExponentialRatio bound operator * operator = IsNilpotent.exp operator - 1 := by
  rw [finiteExponentialRatio, Finset.sum_mul]
  have expansion : (∑ order ∈ Finset.range (bound + 1),
      (((order + 1).factorial : ℚ)⁻¹ • operator ^ order) * operator) =
      ∑ order ∈ Finset.range bound,
        ((order + 1).factorial : ℚ)⁻¹ • operator ^ (order + 1) := by
    simp only [smul_mul_assoc, ← pow_succ]
    rw [Finset.sum_range_succ, vanishing, smul_zero, add_zero]
  rw [expansion, IsNilpotent.exp_eq_sum vanishing, Finset.sum_range_succ']
  simp

theorem finiteExponentialRatio_inverse_operator (bound : ℕ) (operator : Module.End ℂ Value)
    (vanishing : operator ^ (bound + 1) = 0) (value : Value) :
    (finiteExponentialRatioEquiv bound operator ⟨bound + 1, vanishing⟩).symm
      ((IsNilpotent.exp operator - 1) value) = operator value := by
  rw [← finiteExponentialRatio_mul bound operator vanishing, Module.End.mul_apply]
  exact (finiteExponentialRatioEquiv bound operator ⟨bound + 1, vanishing⟩).symm_apply_apply
    (operator value)

theorem finiteExponentialRatio_inverse_commute (bound : ℕ)
    (operator other : Module.End ℂ Value) (nilpotent : IsNilpotent operator)
    (commuting : Commute operator other) (value : Value) :
    (finiteExponentialRatioEquiv bound operator nilpotent).symm (other value) =
      other ((finiteExponentialRatioEquiv bound operator nilpotent).symm value) := by
  apply (finiteExponentialRatioEquiv bound operator nilpotent).injective
  rw [LinearEquiv.apply_symm_apply]
  have equality := congrArg (fun map : Module.End ℂ Value =>
    map ((finiteExponentialRatioEquiv bound operator nilpotent).symm value))
      (finiteExponentialRatio_commute bound operator other commuting).eq
  simpa only [Module.End.mul_apply, LinearEquiv.ofBijective_apply,
    ← finiteExponentialRatioEquiv_apply bound operator nilpotent,
    LinearEquiv.apply_symm_apply] using equality.symm

theorem finiteExponentialRatio_pair_commute (bound : ℕ)
    (first second : Module.End ℂ Value) (commuting : Commute first second) :
    Commute (finiteExponentialRatio bound first) (finiteExponentialRatio bound second) := by
  apply Commute.sum_right
  intro order _
  exact ((finiteExponentialRatio_commute bound first second commuting).pow_right order).smul_right _

theorem finiteDifference_relation_normalized (bound : ℕ)
    (first second : Module.End ℂ Value) (commuting : Commute first second)
    (firstVanishing : first ^ (bound + 1) = 0)
    (secondVanishing : second ^ (bound + 1) = 0) (firstValue secondValue : Value) :
    (IsNilpotent.exp first - 1) secondValue =
        (IsNilpotent.exp second - 1) firstValue ↔
      first ((finiteExponentialRatioEquiv bound second ⟨bound + 1, secondVanishing⟩).symm
        secondValue) =
      second ((finiteExponentialRatioEquiv bound first ⟨bound + 1, firstVanishing⟩).symm
        firstValue) := by
  let firstEquiv := finiteExponentialRatioEquiv bound first ⟨bound + 1, firstVanishing⟩
  let secondEquiv := finiteExponentialRatioEquiv bound second ⟨bound + 1, secondVanishing⟩
  have inverseFirst (value : Value) : firstEquiv.symm (secondEquiv value) =
      secondEquiv (firstEquiv.symm value) :=
    finiteExponentialRatio_inverse_commute bound first (finiteExponentialRatio bound second)
      ⟨bound + 1, firstVanishing⟩
      (finiteExponentialRatio_commute bound second first commuting.symm).symm
      value
  have transformedFirst : secondEquiv.symm (firstEquiv.symm
      ((IsNilpotent.exp first - 1) secondValue)) = first (secondEquiv.symm secondValue) := by
    rw [finiteExponentialRatio_inverse_operator bound first firstVanishing secondValue]
    exact finiteExponentialRatio_inverse_commute bound second first
      ⟨bound + 1, secondVanishing⟩ commuting.symm secondValue
  have transformedSecond : secondEquiv.symm (firstEquiv.symm
      ((IsNilpotent.exp second - 1) firstValue)) = second (firstEquiv.symm firstValue) := by
    rw [← finiteExponentialRatio_mul bound second secondVanishing, Module.End.mul_apply]
    rw [show finiteExponentialRatio bound second (second firstValue) =
      secondEquiv (second firstValue) from rfl, inverseFirst,
      LinearEquiv.symm_apply_apply]
    exact finiteExponentialRatio_inverse_commute bound first second
      ⟨bound + 1, firstVanishing⟩ commuting firstValue
  constructor
  · intro relation
    have transformed := congrArg (fun value => secondEquiv.symm (firstEquiv.symm value)) relation
    rw [transformedFirst, transformedSecond] at transformed
    exact transformed
  · intro relation
    apply firstEquiv.symm.injective
    apply secondEquiv.symm.injective
    rw [transformedFirst, transformedSecond]
    exact relation

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
