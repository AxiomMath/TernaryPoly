module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.HilbertFixedSpace
public import Mathlib
public import Batteries.Data.MLList.Basic
public import Batteries.Lean.LawfulMonadLift
public import Batteries.Lean.Meta.Simp
public import Batteries.Recycling.MonadSatisfying.Lean
public import Batteries.Util.Pickle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped CFC

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cusp_commuting_kernel_bot_or_top (cusp : CuspidalRepresentation)
    (operator : cusp.H →L[ℂ] cusp.H)
    (commuting : ∀ matrix, Commute operator (cuspUnitaryAction cusp matrix).toContinuousLinearMap) :
    LinearMap.ker operator.toLinearMap = ⊥ ∨ LinearMap.ker operator.toLinearMap = ⊤ := by
  apply cusp.irreducible _ operator.isClosed_ker
  intro matrix vector member
  change operator (cusp.π matrix vector) = 0
  have equality := congrArg (fun action : cusp.H →L[ℂ] cusp.H => action vector) (commuting matrix).eq
  change operator (cusp.π matrix vector) = cusp.π matrix (operator vector) at equality
  rw [equality, show operator vector = 0 from member, map_zero]

theorem cusp_commuting_mul_eq_zero (cusp : CuspidalRepresentation)
    (first second : cusp.H →L[ℂ] cusp.H)
    (commuting : ∀ matrix, Commute first (cuspUnitaryAction cusp matrix).toContinuousLinearMap)
    (product_zero : first * second = 0) : first = 0 ∨ second = 0 := by
  rcases cusp_commuting_kernel_bot_or_top cusp first commuting with trivial | full
  · right
    apply ContinuousLinearMap.ext
    intro vector
    have member : second vector ∈ LinearMap.ker first.toLinearMap := by
      exact congrArg (fun action : cusp.H →L[ℂ] cusp.H => action vector) product_zero
    simpa only [trivial, Submodule.mem_bot, zero_apply] using member
  · left
    apply ContinuousLinearMap.ext
    intro vector
    have member : vector ∈ LinearMap.ker first.toLinearMap := by rw [full]; trivial
    exact member

theorem cusp_commuting_selfAdjoint_sign (cusp : CuspidalRepresentation)
    (operator : cusp.H →L[ℂ] cusp.H) (selfAdjoint : IsSelfAdjoint operator)
    (commuting : ∀ matrix, Commute operator (cuspUnitaryAction cusp matrix).toContinuousLinearMap) :
    operator ≤ 0 ∨ 0 ≤ operator := by
  have positive_commuting : ∀ matrix,
      Commute operator⁺ (cuspUnitaryAction cusp matrix).toContinuousLinearMap := by
    intro matrix
    simpa only [CFC.posPart_def] using (commuting matrix).cfcₙ_real (fun scalar : ℝ => scalar⁺)
  rcases cusp_commuting_mul_eq_zero cusp operator⁺ operator⁻ positive_commuting
    (CFC.posPart_mul_negPart operator) with positive_zero | negative_zero
  · exact Or.inl ((CFC.posPart_eq_zero_iff operator selfAdjoint).mp positive_zero)
  · exact Or.inr ((CFC.negPart_eq_zero_iff operator selfAdjoint).mp negative_zero)

theorem cusp_positive_inner_zero (cusp : CuspidalRepresentation) (operator : cusp.H →L[ℂ] cusp.H)
    (positive : 0 ≤ operator) (vector : cusp.H) (zero : inner ℂ (operator vector) vector = 0) :
    operator vector = 0 := by
  have square := CFC.sqrt_mul_sqrt_self operator positive
  have symmetric := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (CFC.sqrt_nonneg operator)).isSymmetric
  have root_zero : CFC.sqrt operator vector = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    calc
      inner ℂ (CFC.sqrt operator vector) (CFC.sqrt operator vector) =
          inner ℂ (CFC.sqrt operator (CFC.sqrt operator vector)) vector := (symmetric _ _).symm
      _ = inner ℂ (operator vector) vector := by rw [← mul_apply_eq_comp, square]
      _ = 0 := zero
  rw [← square, mul_apply_eq_comp, root_zero, map_zero]

theorem cusp_commuting_selfAdjoint_zero_of_inner_zero (cusp : CuspidalRepresentation)
    (operator : cusp.H →L[ℂ] cusp.H) (selfAdjoint : IsSelfAdjoint operator)
    (commuting : ∀ matrix, Commute operator (cuspUnitaryAction cusp matrix).toContinuousLinearMap)
    {vector : cusp.H} (nonzero : vector ≠ 0) (zero : inner ℂ (operator vector) vector = 0) :
    operator = 0 := by
  have killed : operator vector = 0 := by
    rcases cusp_commuting_selfAdjoint_sign cusp operator selfAdjoint commuting with negative | positive
    · have killed := cusp_positive_inner_zero cusp (-operator) (neg_nonneg.mpr negative) vector
        (by simp only [neg_apply, inner_neg_left, zero, neg_zero])
      simpa only [neg_apply, neg_eq_zero] using killed
    · exact cusp_positive_inner_zero cusp operator positive vector zero
  rcases cusp_commuting_kernel_bot_or_top cusp operator commuting with trivial | full
  · have member : vector ∈ LinearMap.ker operator.toLinearMap := killed
    rw [trivial, Submodule.mem_bot] at member
    exact False.elim (nonzero member)
  · apply ContinuousLinearMap.ext
    intro other
    have member : other ∈ LinearMap.ker operator.toLinearMap := by rw [full]; trivial
    exact member

theorem cusp_commuting_selfAdjoint_scalar (cusp : CuspidalRepresentation)
    (operator : cusp.H →L[ℂ] cusp.H) (selfAdjoint : IsSelfAdjoint operator)
    (commuting : ∀ matrix, Commute operator (cuspUnitaryAction cusp matrix).toContinuousLinearMap) :
    ∃ scalar : ℝ, operator = (scalar : ℂ) • (1 : cusp.H →L[ℂ] cusp.H) := by
  let : Nontrivial cusp.H := cusp.nontrivial
  obtain ⟨vector, nonzero⟩ := exists_ne (0 : cusp.H)
  let scalar : ℝ := (inner ℂ (operator vector) vector).re / ‖vector‖ ^ 2
  let shifted := operator - (scalar : ℂ) • (1 : cusp.H →L[ℂ] cusp.H)
  have scalar_selfAdjoint : IsSelfAdjoint (scalar : ℂ) := by simp [IsSelfAdjoint]
  have identity_selfAdjoint : IsSelfAdjoint (1 : cusp.H →L[ℂ] cusp.H) := by simp [IsSelfAdjoint]
  have shifted_selfAdjoint : IsSelfAdjoint shifted :=
    selfAdjoint.sub (scalar_selfAdjoint.smul identity_selfAdjoint)
  have shifted_commuting : ∀ matrix,
      Commute shifted (cuspUnitaryAction cusp matrix).toContinuousLinearMap := by
    intro matrix
    exact (commuting matrix).sub_left ((Commute.one_left _).smul_left (scalar : ℂ))
  have quadratic_zero : inner ℂ (shifted vector) vector = 0 := by
    have denominator_ne : ‖vector‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr nonzero)
    have real_inner := selfAdjoint.isSymmetric.coe_re_inner_apply_self vector
    change ((inner ℂ (operator vector) vector).re : ℂ) = inner ℂ (operator vector) vector at real_inner
    change inner ℂ (operator vector - (scalar : ℂ) • vector) vector = 0
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal,
      ← real_inner, inner_self_eq_norm_sq_to_K]
    change ((inner ℂ (operator vector) vector).re : ℂ) -
      (scalar : ℂ) * (‖vector‖ : ℂ) ^ 2 = 0
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    apply congrArg Complex.ofReal
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ denominator_ne).symm
  have shifted_zero := cusp_commuting_selfAdjoint_zero_of_inner_zero cusp shifted shifted_selfAdjoint
    shifted_commuting nonzero quadratic_zero
  exact ⟨scalar, sub_eq_zero.mp shifted_zero⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
