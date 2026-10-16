module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.NilpotentDifference

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

local instance complexEndRationalAlgebra : Algebra ℚ (Module.End ℂ V) :=
  Algebra.restrictScalars ℚ ℂ (Module.End ℂ V)

/-- The finite exponential average does not depend on the choice of `ℚ`-algebra structure. -/
theorem nilpotentExponentialAverage_inst_irrel {A : Type*} [Ring A] (i₁ i₂ : Algebra ℚ A) (a : A)
    (cutoff : ℕ) :
    @nilpotentExponentialAverage A _ i₁ a cutoff = @nilpotentExponentialAverage A _ i₂ a cutoff := by
  cases Subsingleton.elim i₁ i₂
  rfl

/-- The exponential of a nilpotent element does not depend on the choice of `ℚ`-module structure. -/
theorem exp_inst_irrel {A : Type*} [Ring A] (i₁ i₂ : Module ℚ A) (a : A) :
    @IsNilpotent.exp A _ i₁ a = @IsNilpotent.exp A _ i₂ a := by
  cases Subsingleton.elim i₁ i₂
  rfl

def nilpotentAverageEquiv (operator : Module.End ℂ V) (nilpotent : IsNilpotent operator)
    (cutoff : ℕ) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (nilpotentExponentialAverage operator (cutoff + 1))
    ((Module.End.isUnit_iff _).mp (nilpotentExponentialAverage_isUnit operator nilpotent cutoff))

theorem nilpotentAverageEquiv_apply (operator : Module.End ℂ V) (nilpotent : IsNilpotent operator)
    (cutoff : ℕ) (vector : V) :
    nilpotentAverageEquiv operator nilpotent cutoff vector =
      nilpotentExponentialAverage operator (cutoff + 1) vector := rfl

theorem nilpotent_difference_apply (operator : Module.End ℂ V) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0) (vector : V) :
    (IsNilpotent.exp operator - 1) vector =
      nilpotentExponentialAverage operator (cutoff + 1) (operator vector) := by
  rw [nilpotent_exponential_sub_one operator cutoff nilpotent,
    (nilpotentExponentialAverage_commute operator (cutoff + 1)).eq]
  rfl

theorem nilpotent_difference_kernel (operator : Module.End ℂ V) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0) (vector : V) :
    (IsNilpotent.exp operator - 1) vector = 0 ↔ operator vector = 0 := by
  rw [nilpotent_difference_apply operator cutoff nilpotent]
  have bijective := (Module.End.isUnit_iff _).mp
    (nilpotentExponentialAverage_isUnit operator ⟨cutoff + 1, nilpotent⟩ cutoff)
  exact LinearMap.map_eq_zero_iff _ bijective.injective

theorem nilpotent_difference_range (operator : Module.End ℂ V) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0) :
    LinearMap.range (IsNilpotent.exp operator - 1) = LinearMap.range operator := by
  rw [nilpotent_exponential_sub_one operator cutoff nilpotent]
  have surjective := ((Module.End.isUnit_iff _).mp
    (nilpotentExponentialAverage_isUnit operator ⟨cutoff + 1, nilpotent⟩ cutoff)).surjective
  exact LinearMap.range_comp_of_range_eq_top operator (LinearMap.range_eq_top.mpr surjective)

theorem nilpotent_averages_commute (first second : Module.End ℂ V)
    (commute : Commute first second) (first_cutoff second_cutoff : ℕ) :
    Commute (nilpotentExponentialAverage first first_cutoff)
      (nilpotentExponentialAverage second second_cutoff) :=
  nilpotentExponentialAverage_commute_of_commute _ _
    (nilpotentExponentialAverage_commute_of_commute second first commute.symm first_cutoff).symm second_cutoff

theorem nilpotent_difference_pair_identity (first second : Module.End ℂ V)
    (commute : Commute first second) (first_cutoff second_cutoff : ℕ)
    (first_nilpotent : first ^ (first_cutoff + 1) = 0)
    (second_nilpotent : second ^ (second_cutoff + 1) = 0) :
    (IsNilpotent.exp first - 1) * nilpotentExponentialAverage second (second_cutoff + 1) =
      (nilpotentExponentialAverage first (first_cutoff + 1) *
        nilpotentExponentialAverage second (second_cutoff + 1)) * first ∧
    (IsNilpotent.exp second - 1) * nilpotentExponentialAverage first (first_cutoff + 1) =
      (nilpotentExponentialAverage first (first_cutoff + 1) *
        nilpotentExponentialAverage second (second_cutoff + 1)) * second := by
  have first_average := nilpotentExponentialAverage_commute first (first_cutoff + 1)
  have second_average := nilpotentExponentialAverage_commute second (second_cutoff + 1)
  have first_second_average := nilpotentExponentialAverage_commute_of_commute first second commute (second_cutoff + 1)
  have second_first_average := nilpotentExponentialAverage_commute_of_commute second first commute.symm (first_cutoff + 1)
  have averages := nilpotent_averages_commute first second commute (first_cutoff + 1) (second_cutoff + 1)
  constructor
  · rw [nilpotent_exponential_sub_one first first_cutoff first_nilpotent,
      first_average.eq, mul_assoc, first_second_average.eq, ← mul_assoc]
  · rw [nilpotent_exponential_sub_one second second_cutoff second_nilpotent,
      second_average.eq, mul_assoc, second_first_average.eq, ← mul_assoc, averages.eq]

/-- Averaging the two components carries exactly the closed infinitesimal pairs to closed differences. -/
theorem nilpotent_difference_pair_closed_iff (first second : Module.End ℂ V)
    (commute : Commute first second) (first_cutoff second_cutoff : ℕ)
    (first_nilpotent : first ^ (first_cutoff + 1) = 0)
    (second_nilpotent : second ^ (second_cutoff + 1) = 0) (alpha beta : V) :
    (IsNilpotent.exp first - 1) (nilpotentExponentialAverage second (second_cutoff + 1) beta) =
      (IsNilpotent.exp second - 1) (nilpotentExponentialAverage first (first_cutoff + 1) alpha) ↔
      first beta = second alpha := by
  obtain ⟨first_identity, second_identity⟩ := nilpotent_difference_pair_identity
    first second commute first_cutoff second_cutoff first_nilpotent second_nilpotent
  change ((IsNilpotent.exp first - 1) * nilpotentExponentialAverage second (second_cutoff + 1)) beta =
    ((IsNilpotent.exp second - 1) * nilpotentExponentialAverage first (first_cutoff + 1)) alpha ↔ _
  rw [first_identity, second_identity]
  have invertible := (nilpotentExponentialAverage_isUnit first ⟨first_cutoff + 1, first_nilpotent⟩ first_cutoff).mul
    (nilpotentExponentialAverage_isUnit second ⟨second_cutoff + 1, second_nilpotent⟩ second_cutoff)
  exact ((Module.End.isUnit_iff _).mp invertible).injective.eq_iff

theorem nilpotent_difference_pair_boundary_iff (first second : Module.End ℂ V)
    (first_cutoff second_cutoff : ℕ)
    (first_nilpotent : first ^ (first_cutoff + 1) = 0)
    (second_nilpotent : second ^ (second_cutoff + 1) = 0) (alpha beta : V) :
    (∃ potential : V,
      nilpotentExponentialAverage first (first_cutoff + 1) alpha = (IsNilpotent.exp first - 1) potential ∧
      nilpotentExponentialAverage second (second_cutoff + 1) beta = (IsNilpotent.exp second - 1) potential) ↔
    (∃ potential : V, alpha = first potential ∧ beta = second potential) := by
  have first_injective := ((Module.End.isUnit_iff _).mp
    (nilpotentExponentialAverage_isUnit first ⟨first_cutoff + 1, first_nilpotent⟩ first_cutoff)).injective
  have second_injective := ((Module.End.isUnit_iff _).mp
    (nilpotentExponentialAverage_isUnit second ⟨second_cutoff + 1, second_nilpotent⟩ second_cutoff)).injective
  simp only [nilpotent_difference_apply first first_cutoff first_nilpotent,
    nilpotent_difference_apply second second_cutoff second_nilpotent,
    first_injective.eq_iff, second_injective.eq_iff]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
