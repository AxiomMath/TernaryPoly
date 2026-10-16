module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorExactness

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_linearRangeInverse (linear : V →ₗ[ℂ] W) :
    ∃ inverse : W →ₗ[ℂ] V, ∀ vector, linear (inverse (linear vector)) = linear vector := by
  have onto : Function.Surjective linear.rangeRestrict := by
    rintro ⟨value, vector, equality⟩
    exact ⟨vector, Subtype.ext equality⟩
  obtain ⟨sectionMap, section_law⟩ := linear.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr onto)
  obtain ⟨retraction, retracts⟩ := linear.range.subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨sectionMap.comp retraction, ?_⟩
  intro vector
  have retracts_value := LinearMap.congr_fun retracts (linear.rangeRestrict vector)
  have section_value := congrArg Subtype.val (LinearMap.congr_fun section_law (linear.rangeRestrict vector))
  change linear (sectionMap (retraction (linear vector))) = linear vector
  rw [show retraction (linear vector) = linear.rangeRestrict vector from retracts_value]
  exact section_value

def linearRangeInverse (linear : V →ₗ[ℂ] W) : W →ₗ[ℂ] V :=
  (exists_linearRangeInverse linear).choose

theorem linearRangeInverse_apply (linear : V →ₗ[ℂ] W) (vector : V) :
    linear (linearRangeInverse linear (linear vector)) = linear vector :=
  (exists_linearRangeInverse linear).choose_spec vector

end TernaryPeriodPolynomials.SphericalDetection.Helpers
