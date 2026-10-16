module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.Three

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The rational-cusp support condition implies literal parabolic-level support at three
for every adelic argument of the actual source. -/
theorem badPlaneSource_local_support {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (supported : BadPlaneSource source) (vertices : Fin 3 → RealGL3) (argument : AdelicGL)
    (outside : ¬ ∃ parabolic : planeParabolic ℚ_[3], ∃ compact : LocalThreeGL,
      InLocalThreeLevel compact ∧ adelicThreeGroup argument = parabolic.val * compact) :
    source vertices argument = 0 := by
  obtain ⟨rational, real, compact, factorization⟩ := adelicGL_rational_real_level argument
  have good : GoodFlag .plane (QuotientGroup.mk rational⁻¹) := by
    by_contra bad
    obtain ⟨parabolic, local_compact, local_level, local_eq⟩ :=
      rational_badPlane_local_support rational⁻¹ bad
    apply outside
    refine ⟨parabolic, local_compact * adelicThreeGroup (atFinite compact.val),
      InLocalThreeLevel_mul local_level (finiteLevel_atThree compact), ?_⟩
    rw [factorization, map_mul, map_mul, adelicThreeGroup_atInfinity, mul_one,
      adelicThreeGroup_rational]
    rw [inv_inv] at local_eq
    rw [local_eq, mul_assoc]
  have zero : source vertices (rationalGroup rational * atInfinity real) = 0 := by
    simpa only [inv_inv] using supported vertices rational⁻¹ good real
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [factorization]
  have invariant := (cocycle.1 vertices monomial).2.1 compact
    (rationalGroup rational * atInfinity real)
  dsimp only at invariant
  rw [invariant, zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
