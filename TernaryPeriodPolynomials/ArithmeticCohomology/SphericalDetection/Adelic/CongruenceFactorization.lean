module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.CongruenceFactorization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem adelicGL_ext (first second : AdelicGL)
    (real : realGroup first = realGroup second)
    (finite : finiteGroup first = finiteGroup second) : first = second := by
  apply Units.ext
  funext row column
  apply Prod.ext
  · exact congrArg (fun matrix => matrix.val row column) real
  · exact congrArg (fun matrix => matrix.val row column) finite

theorem realGroup_atInfinity (matrix : RealGL3) : realGroup (atInfinity matrix) = matrix := by
  apply Units.ext
  rfl

theorem finiteGroup_atInfinity (matrix : RealGL3) : finiteGroup (atInfinity matrix) = 1 := by
  apply Units.ext
  rfl

theorem realGroup_atFinite (matrix : FiniteGL) : realGroup (atFinite matrix) = 1 := by
  apply Units.ext
  rfl

theorem finiteGroup_atFinite (matrix : FiniteGL) : finiteGroup (atFinite matrix) = matrix := by
  apply Units.ext
  rfl

/-- The given adelic quotient has a single finite component even at its specified level. -/
theorem adelicGL_rational_real_level (matrix : AdelicGL) :
    ∃ (rational : RationalGL3) (real : RealGL3) (compact : finiteLevel),
      matrix = rationalGroup rational * atInfinity real * atFinite compact.val := by
  obtain ⟨rational, compact, finite_split⟩ := finiteGL_rational_level_factorization (finiteGroup matrix)
  refine ⟨rational, (realGroup (rationalGroup rational))⁻¹ * realGroup matrix, compact, ?_⟩
  apply adelicGL_ext
  · rw [map_mul, map_mul, realGroup_atInfinity, realGroup_atFinite, mul_one, mul_inv_cancel_left]
  · rw [map_mul, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, mul_one,
      finiteGroup_rational, finite_split]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
