module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.CentralRational
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BinaryCentralCharacter

@[expose] public section


/-!
# A spherical cohomological representation has odd degree

If `σ` has a nonzero smooth vector fixed by `GL₂(ℤ̂)`, the finite scalar `-1` acts trivially, so
the central character is trivial at the finite idele `-1`; it is trivial at the rational idele
`-1`, hence also at the real idele `-1`.  The cohomological condition in degree `n` forces the
value `(-1)^(n+3)` there (`BinaryCentralCharacter.centralCharacter_neg_one`), so `n` is odd.

* `centralCharacter_real_neg_one_of_spherical`
* `odd_of_sphericalCusp`

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Oldform

/-- A nonzero spherical vector forces the central character to be trivial at the real idele
`-1`. -/
theorem centralCharacter_real_neg_one_of_spherical (σ : CuspidalRepresentation) (v : σ.smooth)
    (nonzero : v ≠ 0) (spherical : v.val ∈ cuspSphericalValues σ) :
    σ.centralCharacter (realAdeleUnit (-1 : ℝˣ)) = 1 := by
  have rational := cuspCentralCharacter_rational σ v nonzero (-1 : ℚˣ)
  rw [rationalAdeleUnit_real_finite, map_mul] at rational
  have real_eq : Units.map (algebraMap ℚ ℝ : ℚ →* ℝ) (-1 : ℚˣ) = (-1 : ℝˣ) :=
    Units.ext (by simp)
  have unit_eq : Units.map integralEmbedding (-1 : IntegralAdelesˣ) =
      Units.map (algebraMap ℚ FiniteAdeles : ℚ →* FiniteAdeles) (-1 : ℚˣ) := Units.ext (by simp)
  have finite_one := cuspCentralCharacter_finite_integral σ v nonzero spherical
    (-1 : IntegralAdelesˣ)
  rw [unit_eq] at finite_one
  rw [real_eq, finite_one, mul_one] at rational
  exact rational

/-- **A spherical cohomological cuspidal representation has odd degree.** -/
theorem odd_of_sphericalCusp {σ : CuspidalRepresentation} {n : ℕ} (spherical : SphericalCusp σ)
    (cohomological : Cohomological σ n) : Odd n := by
  obtain ⟨v, nonzero, fixed⟩ := spherical
  have one := centralCharacter_real_neg_one_of_spherical σ v nonzero fixed
  rw [EisensteinGraph.StandardConstruction.BinaryCentralCharacter.centralCharacter_neg_one σ
    cohomological] at one
  have even : Even (n + 3) := (neg_one_pow_eq_one_iff_even (by norm_num)).mp one
  obtain ⟨k, hk⟩ := even
  exact ⟨k - 2, by omega⟩

end TernaryPeriodPolynomials.Oldform
