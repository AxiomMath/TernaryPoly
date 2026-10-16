module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.CentralDecomposition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicCentralChar_eq_one (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (place : FinitePlace) : cuspLocalPadicCentralChar cusp place = 1 := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have rational := cuspCentralCharacter_finite_rational_positive cusp vector nonzero central_positive
    (GeneralLinearGroup.det (binaryHeckeRepresentative (Rat.HeightOneSpectrum.primesEquiv place) none))
    (binaryHeckeRepresentative_det_positive _ _)
  rw [binaryHeckeCentral_decomposition, finiteAdeleUnit_mul, map_mul,
    cuspCentralCharacter_finite_integral cusp vector nonzero spherical, one_mul] at rational
  exact rational

theorem cohomological_cuspLocalPadicCentralChar_eq_one (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) (place : FinitePlace) :
    cuspLocalPadicCentralChar cusp place = 1 := by
  obtain ⟨vector, nonzero, fixed⟩ := spherical
  exact cuspLocalPadicCentralChar_eq_one cusp vector nonzero fixed
    (cohomological_centralCharacter_positive cusp cohomological) place

end TernaryPeriodPolynomials.SphericalDetection.Helpers
