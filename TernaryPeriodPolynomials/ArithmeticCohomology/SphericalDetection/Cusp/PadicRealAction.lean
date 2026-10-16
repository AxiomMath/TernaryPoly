module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicEulerIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicAction_real_commute (cusp : CuspidalRepresentation) (place : FinitePlace)
    (real : BinaryRealGL) (vector : cusp.smooth) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ matrix, cuspLocalPadicAction cusp place matrix (cuspSmoothAction cusp (atInfinity real) vector) =
      cuspSmoothAction cusp (atInfinity real) (cuspLocalPadicAction cusp place matrix vector) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro matrix
  simp only [cuspLocalPadicAction, ← cuspSmoothAction_mul]
  rw [← (atInfinity_commute_atFinite real (finiteAtPadicGL 2 place matrix)).eq]

theorem cuspLocalPadicSphereOperator_real_commute (cusp : CuspidalRepresentation) (place : FinitePlace)
    (real : BinaryRealGL) (vector : cusp.smooth) (power : ℕ) :
    cuspLocalPadicSphereOperator cusp place power (cuspSmoothAction cusp (atInfinity real) vector) =
      cuspSmoothAction cusp (atInfinity real) (cuspLocalPadicSphereOperator cusp place power vector) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [cuspLocalPadicSphereOperator_eq_sum, cuspLocalPadicSphereOperator_eq_sum]
  simp only [cuspLocalPadicAction_real_commute]
  exact padicSphereSum_map (cuspSmoothAction cusp (atInfinity real)).toAddMonoidHom _ power

theorem cuspSmoothAction_real_spherical (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (real : BinaryRealGL) :
    (cuspSmoothAction cusp (atInfinity real) vector).val ∈ cuspSphericalValues cusp :=
  cuspSphericalValues_real_stable cusp real vector.val spherical

theorem cuspSmoothAction_real_exists_finite_value_ne_zero (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) :
    ∃ (real : BinaryRealGL) (base : BinaryFiniteGL),
      cusp.realize (cuspSmoothAction cusp (atInfinity real) vector) (atFinite base) ≠ 0 := by
  have realized_nonzero : cusp.realize vector ≠ 0 := by
    intro zero
    apply nonzero
    apply cusp.injective
    rw [zero, map_zero]
  obtain ⟨argument, value_nonzero⟩ := Function.ne_iff.mp realized_nonzero
  obtain ⟨real, base, decomposition⟩ := binaryAdelic_exists_real_finite argument
  refine ⟨real, base, ?_⟩
  rw [cuspSmoothAction_realize, ← (atInfinity_commute_atFinite real base).eq, ← decomposition]
  exact value_nonzero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
