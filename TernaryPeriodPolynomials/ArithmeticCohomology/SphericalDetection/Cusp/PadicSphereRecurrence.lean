module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicSphereAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicSphereOperator_step_one (cusp : CuspidalRepresentation) (place : FinitePlace)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    cuspLocalPadicSphereOperator cusp place 1 (cuspLocalPadicSphereOperator cusp place 1 vector) =
      cuspLocalPadicSphereOperator cusp place 2 vector +
        ((Rat.HeightOneSpectrum.primesEquiv place).val + 1) • (cuspLocalPadicCentralChar cusp place • vector) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [cuspLocalPadicSphereOperator_step_sum,
    padicSphereSum_step_one (fun matrix => cuspLocalPadicAction cusp place matrix vector)
      (cuspLocalPadicAction_right cusp place vector spherical),
    ← cuspLocalPadicSphereOperator_eq_sum, cuspLocalPadicAction_central]

theorem cuspLocalPadicSphereOperator_step_succ (cusp : CuspidalRepresentation) (place : FinitePlace)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) (power : ℕ) :
    cuspLocalPadicSphereOperator cusp place (power + 2) (cuspLocalPadicSphereOperator cusp place 1 vector) =
      cuspLocalPadicSphereOperator cusp place (power + 3) vector +
        (Rat.HeightOneSpectrum.primesEquiv place).val •
          (cuspLocalPadicCentralChar cusp place • cuspLocalPadicSphereOperator cusp place (power + 1) vector) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [cuspLocalPadicSphereOperator_step_sum,
    padicSphereSum_step_succ (fun matrix => cuspLocalPadicAction cusp place matrix vector)
      (cuspLocalPadicAction_right cusp place vector spherical)]
  simp only [cuspLocalPadicAction_mul, cuspLocalPadicAction_central, padicSphereSum_smul,
    ← cuspLocalPadicSphereOperator_eq_sum]

theorem cuspLocalPadicSphereOperator_one_spherical (cusp : CuspidalRepresentation) (place : FinitePlace)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    (cuspLocalPadicSphereOperator cusp place 1 vector).val ∈ cuspSphericalValues cusp := by
  rw [cuspLocalPadicSphereOperator_one cusp vector spherical place]
  exact (cuspSphericalValues cusp).smul_mem _ (cuspPrimeHeckeSum_spherical cusp _ vector spherical)

theorem cuspLocalPadicSphereOperator_spherical (cusp : CuspidalRepresentation) (place : FinitePlace)
    (power : ℕ) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    (cuspLocalPadicSphereOperator cusp place power vector).val ∈ cuspSphericalValues cusp := by
  induction power using Nat.strong_induction_on generalizing vector with
  | h power induction =>
    rcases power with _ | power
    · exact spherical
    rcases power with _ | power
    · exact cuspLocalPadicSphereOperator_one_spherical cusp place vector spherical
    rcases power with _ | power
    · have recurrence := cuspLocalPadicSphereOperator_step_one cusp place vector spherical
      have solved := eq_sub_of_add_eq recurrence.symm
      rw [solved]
      exact (cuspSphericalValues cusp).sub_mem
        (cuspLocalPadicSphereOperator_one_spherical cusp place _
          (cuspLocalPadicSphereOperator_one_spherical cusp place vector spherical))
        ((cuspSphericalValues cusp).nsmul_mem
          ((cuspSphericalValues cusp).smul_mem _ spherical) _)
    · have recurrence := cuspLocalPadicSphereOperator_step_succ cusp place vector spherical power
      have solved := eq_sub_of_add_eq recurrence.symm
      rw [solved]
      exact (cuspSphericalValues cusp).sub_mem
        (induction (power + 2) (by omega) _
          (cuspLocalPadicSphereOperator_one_spherical cusp place vector spherical))
        ((cuspSphericalValues cusp).nsmul_mem
          ((cuspSphericalValues cusp).smul_mem _ (induction (power + 1) (by omega) vector spherical)) _)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
