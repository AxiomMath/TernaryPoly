module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicHeckeAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- At degree zero there is one identity coset; the two primitive charts are used only at positive degree. -/
def cuspLocalPadicSphereOperator (cusp : CuspidalRepresentation) (place : FinitePlace) : ℕ → Module.End ℂ cusp.smooth
  | 0 => 1
  | power + 1 => cuspLocalPadicPrimitiveOperator cusp place (power + 1)

theorem cuspLocalPadicSphereOperator_zero (cusp : CuspidalRepresentation) (place : FinitePlace)
    (vector : cusp.smooth) : cuspLocalPadicSphereOperator cusp place 0 vector = vector := rfl

theorem cuspLocalPadicSphereOperator_succ (cusp : CuspidalRepresentation) (place : FinitePlace) (power : ℕ) :
    cuspLocalPadicSphereOperator cusp place (power + 1) = cuspLocalPadicPrimitiveOperator cusp place (power + 1) := rfl

theorem cuspLocalPadicSphereOperator_one (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    cuspLocalPadicSphereOperator cusp place 1 vector =
      cusp.centralCharacter (finiteAdeleUnit (finiteAtPadicUnit place (padicPrimePowerUnit 1))) •
        cuspPrimeHeckeSum cusp (Rat.HeightOneSpectrum.primesEquiv place) vector :=
  cuspLocalPadicPrimitiveOperator_one cusp vector spherical place

theorem cuspLocalPadicSphereOperator_one_realize (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (place : FinitePlace) (base : BinaryFiniteGL) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    padicPrimitiveSum 1 (cuspLocalPadicValue cusp vector base place) =
      cusp.centralCharacter (finiteAdeleUnit (finiteAtPadicUnit place (padicPrimePowerUnit 1))) *
        cusp.realize (cuspPrimeHeckeSum cusp (Rat.HeightOneSpectrum.primesEquiv place) vector) (atFinite base) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [← cuspLocalPadicPrimitiveOperator_realize, cuspLocalPadicPrimitiveOperator_one cusp vector spherical place, map_smul]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
