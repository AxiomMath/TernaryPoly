module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaneCoordinateAssembly

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finiteCompletionPadicEquiv (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    place.adicCompletion ℚ ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] :=
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv place).toAlgEquiv.toRingEquiv

def finiteIntegralPadicEquiv (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (place.adicCompletionIntegers ℚ) ≃+* ℤ_[(Rat.HeightOneSpectrum.primesEquiv place).val] := by
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  letI : Algebra ℤ (place.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv place).toAlgEquiv.toRingEquiv

theorem finitePadicEquiv_compatible (place : FinitePlace) (integer : place.adicCompletionIntegers ℚ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (finiteIntegralPadicEquiv place integer : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) =
      finiteCompletionPadicEquiv place integer.val :=
  Rat.HeightOneSpectrum.adicCompletionIntegers.coe_padicIntEquiv_apply place integer

theorem finitePadicEquiv_inverse_compatible (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ integer : ℤ_[(Rat.HeightOneSpectrum.primesEquiv place).val],
      (finiteCompletionPadicEquiv place).symm (integer : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) =
        ((finiteIntegralPadicEquiv place).symm integer).val := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro integer
  apply (finiteCompletionPadicEquiv place).injective
  rw [RingEquiv.apply_symm_apply, ← finitePadicEquiv_compatible, RingEquiv.apply_symm_apply]

def finitePlacePadicCoordinates (place : FinitePlace) (first second : place.adicCompletion ℚ) :
    LocalPlanePivotCoordinates (place.adicCompletionIntegers ℚ).toSubring first second := by
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  exact localPlanePivotCoordinates_transport
    (source := PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv place).val)
    (target := (place.adicCompletionIntegers ℚ).toSubring) (finiteCompletionPadicEquiv place).symm
    (finiteIntegralPadicEquiv place).symm (finitePadicEquiv_inverse_compatible place) first second
    (padicPlanePivotCoordinates (finiteCompletionPadicEquiv place first) (finiteCompletionPadicEquiv place second))

theorem finitePlacePadicCoordinates_block (place : FinitePlace) (first second : place.adicCompletion ℚ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    GeneralLinearGroup.map (finiteCompletionPadicEquiv place).toRingHom (finitePlacePadicCoordinates place first second).block =
      (padicPlanePivotCoordinates (finiteCompletionPadicEquiv place first) (finiteCompletionPadicEquiv place second)).block := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  apply Units.ext
  funext row column
  exact (finiteCompletionPadicEquiv place).apply_symm_apply _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
