module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REIntegrable

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem threeStable_univ : ThreeStable Set.univ :=
  ⟨MeasurableSet.univ, fun _ _ _ _ => by simp⟩

/-- **The adelic Euler product of the finite entry integral.**  For a nonzero spherical vector which is an
eigenvector of the local sphere operators at every place, and a convergent exponent `3 < Re e`, the integral
of the entry integrand over `𝔸_f²` is the product of the local Euler factors at all places times the base value. -/
theorem entryIntegral_full (cusp : CuspidalRepresentation) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) (convergent : 3 < e.re)
    (eigenvalues : FinitePlace → ℂ)
    (eigen : ∀ place, cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalues place • vector)
    (value : ℂ) (product : HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor cusp place.val (eigenvalues place.val) e) value) :
    (∫ v, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure)) =
      value * cuspLocalPadicEulerFactor cusp placeThree (eigenvalues placeThree) e *
        entryBaseValue cusp vector m e := by
  have integrable := entryIntegrand_integrable cusp vector spherical m e convergent
  have two : 2 < e.re := by linarith
  have main := entryIntegral_eulerProduct threeStable_univ cusp vector nonzero spherical m e two eigenvalues
    (fun place _ => eigen place) integrable value product
  rw [Measure.restrict_univ] at main
  rw [main, entryBase_univ cusp vector nonzero spherical m e two (eigenvalues placeThree) (eigen placeThree)
    integrable, mul_assoc]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
