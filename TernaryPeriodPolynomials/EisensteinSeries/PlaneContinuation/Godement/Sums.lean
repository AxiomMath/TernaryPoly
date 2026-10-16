module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.Godement

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorGodement

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementSums

theorem integrand_sum {Index : Type*} {degree : ℕ} (data : InducingData degree) (indices : Finset Index)
    (tests : Index → Rectangular Adeles → data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    integrand data (fun value => ∑ index ∈ indices, tests index value) parameter point binary =
      ∑ index ∈ indices, integrand data (tests index) parameter point binary := by
  simp only [integrand, map_sum, Finset.sum_apply, Finset.mul_sum]

theorem section_sum {Index : Type*} {degree : ℕ} (data : InducingData degree) (indices : Finset Index)
    (tests : Index → Rectangular Adeles → data.cusp.smooth) (parameter : ℂ) (point : AdelicGL)
    (integrable : ∀ index ∈ indices, Integrable (integrand data (tests index) parameter point) BinaryHaar.measure) :
    sectionFunction data (fun value => ∑ index ∈ indices, tests index value) parameter point =
      ∑ index ∈ indices, sectionFunction data (tests index) parameter point := by
  simp only [sectionFunction, integrand_sum]
  rw [integral_finsetSum indices integrable, Finset.mul_sum]

theorem integrand_smul {degree : ℕ} (data : InducingData degree) (coefficient : ℂ)
    (test : Rectangular Adeles → data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    integrand data (fun value => coefficient • test value) parameter point binary =
      coefficient * integrand data test parameter point binary := by
  simp only [integrand, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem section_smul {degree : ℕ} (data : InducingData degree) (coefficient : ℂ)
    (test : Rectangular Adeles → data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) :
    sectionFunction data (fun value => coefficient • test value) parameter point =
      coefficient * sectionFunction data test parameter point := by
  simp only [sectionFunction, integrand_smul, integral_const_mul]
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementSums
