module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.OrbitalMass

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryProductHaar
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealBinaryRecovery TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedSectionAlgebra
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryIntegral

def sectionFunction {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) : ℂ :=
  outerCharacter data parameter (GeneralLinearGroup.det point) *
    ∫ binary : BinaryFiniteGL, kernel induced point (atFinite binary) ∂BinaryProductHaar.finiteMeasure

theorem section_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular ℝ → ℝ) (point : AdelicGL) :
    VectorGodement.sectionFunction data (LinearProfileRecovery.test induced cutoff) parameter point =
      RealOrbitalMass.mass cutoff point * sectionFunction induced point := by
  rw [VectorGodement.sectionFunction, integral_product]
  simp_rw [integrand_separated induced cutoff point]
  rw [integral_prod_mul (fun binary : BinaryRealGL => (cutoff (realFrame point * binary.val) : ℂ))
    (fun binary : BinaryFiniteGL => kernel induced point (atFinite binary))]
  unfold RealOrbitalMass.mass sectionFunction
  ring

theorem kernel_integrable {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (parameter : ℂ) (point : AdelicGL)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    Integrable (fun binary : BinaryFiniteGL => kernel (flat.1 parameter) point (atFinite binary)) BinaryProductHaar.finiteMeasure := by
  obtain ⟨cutoff, smooth, compact, supported, _, _, nonzero⟩ := RealOrbitalMass.exists_cutoff point
  have productIntegral := (BinaryProductHaar.integrable_iff _).mp
    (LinearProfileRecovery.test_integrable flat cutoff smooth compact supported parameter point halfPlane)
  simp only [integrand_separated (flat.1 parameter) cutoff point] at productIntegral
  have integrated := productIntegral.integral_prod_right
  simp only [integral_mul_const] at integrated
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr nonzero) _).mp integrated

theorem exists_meromorphic {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (point : AdelicGL) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : ℂ, (1 - (degree : ℝ)) / 2 < parameter.re →
        continuation parameter = sectionFunction (flat.1 parameter) point := by
  obtain ⟨cutoff, smooth, compact, supported, _, _, nonzero⟩ := RealOrbitalMass.exists_cutoff point
  obtain ⟨continuation, _, meromorphic, _, recovery, _⟩ :=
    LinearProfileRecovery.exists_recovery flat cutoff smooth compact supported
  refine ⟨fun parameter => (RealOrbitalMass.mass cutoff point)⁻¹ * average (continuation parameter) point,
    fun parameter => analyticAt_const.meromorphicAt.mul (meromorphic point parameter), ?_⟩
  intro parameter halfPlane
  dsimp only
  exact (congrArg (fun scalar : ℂ => (RealOrbitalMass.mass cutoff point)⁻¹ * scalar)
    ((recovery point parameter halfPlane).trans (section_eq (flat.1 parameter) cutoff point))).trans
      (inv_mul_cancel_left₀ nonzero _)

theorem kernel_add {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {first second : AdelicGL → ℂ} (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) (point : AdelicGL) (binary : BinaryAdelicGL) :
    kernel (induced_add firstInduced secondInduced) point binary =
      kernel firstInduced point binary + kernel secondInduced point binary := by
  simp only [kernel, profile_add firstInduced secondInduced, map_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem kernel_smul {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (coefficient : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    kernel (induced_smul induced coefficient) point binary = coefficient * kernel induced point binary := by
  simp only [kernel, profile_smul induced coefficient, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro key _
  ring

theorem section_add {degree : ℕ} {data : InducingData degree} {first second : ℂ → AdelicGL → ℂ}
    (firstFlat : IsFlatSection data first) (secondFlat : IsFlatSection data second)
    (parameter : ℂ) (point : AdelicGL) (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    sectionFunction (induced_add (firstFlat.1 parameter) (secondFlat.1 parameter)) point =
      sectionFunction (firstFlat.1 parameter) point + sectionFunction (secondFlat.1 parameter) point := by
  simp only [sectionFunction, kernel_add (firstFlat.1 parameter) (secondFlat.1 parameter)]
  exact (congrArg (fun scalar : ℂ => outerCharacter data parameter (GeneralLinearGroup.det point) * scalar)
    (integral_add (kernel_integrable firstFlat parameter point halfPlane)
      (kernel_integrable secondFlat parameter point halfPlane))).trans (mul_add _ _ _)

theorem section_smul {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (coefficient : ℂ) (point : AdelicGL) :
    sectionFunction (induced_smul induced coefficient) point = coefficient * sectionFunction induced point := by
  simp only [sectionFunction, kernel_smul induced coefficient, integral_const_mul]
  ring

def sectionLinear {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) : flatSpace data →ₗ[ℂ] (AdelicGL → ℂ) where
  toFun := fun function point => sectionFunction (function.property.1 parameter) point
  map_add' := fun first second => funext (fun point =>
    section_add first.property second.property parameter point halfPlane)
  map_smul' := fun coefficient function => funext (fun point =>
    section_smul (function.property.1 parameter) coefficient point)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryIntegral
