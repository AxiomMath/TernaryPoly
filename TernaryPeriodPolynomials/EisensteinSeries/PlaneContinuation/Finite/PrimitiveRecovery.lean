module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RecoveryContinuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealBinaryRecovery TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoveryIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FinitePrimitiveRecovery

def integralGroup : Set BinaryFiniteGL := Set.range (GeneralLinearGroup.map integralEmbedding)

theorem integralGroup_isOpen : IsOpen integralGroup := BinaryLevel.integralMap_isOpenMap.isOpen_range

theorem integralGroup_isCompact : IsCompact integralGroup := by
  let _ : CompactSpace (Matrix (Fin 2) (Fin 2) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → IntegralAdeles))
  exact isCompact_range BinaryLevel.integralMap_continuous

def mass : ℝ := BinaryProductHaar.finiteMeasure.real integralGroup

theorem mass_pos : 0 < mass := by
  have positive : 0 < BinaryProductHaar.finiteMeasure integralGroup :=
    integralGroup_isOpen.measure_pos _ ⟨1, 1, map_one _⟩
  exact ENNReal.toReal_pos positive.ne' integralGroup_isCompact.measure_lt_top.ne

theorem mass_nonzero : (mass : ℂ) ≠ 0 := by exact_mod_cast mass_pos.ne'

theorem kernel_primitive {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : BinaryFiniteGL) (binaryIntegral : binary ∈ integralGroup) :
    kernel induced point (atFinite binary) =
      (outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ * function point := by
  have membership : atFinite binary ∈ integralRegion := binaryIntegral
  have equality := PrimitiveFrameRecovery.integrand_eq induced
    (LinearProfileRecovery.test induced (fun _ => 1)) (fun _ => 1)
    (LinearProfileRecovery.test_primitive induced (fun _ => 1)) point pointIntegral (atFinite binary) membership
  simpa only [integrand_eq_kernel induced, PrimitiveFrameRecovery.scalarCutoff, Complex.ofReal_one, one_mul] using equality

theorem kernel_supported {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (binary : BinaryAdelicGL)
    (outside : finite (FrameProfile.frame point * binary.val) ∉ Set.range CompactFiniteFrames.embedding) :
    kernel induced point binary = 0 := by
  simp only [kernel, UniversalFiniteProfiles.boxes_supported data _ _ outside, zero_mul, Finset.sum_const_zero]

theorem primitive_integral {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    (∫ binary in integralGroup, kernel induced point (atFinite binary) ∂BinaryProductHaar.finiteMeasure) =
      (mass : ℂ) * ((outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ * function point) := by
  rw [setIntegral_congr_fun integralGroup_isOpen.measurableSet
    (fun binary membership => kernel_primitive induced point pointIntegral binary membership)]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Complex.real_smul, mass]

def remainder {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) : ℂ :=
  outerCharacter data parameter (GeneralLinearGroup.det point) *
    ∫ binary in integralGroupᶜ, kernel induced point (atFinite binary) ∂BinaryProductHaar.finiteMeasure

theorem section_decomposition {degree : ℕ} {data : InducingData degree} {function : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data function) (parameter : ℂ) (point : AdelicGL)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point =
      (mass : ℂ) * function parameter point + remainder (flat.1 parameter) point := by
  rw [FiniteRecoveryIntegral.sectionFunction, ← integral_add_compl integralGroup_isOpen.measurableSet
    (kernel_integrable flat parameter point halfPlane), primitive_integral (flat.1 parameter) point pointIntegral, mul_add]
  unfold remainder
  congr 1
  have nonzero := FrameProfile.character_ne_zero (outerCharacter data parameter) (GeneralLinearGroup.det point)
  field_simp

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FinitePrimitiveRecovery
