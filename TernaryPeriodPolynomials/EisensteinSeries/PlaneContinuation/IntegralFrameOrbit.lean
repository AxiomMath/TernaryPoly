module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Flat.ProfileInterpolation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit

def realFrame (point : AdelicGL) : Rectangular ℝ := columns (realGroup point)⁻¹.val

theorem realFrame_fullRank (point : AdelicGL) : FullRank (realFrame point) := columns_fullRank _

theorem frame_eq (point : AdelicGL) :
    FrameProfile.frame point = adelicFrame (finiteGroup point) (realFrame point) := by
  rw [FrameProfile.frame, RectangularKernel.standard, mul_standard]
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · rfl
  · change _ = ((finiteGroup point)⁻¹.val * (RectangularKernel.standard : Rectangular FiniteAdeles)) row column
    rw [RectangularKernel.standard, mul_standard]
    rfl

theorem realFrame_eq (point : AdelicGL) :
    realFrame point = coordinateEquiv.symm (archimedean (FrameProfile.frame point)) := by
  rw [frame_eq]
  rfl

def finiteBinary : BinaryAdelicGL →* BinaryFiniteGL := GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)

def integralRegion : Set BinaryAdelicGL :=
  finiteBinary ⁻¹' Set.range (GeneralLinearGroup.map integralEmbedding (n := Fin 2))

theorem finiteBinary_continuous : Continuous finiteBinary := by
  apply Units.continuous_map
  exact continuous_pi (fun row => continuous_pi (fun column =>
    continuous_snd.comp ((continuous_apply column).comp (continuous_apply row))))

theorem integralRegion_isOpen : IsOpen integralRegion := by
  apply IsOpen.preimage finiteBinary_continuous
  exact integralMap_isOpenMap.isOpen_range

theorem integralRegion_measurable : MeasurableSet integralRegion := integralRegion_isOpen.measurableSet

theorem finiteGroup_levi (point : AdelicGL) (binary : BinaryAdelicGL) :
    finiteGroup (planeLevi binary⁻¹ 1 * point) = planeLevi (finiteBinary binary)⁻¹ 1 * finiteGroup point := by
  rw [map_mul, finiteGroup, map_planeLevi, map_inv, map_one]
  rfl

theorem orbit_integral (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : BinaryAdelicGL) (binaryIntegral : binary ∈ integralRegion) :
    ∃ finitePoint : IntegralFiniteGL,
      FrameProfile.frame point * binary.val =
        adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) (realFrame (planeLevi binary⁻¹ 1 * point)) := by
  obtain ⟨pointIntegral, pointEquality⟩ := pointIntegral
  obtain ⟨binaryIntegral, binaryEquality⟩ := binaryIntegral
  refine ⟨planeLevi binaryIntegral⁻¹ 1 * pointIntegral, ?_⟩
  rw [← FrameProfile.frame_levi, frame_eq, finiteGroup_levi, ← pointEquality, ← binaryEquality,
    map_mul, map_planeLevi, map_inv, map_one]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
