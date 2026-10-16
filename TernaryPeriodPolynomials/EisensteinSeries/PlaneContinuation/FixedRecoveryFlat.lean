module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.FlatExtension
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ParameterShift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FixedRecoveryFlat

theorem tuple_eq_of_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {first second : AdelicGL → ℂ} (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) (equality : first = second) (frame : Rectangular ℝ) :
    ProfileTuples.tuple firstInduced frame = ProfileTuples.tuple secondInduced frame := by
  subst second
  rfl

theorem flat_tuple_parameter {degree : ℕ} {data : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data family) (source target : ℂ) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ProfileTuples.tuple (flat.1 target) frame =
      TupleParameterShift.factor data source target (RealFrameChart.point frame) •
        ProfileTuples.tuple (flat.1 source) frame :=
  (tuple_eq_of_eq (flat.1 target) (InducedParameterShift.induced (flat.1 source) target)
    (InducedFlatExtension.flat_eq_extension flat source target) frame).trans
      (TupleParameterShift.tuple_shift (flat.1 source) target frame fullRank)

def family {degree : ℕ} {data : InducingData degree} {original : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data original) (reference : ℂ) : ℂ → AdelicGL → ℂ :=
  fun parameter => InducedParameterShift.function reference parameter
    (FiniteSectionProjection.sectionFunction (flat.1 reference))

theorem isFlat {degree : ℕ} {data : InducingData degree} {original : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data original) (reference : ℂ) (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) :
    IsFlatSection data (family flat reference) :=
  InducedFlatExtension.flat (RecoveryGlobalCusp.section_induced (flat.1 reference) halfPlane)

theorem tuple {degree : ℕ} {data : InducingData degree} {original : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection data original) (reference : ℂ) (halfPlane : -(degree : ℝ) / 2 ≤ reference.re)
    (parameter : ℂ) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ProfileTuples.tuple ((isFlat flat reference halfPlane).1 parameter) frame =
      TupleRecoveryOperator.operator data reference halfPlane (ProfileTuples.tuple (flat.1 parameter) frame) := by
  change ProfileTuples.tuple
    (InducedParameterShift.induced (RecoveryGlobalCusp.section_induced (flat.1 reference) halfPlane) parameter) frame = _
  rw [TupleParameterShift.tuple_shift (RecoveryGlobalCusp.section_induced (flat.1 reference) halfPlane) parameter frame fullRank,
    TupleInducedRecovery.tuple (flat.1 reference) halfPlane frame fullRank,
    flat_tuple_parameter flat reference parameter frame fullRank, map_smul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FixedRecoveryFlat
