module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftReindex
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.AnalyticFamilyTaylor

@[expose] public section


/-!
# Linearity of the local standard integral in the section

Original work by Claude Sonnet 5.5.

The plane cusp lift vector, hence the local Hilbert standard integral, of a constant multiple of a
plane section is the multiple of the vector (`vector_const_mul`, `localValue_const_mul`). Consequently
the local vector of the twisted family with one more vertex (`HCLift.dropFirst`,
`HCLift.extendedWeight`) is the multiple `exp ((s - s₀) τ(v))` of the local vector of the original
twisted family (`localFamilyValue_extended`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

theorem vector_const_mul {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (scalar : ℂ) (induced : IsInduced data .plane parameter function)
    (scaledInduced : IsInduced data .plane parameter (fun y => scalar * function y))
    (y : AdelicGL) :
    (CuspLift.vector data .plane parameter (fun y => scalar * function y) scaledInduced y).val =
      scalar • (CuspLift.vector data .plane parameter function induced y).val := by
  have equality : CuspLift.vector data .plane parameter (fun y => scalar * function y)
      scaledInduced y = scalar • CuspLift.vector data .plane parameter function induced y := by
    apply data.cusp.injective
    funext binary
    rw [CuspLift.realizes, map_smul, Pi.smul_apply, smul_eq_mul, CuspLift.realizes]
    ring
  exact congrArg Subtype.val equality

theorem localValue_const_mul {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (scalar : ℂ) (induced : IsInduced data .plane parameter function)
    (scaledInduced : IsInduced data .plane parameter (fun y => scalar * function y))
    (argument : AdelicGL) :
    localValue data parameter (fun y => scalar * function y) scaledInduced argument =
      scalar • localValue data parameter function induced argument := by
  unfold localValue
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun coordinates => ?_))
  exact vector_const_mul data parameter function scalar induced scaledInduced _

theorem localValue_congr {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    {function other : AdelicGL → ℂ} (equality : function = other)
    (induced : IsInduced data .plane parameter function)
    (otherInduced : IsInduced data .plane parameter other) (argument : AdelicGL) :
    localValue data parameter function induced argument =
      localValue data parameter other otherInduced argument := by
  subst equality
  rfl

section Extended

variable {degree arity : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)
  (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
  (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))
  (weight : (Fin arity → RealGL3) → ℝ)

include induced in
/-- The induced property of the family with one more vertex. -/
theorem dropFirst_induced (vertices : Fin (arity + 1) → RealGL3) :
    IsInduced data .plane cohomologicalPoint (dropFirst family vertices) :=
  induced (fun i => vertices i.succ)

theorem twistedAt_extended (parameter : ℂ) (vertices : Fin (arity + 1) → RealGL3)
    (y : AdelicGL) :
    twistedAt data holomorphic (dropFirst family) (dropFirst_induced data family induced)
        (extendedWeight weight) parameter vertices y =
      Complex.exp ((parameter - cohomologicalPoint) * (determinantTwist (vertices 0) : ℂ)) *
        twistedAt data holomorphic family induced weight parameter (fun i => vertices i.succ)
          y := by
  have flat : flatAt data holomorphic (dropFirst family) (dropFirst_induced data family induced)
      parameter vertices y =
      flatAt data holomorphic family induced parameter (fun i => vertices i.succ) y := rfl
  unfold twistedAt
  rw [flat]
  simp only [extendedWeight, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem localFamilyValue_extended (parameter : ℂ) (vertices : Fin (arity + 1) → RealGL3)
    (argument : AdelicGL) :
    localFamilyValue data parameter
        (twistedAt data holomorphic (dropFirst family) (dropFirst_induced data family induced)
          (extendedWeight weight) parameter)
        (twistedAt_induced data holomorphic (dropFirst family)
          (dropFirst_induced data family induced) (extendedWeight weight) parameter)
        vertices argument =
      Complex.exp ((parameter - cohomologicalPoint) * (determinantTwist (vertices 0) : ℂ)) •
        localFamilyValue data parameter
          (twistedAt data holomorphic family induced weight parameter)
          (twistedAt_induced data holomorphic family induced weight parameter)
          (fun i => vertices i.succ) argument := by
  have functionEquality : twistedAt data holomorphic (dropFirst family)
      (dropFirst_induced data family induced) (extendedWeight weight) parameter vertices =
      fun y => Complex.exp ((parameter - cohomologicalPoint) *
        (determinantTwist (vertices 0) : ℂ)) *
        twistedAt data holomorphic family induced weight parameter (fun i => vertices i.succ) y :=
    funext (twistedAt_extended data holomorphic family induced weight parameter vertices)
  unfold localFamilyValue
  rw [localValue_congr data parameter functionEquality
    (twistedAt_induced data holomorphic (dropFirst family)
      (dropFirst_induced data family induced) (extendedWeight weight) parameter vertices)
    (LinearFamilies.induced_smul data .plane parameter
      (Complex.exp ((parameter - cohomologicalPoint) * (determinantTwist (vertices 0) : ℂ)))
      (twistedAt data holomorphic family induced weight parameter (fun i => vertices i.succ))
      (twistedAt_induced data holomorphic family induced weight parameter
        (fun i => vertices i.succ))) argument]
  exact localValue_const_mul data parameter _ _
    (twistedAt_induced data holomorphic family induced weight parameter
      (fun i => vertices i.succ)) _ argument

end Extended

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
