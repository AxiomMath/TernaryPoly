module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.RightEquivariance
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersFlat
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Hilbert

@[expose] public section


/-!
# The integrand identity behind the diagonal of `DiagonalDatum`

If two plane-induced functions satisfy `F y = G (y h)` for a real `h`, their plane cusp-lift vectors
satisfy `v_F(y) = v_G(y h)` (the lift is determined by its realization, and the realization of
`v_F(y)` at `B` is `|det B|^{-e} F(planeLevi(B,1) y)`). Hence the global and local Hilbert standard
integrands of `F` at `g` and of `G` at `g h` agree pointwise, so the local values agree:
`localValue F g = localValue G (g h)`. With `SectionMultipliersFlat.flat_twist_diagonal` this gives
`translate_eq` of `diagonalDatum_of_factorization`: the local factor of the flat family of
`Φ_{s - s₀} = ρ_h^{s - s₀} · R(h) f` at `g` equals that of the flat family of `f` at `g h`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.RightEquivariance

theorem vector_translate {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (first second : AdelicGL → ℂ) (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) (real : RealGL3)
    (agree : ∀ element, first element = second (element * atInfinity real))
    (argument : AdelicGL) :
    CuspLift.vector data .plane parameter first firstInduced argument =
      CuspLift.vector data .plane parameter second secondInduced (argument * atInfinity real) := by
  apply data.cusp.injective
  funext binary
  rw [CuspLift.realizes, CuspLift.realizes, agree, mul_assoc]

theorem localIntegrand_translate {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (first second : AdelicGL → ℂ) (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) (real : RealGL3)
    (agree : ∀ element, first element = second (element * atInfinity real))
    (argument : AdelicGL) :
    localIntegrand data parameter first firstInduced argument =
      localIntegrand data parameter second secondInduced (argument * atInfinity real) := by
  funext coordinates
  unfold localIntegrand
  rw [vector_translate data parameter first second firstInduced secondInduced real agree,
    mul_assoc (weyl⁻¹ * localRadical coordinates) argument (atInfinity real)]

theorem localValue_translate {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (first second : AdelicGL → ℂ) (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second) (real : RealGL3)
    (agree : ∀ element, first element = second (element * atInfinity real))
    (argument : AdelicGL) :
    localValue data parameter first firstInduced argument =
      localValue data parameter second secondInduced (argument * atInfinity real) := by
  unfold localValue
  rw [localIntegrand_translate data parameter first second firstInduced secondInduced real agree]

/-- The local Hilbert value of the flat family of a plane section at a parameter. -/
def localFlatValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (parameter : ℂ) (argument : AdelicGL) : data.cusp.H :=
  localValue data parameter
    ((SectionSpace.linearFlatExtension data holomorphic sectionValue).val parameter)
    ((SectionSpace.linearFlatExtension data holomorphic sectionValue).property.1 parameter)
    argument

/-- The local factor of the flat family of the twist `Φ_{s - s₀} = ρ_h^{s - s₀} · R(h) f` at `g`
is the local factor of the flat family of `f` at `g h`. -/
theorem localFlatValue_twist {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) {logXi : AdelicGL → ℝ}
    (law : HeightLaw logXi)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (parameter : ℂ) (argument : AdelicGL) :
    localFlatValue data holomorphic
        ⟨twist logXi real (parameter - cohomologicalPoint) sectionValue.val,
          isInduced_twist data cohomologicalPoint law real (parameter - cohomologicalPoint)
            sectionValue.val sectionValue.property⟩ parameter argument =
      localFlatValue data holomorphic sectionValue parameter (argument * atInfinity real) :=
  localValue_translate data parameter _ _ _ _ real
    (fun element => SectionMultipliersFlat.flat_twist_diagonal data holomorphic law sectionValue
      real parameter element) argument

end TernaryPeriodPolynomials.EdgeConvergence.RightEquivariance
