module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalRealization
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Inputs
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersFlat

@[expose] public section


/-!
# The scalar integrand of the local standard integral of a twisted section

Original work by Claude Sonnet 5.5.

For a plane section `f`, a real element `h` and `z ∈ ℂ`, the twisted section is
`Φ_z = ρ_h^z · R(h) f` (`SectionMultipliers.twist`). Its flat family is `Ξ^{s - s₀} Φ_z`
(`SectionMultipliersFlat.linearFlatExtension_eq_xi`), so the realization at `B` of the plane cusp lift
at `w⁻¹ n(u) κ` is the explicit function
`twistIntegrand s z u = |det B|^{-e(s)} · Ξ(P)^{s - s₀} · ρ_h(P)^z · f(P h)`, `P = planeLevi(B,1) w⁻¹ n(u) κ`.

* `localScalarIntegrand_twist` identifies the scalar integrand of the flat family of `Φ_z` with
  `twistIntegrand`;
* `twistIntegrand_eq_mul` : `twistIntegrand s z u = ρ_h(P)^z · twistIntegrand s 0 u`;
* `twistIntegrand_continuous` : `twistIntegrand · · u` is jointly continuous in `(s, z)`;
* `localScalar_twist_eq_integral` : the realization of the local Hilbert standard integral of `Φ_z` at
  `κ` is the integral of `twistIntegrand` over the local radical (`localValue_realizes`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCTwist

/-- The twisted plane section `Φ_z = ρ_h^z · R(h) f`. -/
def twistSection {degree : ℕ} (data : InducingData degree) {logXi : AdelicGL → ℝ}
    (law : SectionMultipliers.HeightLaw logXi) (real : RealGL3) (z : ℂ)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    SectionSpace.inducedSections data .plane cohomologicalPoint :=
  ⟨SectionMultipliers.twist logXi real z sectionValue.val,
    SectionMultipliers.isInduced_twist data cohomologicalPoint law real z sectionValue.val
      sectionValue.property⟩

/-- The point `planeLevi(B, 1) · w⁻¹ n(u) κ` at which a plane section is evaluated by the realization
at `B` of its plane cusp lift at the point `w⁻¹ n(u) κ` of the local standard integrand. -/
def evaluationPoint (binary : BinaryAdelicGL) (compact : AdelicGL)
    (coordinates : LocalLine × LocalLine) : AdelicGL :=
  binaryLevi .plane binary * (weyl⁻¹ * localRadical coordinates * compact)

/-- The explicit scalar integrand of the local standard integral of the flat family of the twisted
section `Φ_z`, at the parameter `s`. -/
def twistIntegrand (degree : ℕ) (logXi : AdelicGL → ℝ) (sectionFunction : AdelicGL → ℂ)
    (real : RealGL3) (binary : BinaryAdelicGL) (compact : AdelicGL) (parameter exponent : ℂ)
    (coordinates : LocalLine × LocalLine) : ℂ :=
  normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane parameter) *
    (Complex.exp ((parameter - cohomologicalPoint) *
        (logXi (evaluationPoint binary compact coordinates) : ℂ)) *
      (SectionMultipliers.heightMultiplier logXi real exponent
          (evaluationPoint binary compact coordinates) *
        sectionFunction (evaluationPoint binary compact coordinates * atInfinity real)))

/-- The scalar integrand of the flat family of `Φ_z` is `twistIntegrand`. -/
theorem localScalarIntegrand_twist {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) {logXi : AdelicGL → ℝ}
    (law : SectionMultipliers.HeightLaw logXi)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (binary : BinaryAdelicGL) (compact : AdelicGL) (exponent parameter : ℂ)
    (coordinates : LocalLine × LocalLine) :
    localScalarIntegrand data parameter
        (EdgeInputs.flatFamily data holomorphic
          (twistSection data law real exponent sectionValue) parameter)
        ((EdgeInputs.flatFamily_flat data holomorphic
          (twistSection data law real exponent sectionValue)).1 parameter)
        compact binary coordinates =
      twistIntegrand degree logXi sectionValue.val real binary compact parameter exponent
        coordinates := by
  unfold localScalarIntegrand
  rw [CuspLift.realizes]
  unfold EdgeInputs.flatFamily twistIntegrand evaluationPoint
  rw [SectionMultipliersFlat.linearFlatExtension_eq_xi data holomorphic law]
  all_goals rfl

/-- Splitting off the height multiplier: `twistIntegrand s z u = ρ_h(P)^z · twistIntegrand s 0 u`. -/
theorem twistIntegrand_eq_mul (degree : ℕ) (logXi : AdelicGL → ℝ)
    (sectionFunction : AdelicGL → ℂ) (real : RealGL3) (binary : BinaryAdelicGL)
    (compact : AdelicGL) (parameter exponent : ℂ) (coordinates : LocalLine × LocalLine) :
    twistIntegrand degree logXi sectionFunction real binary compact parameter exponent
        coordinates =
      SectionMultipliers.heightMultiplier logXi real exponent
          (evaluationPoint binary compact coordinates) *
        twistIntegrand degree logXi sectionFunction real binary compact parameter 0
          coordinates := by
  unfold twistIntegrand
  rw [SectionMultipliers.heightMultiplier_zero]
  ring

/-- The exponent `e(s) = (n + 3) / 2 + 1 / 2 + s / 3` of the plane induction is continuous. -/
theorem binaryInductionExponent_plane_continuous (degree : ℕ) :
    Continuous (fun parameter : ℂ => binaryInductionExponent degree .plane parameter) := by
  simp only [binaryInductionExponent, inductionExponent]
  exact continuous_const.add (continuous_const.add (continuous_id.div_const _))

/-- `twistIntegrand · · u` is jointly continuous in `(s, z)`. -/
theorem twistIntegrand_continuous (degree : ℕ) (logXi : AdelicGL → ℝ)
    (sectionFunction : AdelicGL → ℂ) (real : RealGL3) (binary : BinaryAdelicGL)
    (compact : AdelicGL) (coordinates : LocalLine × LocalLine) :
    Continuous (fun p : ℂ × ℂ =>
      twistIntegrand degree logXi sectionFunction real binary compact p.1 p.2 coordinates) := by
  have normPart : Continuous (fun p : ℂ × ℂ => normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .plane p.1)) := by
    unfold normPower
    exact (((binaryInductionExponent_plane_continuous degree).comp continuous_fst).neg.mul
      continuous_const).cexp
  have shiftPart : Continuous (fun p : ℂ × ℂ => Complex.exp ((p.1 - cohomologicalPoint) *
      (logXi (evaluationPoint binary compact coordinates) : ℂ))) :=
    ((continuous_fst.sub continuous_const).mul continuous_const).cexp
  have multiplierPart : Continuous (fun p : ℂ × ℂ =>
      SectionMultipliers.heightMultiplier logXi real p.2
        (evaluationPoint binary compact coordinates)) := by
    unfold SectionMultipliers.heightMultiplier
    exact (continuous_snd.mul continuous_const).cexp
  unfold twistIntegrand
  exact normPart.mul (shiftPart.mul (multiplierPart.mul continuous_const))

/-- A maximal compact element has integral finite part. -/
theorem integralArguments_of_compact {compact : AdelicGL} (membership : inMaximalCompact compact) :
    compact ∈ integralArguments := by
  obtain ⟨integral, equality⟩ := membership.2
  exact ⟨integral, equality.symm⟩

/-- The realization at `B` of the local Hilbert standard integral of the flat family of `Φ_z`,
at `κ` in the maximal compact subgroup and `Re s > -n/2 - 1`, is the integral of `twistIntegrand`. -/
theorem localScalar_twist_eq_integral {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) {logXi : AdelicGL → ℝ}
    (law : SectionMultipliers.HeightLaw logXi)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (parameter exponent : ℂ) (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re)
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (binary : BinaryAdelicGL) :
    EdgeInputs.localScalar data holomorphic (twistSection data law real exponent sectionValue)
        parameter compact binary =
      ∫ coordinates, twistIntegrand degree logXi sectionValue.val real binary compact parameter
        exponent coordinates ∂localRadicalMeasure := by
  have integral := integralArguments_of_compact compactMembership
  have memberSmooth : EdgeInputs.localVector data holomorphic
      (twistSection data law real exponent sectionValue) parameter compact ∈ data.cusp.smooth :=
    localValue_mem_smooth data parameter
      (EdgeInputs.flatFamily data holomorphic (twistSection data law real exponent sectionValue)
        parameter)
      ((EdgeInputs.flatFamily_flat data holomorphic
        (twistSection data law real exponent sectionValue)).1 parameter) halfPlane compact integral
  have equality : EdgeInputs.localScalar data holomorphic
      (twistSection data law real exponent sectionValue) parameter compact binary =
      data.cusp.realize ⟨EdgeInputs.localVector data holomorphic
        (twistSection data law real exponent sectionValue) parameter compact, memberSmooth⟩
        binary := by
    unfold EdgeInputs.localScalar
    exact EdgeInputs.vecScalar_of_mem data memberSmooth binary
  rw [equality]
  refine (localValue_realizes data
    (EdgeInputs.flatFamily data holomorphic (twistSection data law real exponent sectionValue))
    (EdgeInputs.flatFamily_flat data holomorphic
      (twistSection data law real exponent sectionValue))
    parameter halfPlane compact integral binary).trans ?_
  exact congrArg
    (fun function : LocalLine × LocalLine → ℂ => ∫ coordinates, function coordinates
      ∂localRadicalMeasure)
    (funext fun coordinates => localScalarIntegrand_twist data holomorphic law sectionValue real
      binary compact exponent parameter coordinates)

end TernaryPeriodPolynomials.EdgeConvergence.HCTwist
