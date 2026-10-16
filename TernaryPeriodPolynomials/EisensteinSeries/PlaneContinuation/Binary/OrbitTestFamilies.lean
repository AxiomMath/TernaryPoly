module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.OrbitProfile
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ExponentialTestFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ParametricGodementContinuation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AveragedGodementContinuation
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.ConstantTerm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorMatrixOrbit
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitTestFamilies

def height (value : RealSpace) : ℝ := BinaryOrbitChart.height (coordinateEquiv.symm value)

theorem height_contDiffAt (value : RealSpace) (inside : coordinateEquiv.symm value ∈ BinaryOrbitChart.domain) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) height value :=
  ((BinaryOrbitChart.height_contDiffAt _ inside).of_le le_top).comp value
    coordinateEquiv.symm.toContinuousLinearEquiv.contDiff.contDiffAt

theorem exists_family {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ BinaryOrbitChart.domain) :
    ∃ indices : Finset (tsupport cutoff), ∃ radii : indices → ℝ≥0, ∃ positive : ∀ index, 0 < radii index,
      ∃ tests : ℂ → SchwartzMap RealSpace (ProductStages.Source data.cusp radii positive),
        (∀ parameter, tsupport (fun value => tests parameter value) ⊆ coordinateEquiv.symm ⁻¹' tsupport cutoff) ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (fun pair : ℂ × RealSpace => tests pair.1 pair.2) ∧
        (∀ value, Differentiable ℂ (fun parameter => tests parameter value)) ∧
        (∀ parameterSet : Set ℂ, IsCompact parameterSet → ∀ weight order : ℕ,
          ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameterSet,
            SchwartzMap.seminorm ℂ weight order (tests parameter) ≤ bound) ∧
        ∀ parameter value,
          ProductStages.hilbertMap data.cusp radii positive (tests parameter value) =
            cutoff (coordinateEquiv.symm value) • BinaryOrbitProfile.profile data vector parameter (coordinateEquiv.symm value) := by
  obtain ⟨indices, radii, positive, test, testSupport, image⟩ :=
    BinaryOrbitProfile.exists_supported_test data vector fixed 0 cutoff smooth compact supported
  have compactSupport : HasCompactSupport (fun value => test value) :=
    (coordinateEquiv.symm.toContinuousLinearEquiv.toHomeomorph.isCompact_preimage.mpr compact).of_isClosed_subset
      (isClosed_tsupport (fun value => test value)) testSupport
  have smoothHeight : ∀ point ∈ tsupport (fun value => test value), ContDiffAt ℝ (↑(⊤ : ℕ∞)) height point :=
    fun point membership => height_contDiffAt point (supported (testSupport membership))
  let tests := ExponentialTestFamilies.family 0 height test compactSupport smoothHeight
  refine ⟨indices, radii, positive, tests, ?_, ?_, ?_, ?_, ?_⟩
  · intro parameter
    exact (ExponentialTestFamilies.family_support 0 height test compactSupport smoothHeight parameter).trans testSupport
  · exact ExponentialTestFamilies.family_joint_contDiff 0 height test compactSupport smoothHeight
  · exact ExponentialTestFamilies.family_pointwise_differentiable 0 height test compactSupport smoothHeight
  · exact ExponentialTestFamilies.family_uniform_seminorms 0 height test compactSupport smoothHeight
  · intro parameter value
    change ProductStages.hilbertMap data.cusp radii positive
      (ExponentialTestFamilies.family 0 height test compactSupport smoothHeight parameter value) = _
    rw [ExponentialTestFamilies.family_apply, map_smul, image,
      BinaryOrbitProfile.parameter_shift data vector parameter 0]
    exact smul_comm _ _ _

theorem exists_continuation {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff) (supported : tsupport cutoff ⊆ BinaryOrbitChart.domain) :
    ∃ indices : Finset (tsupport cutoff), ∃ radii : indices → ℝ≥0, ∃ positive : ∀ index, 0 < radii index,
      ∃ tests : ℂ → SchwartzMap RealSpace (ProductStages.Source data.cusp radii positive),
        (∀ parameter value,
          (ProductStages.smoothMap data.cusp radii positive (tests parameter value)).val.val =
            cutoff (coordinateEquiv.symm value) • BinaryOrbitProfile.profile data vector parameter (coordinateEquiv.symm value)) ∧
        ∀ finiteScale : FiniteAdelesˣ, ∀ offset : FiniteRectangularFourier.Space,
          IsEisensteinContinuation
            (fun parameter point => VectorGodement.sectionFunction data
              (liftTest data (ProductStages.smoothMap data.cusp radii positive)
                (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset))) parameter point)
            (fun parameter point => VectorGodementContinuation.continuation data
              (ProductStages.smoothMap data.cusp radii positive) (tests parameter) finiteScale offset parameter point) ∧
          (∀ point parameter, MeromorphicAt (fun value => PlaneConstantTerm.average
            (fun argument => VectorGodementContinuation.continuation data
              (ProductStages.smoothMap data.cusp radii positive) (tests value) finiteScale offset value argument) point) parameter) ∧
          ∀ parameter, (1 - (degree : ℝ)) / 2 < parameter.re → ∀ point,
            PlaneConstantTerm.average (fun argument => VectorGodementContinuation.continuation data
              (ProductStages.smoothMap data.cusp radii positive) (tests parameter) finiteScale offset parameter argument) point =
              VectorGodement.sectionFunction data
                (liftTest data (ProductStages.smoothMap data.cusp radii positive)
                  (BanachAdelicTheta.tensorTest (tests parameter) (RectangularAdelicPoisson.finiteTest finiteScale offset))) parameter point := by
  obtain ⟨indices, radii, positive, tests, _, _, holomorphic, bounded, image⟩ :=
    exists_family data vector fixed cutoff smooth compact supported
  have uniform (parameters : Set ℂ) (compact : IsCompact parameters) :=
    UniformSchwartzBounds.image_family tests parameters (bounded parameters compact)
  refine ⟨indices, radii, positive, tests, ?_, ?_⟩
  · intro parameter value
    rw [ProductStages.smoothMap_hilbert]
    exact image parameter value
  · intro scale offset
    refine ⟨?_, ?_, ?_⟩
    · exact ParametricGodementContinuation.isEisensteinContinuation data
        (ProductStages.smoothMap data.cusp radii positive) (ProductStages.smoothMap_continuous data.cusp radii positive)
        tests holomorphic uniform scale offset
    · exact AveragedGodementContinuation.meromorphic data
        (ProductStages.smoothMap data.cusp radii positive) (ProductStages.smoothMap_continuous data.cusp radii positive)
        tests holomorphic uniform scale offset
    · intro parameter halfPlane point
      exact GodementConstantTerm.average_continuation data
        (ProductStages.smoothMap data.cusp radii positive) (ProductStages.smoothMap_continuous data.cusp radii positive)
        (tests parameter) scale offset parameter halfPlane point

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitTestFamilies
