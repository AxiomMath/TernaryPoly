module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.OrbitIntegral
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.Coefficients

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitCoefficients

theorem kernel_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (finiteTest : Rectangular FiniteAdeles → ℂ) (continuous : Continuous finiteTest)
    (compact : HasCompactSupport finiteTest) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (point : FiniteGL) :
    Integrable (kernel data vector finiteTest parameter point) BinaryProductHaar.finiteMeasure := by
  obtain ⟨cutoff, smooth, supportCompact, supported, massNonzero⟩ := exists_cutoff
  obtain ⟨indices, radii, positive, realTest, _, image⟩ :=
    BinaryOrbitProfile.exists_supported_test data vector fixed parameter cutoff smooth supportCompact supported
  have smoothImage (value : RealSpace) :
      (ProductStages.smoothMap data.cusp radii positive (realTest value)).val.val =
        cutoff (RectangularTransport.coordinateEquiv.symm value) •
          BinaryOrbitProfile.profile data vector parameter (RectangularTransport.coordinateEquiv.symm value) := by
    rw [ProductStages.smoothMap_hilbert]
    exact image value
  have rawIntegrable := VectorUnfolding.raw_integrable_at data (ProductStages.smoothMap data.cusp radii positive)
    (ProductStages.smoothMap_continuous data.cusp radii positive) realTest finiteTest continuous compact parameter (atFinite point) halfPlane
  rw [liftTest_eq data vector radii positive cutoff finiteTest parameter realTest smoothImage] at rawIntegrable
  have productIntegrable := (BinaryProductHaar.integrable_iff _).mp rawIntegrable
  simp only [integrand_separated data vector cutoff supported finiteTest parameter point] at productIntegrable
  have integrated := productIntegrable.integral_prod_right
  simp only [integral_mul_const] at integrated
  have identityFrame : IntegralFrameOrbit.realFrame 1 = columns (1 : TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth.PlaneMatrix) := by
    rw [IntegralFrameOrbit.realFrame, map_one, inv_one, Units.val_one]
  have nonzero : (∫ binary : BinaryRealGL,
      (cutoff (columns (1 : TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth.PlaneMatrix) * binary.val) : ℂ) ∂BinaryProductHaar.realMeasure) ≠ 0 := by
    simpa only [RealOrbitalMass.mass, identityFrame] using massNonzero
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr nonzero) _).mp integrated

theorem exists_box_meromorphic {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (scale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) (point : FiniteGL) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : ℂ, (1 - (degree : ℝ)) / 2 < parameter.re →
        continuation parameter = coefficientIntegral data vector (RectangularAdelicPoisson.finiteTest scale offset) parameter point := by
  obtain ⟨cutoff, smooth, compact, supported, nonzero⟩ := exists_cutoff
  obtain ⟨indices, radii, positive, tests, image, result⟩ :=
    BinaryOrbitTestFamilies.exists_continuation data vector fixed cutoff smooth compact supported
  obtain ⟨_, meromorphic, equality⟩ := result scale offset
  let average (parameter : ℂ) := PlaneConstantTerm.average
    (fun argument => VectorGodementContinuation.continuation data
      (ProductStages.smoothMap data.cusp radii positive) (tests parameter) scale offset parameter argument) (atFinite point)
  let factor (parameter : ℂ) := RealOrbitalMass.mass cutoff 1 *
    outerCharacter data parameter (GeneralLinearGroup.det (atFinite point))
  have factorNonzero (parameter : ℂ) : factor parameter ≠ 0 :=
    mul_ne_zero nonzero (FrameProfile.character_ne_zero _ _)
  have factorMeromorphic (parameter : ℂ) : MeromorphicAt factor parameter :=
    analyticAt_const.meromorphicAt.mul
      ((ZeroConstantThetaIntegral.outer_differentiable data (GeneralLinearGroup.det (atFinite point))).analyticAt parameter).meromorphicAt
  refine ⟨fun parameter => (factor parameter)⁻¹ * average parameter,
    fun parameter => (factorMeromorphic parameter).inv.mul (meromorphic (atFinite point) parameter), ?_⟩
  intro parameter halfPlane
  have identity := equality parameter halfPlane (atFinite point)
  rw [liftTest_eq data vector radii positive cutoff _ parameter (tests parameter) (image parameter),
    section_eq data vector cutoff supported _ parameter point] at identity
  change (factor parameter)⁻¹ * average parameter = _
  change average parameter = factor parameter * _ at identity
  rw [identity, inv_mul_cancel_left₀ (factorNonzero parameter)]

theorem coefficientIntegral_boxes {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (boxes : FlatProfilePackages.Boxes) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (point : FiniteGL) :
    coefficientIntegral data vector boxes.test parameter point =
      ∑ index ∈ boxes.indices, boxes.coefficients index * coefficientIntegral data vector
        (RectangularAdelicPoisson.finiteTest (FiniteLatticeMeasure.rationalScale boxes.scale) index.out) parameter point := by
  have integrable (index : FiniteLatticeCosets.Space ⧸ FiniteLatticeCosets.latticeSubgroup
      (FiniteLatticeMeasure.rationalScale boxes.scale)) := (kernel_integrable data vector fixed _
    (ZeroConstantThetaDecay.finiteTest_continuous (FiniteLatticeMeasure.rationalScale boxes.scale) index.out)
    (ZeroConstantThetaDecay.finiteTest_compactSupport (FiniteLatticeMeasure.rationalScale boxes.scale) index.out)
    parameter halfPlane point).const_mul (boxes.coefficients index)
  unfold coefficientIntegral
  have kernelSum : kernel data vector boxes.test parameter point = fun binary =>
      ∑ index ∈ boxes.indices, boxes.coefficients index * kernel data vector
        (RectangularAdelicPoisson.finiteTest (FiniteLatticeMeasure.rationalScale boxes.scale) index.out) parameter point binary := by
    funext binary
    simp only [kernel, FlatProfilePackages.Boxes.test, Finset.sum_mul, mul_assoc]
  rw [kernelSum, integral_finsetSum boxes.indices (fun index _ => integrable index)]
  simp only [integral_const_mul]

theorem exists_boxes_meromorphic {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (boxes : FlatProfilePackages.Boxes) (point : FiniteGL) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : ℂ, (1 - (degree : ℝ)) / 2 < parameter.re →
        continuation parameter = coefficientIntegral data vector boxes.test parameter point := by
  choose continuations meromorphic equalities using fun index : FiniteLatticeCosets.Space ⧸
      FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale boxes.scale) =>
    exists_box_meromorphic data vector fixed (FiniteLatticeMeasure.rationalScale boxes.scale) index.out point
  refine ⟨fun parameter => ∑ index ∈ boxes.indices, boxes.coefficients index * continuations index parameter, ?_, ?_⟩
  · intro parameter
    apply MeromorphicAt.fun_sum
    intro index _
    exact analyticAt_const.meromorphicAt.mul (meromorphic index parameter)
  · intro parameter halfPlane
    rw [coefficientIntegral_boxes data vector fixed boxes parameter halfPlane point]
    apply Finset.sum_congr rfl
    intro index _
    rw [equalities index parameter halfPlane]

theorem exists_recovery_meromorphic {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : FiniteGL) (key : UniversalFiniteProfiles.Key data) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter : ℂ, (1 - (degree : ℝ)) / 2 < parameter.re →
        continuation parameter = ∫ binary : BinaryFiniteGL,
          RecoveryCoefficients.coefficient data parameter (atFinite point) key binary * data.cusp.realize vector (atFinite binary)
            ∂BinaryProductHaar.finiteMeasure :=
  exists_boxes_meromorphic data vector fixed (UniversalFiniteProfiles.boxes data key) point

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitCoefficients
