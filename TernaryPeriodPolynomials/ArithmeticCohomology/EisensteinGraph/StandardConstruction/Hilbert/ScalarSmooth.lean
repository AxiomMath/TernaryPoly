module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.FullRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FixedFamilyAnalyticity

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertScalarSmooth

def lineBlockProduct (matrices : JointMatrix) : Fin 1 → PlaneMatrix :=
  fun _ => RightOrbitAnalyticity.lineBlock 1 matrices.1 * matrices.2

theorem lineBlockProduct_contDiff : ContDiff ℝ ⊤ lineBlockProduct := by
  apply contDiff_pi.mpr
  intro index
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;>
    simp [lineBlockProduct, Matrix.mul_apply, Fin.sum_univ_three, RightOrbitAnalyticity.lineBlock] <;> fun_prop

theorem lineBlockProduct_mapsTo : Set.MapsTo lineBlockProduct jointDomain (SmoothJets.domain 3 1) := by
  intro matrices membership index
  change (RightOrbitAnalyticity.lineBlock 1 matrices.1 * matrices.2).det ≠ 0
  rw [Matrix.det_mul, RightOrbitAnalyticity.lineBlock_det]
  exact mul_ne_zero membership.1 membership.2

def matrixVector {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (finite : FiniteGL)
    (matrix : PlaneMatrix) : data.cusp.smooth :=
  HilbertStandardSmooth.vector data parameter function induced halfPlane
    (atFinite finite * atInfinity (invertibleMatrix matrix))

def jointModel {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (finite : FiniteGL) (matrices : JointMatrix) : data.cusp.H :=
  normalization (-binaryInductionExponent degree .line parameter) matrices •
    AdelicTaylorBounds.rightMatrix (HilbertStandard.value data parameter function induced)
      (atFinite finite) (lineBlockProduct matrices)

theorem jointModel_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (finite : FiniteGL) :
    ContDiffOn ℝ ⊤ (jointModel data parameter function induced finite) jointDomain :=
  (normalization_contDiffOn _).smul
    ((HilbertStandardSmooth.right_smooth data parameter function induced halfPlane (atFinite finite)).comp
      lineBlockProduct_contDiff.contDiffOn lineBlockProduct_mapsTo)

theorem jointModel_at_units {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (finite : FiniteGL) (binary : BinaryRealGL) (real : RealGL3) :
    jointModel data parameter function induced finite (binary.val, real.val) =
      data.cusp.π (atInfinity binary)
        (HilbertStandard.value data parameter function induced (atFinite finite * atInfinity real)) := by
  have productEquality : lineBlockProduct (binary.val, real.val) =
      fun _ => (lineLevi 1 binary * real).val := by
    funext index
    change RightOrbitAnalyticity.lineBlock 1 binary.val * real.val = (lineLevi 1 binary).val * real.val
    congr 1
    simp only [RightOrbitAnalyticity.lineBlock, lineLevi_val, Units.val_one]
  have argumentEquality : atFinite finite * atInfinity (lineLevi 1 binary * real) =
      lineLevi 1 (atInfinity binary) * (atFinite finite * atInfinity real) := by
    rw [RealTranslations.atInfinity_mul, ← HilbertStandardSmooth.lineLevi_atInfinity,
      ← mul_assoc, TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, mul_assoc]
  unfold jointModel AdelicTaylorBounds.rightMatrix SmoothJets.matrixExtension
  simp only [productEquality, invertibleMatrix_units]
  rw [argumentEquality]
  have normalizationEquality : normalization (-binaryInductionExponent degree .line parameter)
      (binary.val, real.val) = normPower (GeneralLinearGroup.det (atInfinity binary))
        (-binaryInductionExponent degree .line parameter) := by
    rw [SmoothNormPower.normPower_det_atInfinity]
    simp only [normalization, Real.log_abs]
  rw [normalizationEquality]
  exact HilbertUniformCompact.normalizedValue_eq_action data parameter function induced
    (atInfinity binary) (atFinite finite * atInfinity real)

theorem jointOrbit_analyticAt {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (finite : FiniteGL) (real : RealGL3) :
    AnalyticAt ℝ (LocalAnalyticFamilies.familyOrbit data.cusp
      (fun matrix => (matrixVector data parameter function induced halfPlane finite matrix).val)) (1, real.val) := by
  have jointSmooth : ContDiffOn ℝ ⊤ (LocalAnalyticFamilies.familyOrbit data.cusp
      (fun matrix => (matrixVector data parameter function induced halfPlane finite matrix).val)) jointDomain := by
    apply (jointModel_smooth data parameter function induced halfPlane finite).congr
    intro matrices membership
    have equality := jointModel_at_units data parameter function induced finite
      (invertibleMatrix matrices.1) (invertibleMatrix matrices.2)
    change data.cusp.π (atInfinity (invertibleMatrix matrices.1))
      (HilbertStandard.value data parameter function induced
        (atFinite finite * atInfinity (invertibleMatrix matrices.2))) = _
    simpa only [invertibleMatrix_val _ membership.1, invertibleMatrix_val _ membership.2,
      Prod.mk.eta] using equality.symm
  have membership : ((1 : BinaryMatrix), real.val) ∈ jointDomain :=
    ⟨by simp, GeneralLinearGroup.det_ne_zero real⟩
  exact (jointSmooth.contDiffAt (jointDomain_isOpen.mem_nhds membership)).analyticAt

theorem scalar_matrix_analyticAt {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (integral : GL3 IntegralAdeles) (real : RealGL3) (test : BinaryAdelicGL) :
    AnalyticAt ℝ (fun matrix => data.cusp.realize
      (matrixVector data parameter function induced halfPlane (GeneralLinearGroup.map integralEmbedding integral) matrix)
      test) real.val := by
  have compact : inMaximalCompact (atFinite (GeneralLinearGroup.map integralEmbedding integral)) := by
    constructor
    · rw [InducedContinuity.realGroup_atFinite]
      simp
    · rw [InducedContinuity.finiteGroup_atFinite]
      exact ⟨integral, rfl⟩
  exact FixedFamilyAnalyticity.scalar_analyticAt data.cusp BinaryLevel.finiteCongruence
    BinaryLevel.finiteCongruence_isOpen BinaryLevel.finiteCongruence_isCompact
    (EndpointAdmissibility.all_finiteDimensional data)
    (matrixVector data parameter function induced halfPlane (GeneralLinearGroup.map integralEmbedding integral))
    (fun matrix => HilbertFixedStandard.value_principal_fixed_rightReal data parameter function induced _ compact _)
    real.val (jointOrbit_analyticAt data parameter function induced halfPlane _ real) test

theorem scalar_integralFinite_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (integral : GL3 IntegralAdeles) (test : BinaryAdelicGL) :
    Smooth (fun real : Fin 1 → RealGL3 => data.cusp.realize
      (HilbertStandardSmooth.vector data parameter function induced halfPlane
        (atFinite (GeneralLinearGroup.map integralEmbedding integral) * atInfinity (real 0))) test) := by
  apply (SmoothAnalyticity.smooth_iff_analyticOn _).mpr
  intro matrices membership
  have analytic := scalar_matrix_analyticAt data parameter function induced halfPlane integral
    (invertibleMatrix (matrices 0)) test
  rw [invertibleMatrix_val _ (membership 0)] at analytic
  let projection : SmoothJets.MatrixTuples 3 1 →L[ℝ] PlaneMatrix := ContinuousLinearMap.proj 0
  exact (analytic.fun_comp (f := fun other : SmoothJets.MatrixTuples 3 1 => other 0)
    (x := matrices) (projection.analyticAt matrices)).analyticWithinAt

theorem smooth_mul_left {size arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E) (smooth : Smooth function)
    (left : Fin arity → GeneralLinearGroup (Fin size) ℝ) :
    Smooth (fun real => function (fun index => left index * real index)) := by
  let linear := TranslatedJets.tupleLeftMulL (fun index => (left index).val)
  have maps : Set.MapsTo linear (SmoothJets.domain size arity) (SmoothJets.domain size arity) := by
    intro matrices membership
    change matrices ∈ linear ⁻¹' SmoothJets.domain size arity
    rw [TranslatedJets.preimage_domain]
    exact membership
  apply (smooth.comp linear.contDiff.contDiffOn maps).congr
  intro matrices membership
  change function (fun index => left index * invertibleMatrix (matrices index)) =
    function (fun index => invertibleMatrix ((left index).val * matrices index))
  congr 1
  funext index
  exact (TranslatedJets.invertibleMatrix_mul_left (left index) (matrices index) (membership index)).symm

theorem scalar_compact_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) (compact : inMaximalCompact argument) (test : BinaryAdelicGL) :
    Smooth (fun real : Fin 1 → RealGL3 => data.cusp.realize
      (HilbertStandardSmooth.vector data parameter function induced halfPlane (argument * atInfinity (real 0))) test) := by
  obtain ⟨integral, equality⟩ := compact.2
  have decomposition : argument =
      atFinite (GeneralLinearGroup.map integralEmbedding integral) * atInfinity (realGroup argument) := by
    apply InducedContinuity.adelic_ext
    · simp only [map_mul, InducedContinuity.realGroup_atFinite, InducedContinuity.realGroup_atInfinity, one_mul]
    · simp only [map_mul, InducedContinuity.finiteGroup_atFinite, InducedContinuity.finiteGroup_atInfinity, mul_one]
      exact equality.symm
  have smooth := smooth_mul_left _ (scalar_integralFinite_smooth data parameter function induced halfPlane integral test)
    (fun _ : Fin 1 => realGroup argument)
  have agreement : (fun real : Fin 1 → RealGL3 => data.cusp.realize
      (HilbertStandardSmooth.vector data parameter function induced halfPlane (argument * atInfinity (real 0))) test) =
      (fun real : Fin 1 → RealGL3 => data.cusp.realize
        (HilbertStandardSmooth.vector data parameter function induced halfPlane
          (atFinite (GeneralLinearGroup.map integralEmbedding integral) *
            atInfinity (realGroup argument * real 0))) test) := by
    funext real
    rw [RealTranslations.atInfinity_mul, ← mul_assoc, ← decomposition]
  rw [agreement]
  exact smooth

/-- Scalar smoothness for the actual full standard integral, for every base and
every degree in the convergence half-plane. -/
theorem standard_smooth {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    Smooth (fun real : Fin 1 → RealGL3 =>
      ∫ coordinates, standardIntegrand extension parameter (argument * atInfinity (real 0))
        coordinates ∂radicalMeasure) := by
  obtain ⟨first, second, unit, binary, compact, compactMembership, decomposition⟩ :=
    LineCompactDecomposition.adelic_radical_lineCompact argument
  have agreement : (fun real : Fin 1 → RealGL3 =>
      ∫ coordinates, standardIntegrand extension parameter (argument * atInfinity (real 0))
        coordinates ∂radicalMeasure) =
      (fun real : Fin 1 → RealGL3 =>
        (data.chi.toMonoidHom unit * normPower unit (2 * inductionExponent .line parameter)) *
          (normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .line parameter) *
            data.cusp.realize (HilbertStandardSmooth.vector data parameter (extension parameter)
              (flat.1 parameter) halfPlane (compact * atInfinity (real 0))) binary)) := by
    funext real
    rw [← HilbertFullRealization.value_realizes_one data extension flat parameter halfPlane,
      decomposition]
    simp only [mul_assoc]
    rw [HilbertFullRealization.vector_radical, HilbertFullRealization.lineLevi_split,
      mul_assoc, HilbertFullRealization.vector_rankOne, HilbertFullRealization.vector_binary,
      map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, CuspRealization.realize_equivariant, one_mul]
    simp only [smul_eq_mul, mul_assoc]
  rw [agreement]
  exact contDiffOn_const.mul (contDiffOn_const.mul
    (scalar_compact_smooth data parameter (extension parameter) (flat.1 parameter) halfPlane compact compactMembership binary))

theorem standard_induced {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    IsInduced data .line parameter
      (fun argument => ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure) := by
  refine ⟨standard_smooth data extension flat parameter halfPlane, ?_,
    HilbertFullRealization.hasSmoothCuspLift data extension flat parameter halfPlane, ?_, ?_, ?_⟩
  · intro level argument
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with coordinates
    unfold standardIntegrand
    rw [← mul_assoc, (flat.1 parameter).2.1 level]
  · intro first second argument
    exact StandardInvariance.integral_lineRadical extension parameter argument first second
  · exact StandardRankOne.integral_rankOne_normalized data extension flat parameter
  · exact HilbertFullRealization.normalized_binaryOrbit_mem data extension flat parameter halfPlane

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertScalarSmooth
