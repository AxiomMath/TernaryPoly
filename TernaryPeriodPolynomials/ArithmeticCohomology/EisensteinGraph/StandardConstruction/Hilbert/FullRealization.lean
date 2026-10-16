module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.ScalarLimit
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.CompactDecomposition

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertFullRealization

theorem lineLevi_split (unit : Adelesˣ) (binary : BinaryAdelicGL) :
    lineLevi unit binary = lineLevi unit 1 * lineLevi 1 binary := by
  simpa only [Prod.mk_mul_mk, mul_one, one_mul, lineLeviHom, MonoidHom.coe_mk, OneHom.coe_mk] using
    ((lineLeviHom Adeles).map_mul (unit, 1) (1, binary))

theorem vector_radical {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (first second : Adeles) (argument : AdelicGL) :
    HilbertStandardSmooth.vector data parameter function induced halfPlane
        (lineUnipotent first second * argument) =
      HilbertStandardSmooth.vector data parameter function induced halfPlane argument :=
  Subtype.ext (HilbertStandard.value_radical_invariant data parameter function induced first second argument)

theorem vector_rankOne {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (unit : Adelesˣ) (argument : AdelicGL) :
    HilbertStandardSmooth.vector data parameter function induced halfPlane (lineLevi unit 1 * argument) =
      (data.chi.toMonoidHom unit * normPower unit (2 * inductionExponent .line parameter)) •
        HilbertStandardSmooth.vector data parameter function induced halfPlane argument :=
  Subtype.ext (HilbertStandardAlgebra.value_rankOne data parameter function induced unit argument)

theorem vector_binary {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (binary : BinaryAdelicGL) (argument : AdelicGL) :
    HilbertStandardSmooth.vector data parameter function induced halfPlane (lineLevi 1 binary * argument) =
      normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .line parameter) •
        CuspRealization.smoothAction data.cusp binary
          (HilbertStandardSmooth.vector data parameter function induced halfPlane argument) :=
  Subtype.ext (HilbertBinaryCovariance.value_lineLevi data parameter function induced binary argument)

/-- The full Hilbert integral realizes the full scalar integral at every adelic base. -/
theorem value_realizes_one {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    data.cusp.realize (HilbertStandardSmooth.vector data parameter (extension parameter)
      (flat.1 parameter) halfPlane argument) 1 =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure := by
  obtain ⟨first, second, unit, binary, compact, compactMembership, decomposition⟩ :=
    LineCompactDecomposition.adelic_radical_lineCompact argument
  rw [decomposition, mul_assoc (lineUnipotent first second), vector_radical,
    StandardInvariance.integral_lineRadical, lineLevi_split,
    mul_assoc (lineLevi unit 1), vector_rankOne, map_smul, Pi.smul_apply,
    StandardRankOne.integral_rankOne_normalized data extension flat]
  congr 1
  rw [vector_binary, map_smul, Pi.smul_apply]
  change normPower _ _ * data.cusp.realize
    (CuspRealization.smoothAction data.cusp binary
      (HilbertStandardSmooth.vector data parameter (extension parameter) (flat.1 parameter) halfPlane compact)) 1 = _
  rw [CuspRealization.realize_equivariant, one_mul,
    HilbertScalarLimit.compact_value_realizes data extension flat parameter halfPlane compact compactMembership binary]
  exact (ScalarBinaryIntegral.integral_lineLevi_normalized data parameter (extension parameter)
    (flat.1 parameter) binary compact).symm

theorem value_realizes {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) (test : BinaryAdelicGL) :
    data.cusp.realize (HilbertStandardSmooth.vector data parameter (extension parameter)
      (flat.1 parameter) halfPlane argument) test =
      ∫ coordinates, ScalarBinaryIntegral.cuspIntegrand data parameter (extension parameter)
        (flat.1 parameter) test argument coordinates ∂radicalMeasure := by
  have equality := value_realizes_one data extension flat parameter halfPlane (lineLevi 1 test * argument)
  rw [vector_binary, map_smul, Pi.smul_apply] at equality
  change normPower _ _ * data.cusp.realize
    (CuspRealization.smoothAction data.cusp test
      (HilbertStandardSmooth.vector data parameter (extension parameter) (flat.1 parameter) halfPlane argument)) 1 = _
    at equality
  rw [CuspRealization.realize_equivariant, one_mul] at equality
  have normalized := ScalarBinaryIntegral.integral_lineLevi_normalized data parameter
    (extension parameter) (flat.1 parameter) test argument
  exact mul_left_cancel₀ (ParabolicInvariance.normPower_ne_zero _ _) (equality.trans normalized)

theorem value_realizes_normalized {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) (test : BinaryAdelicGL) :
    data.cusp.realize (HilbertStandardSmooth.vector data parameter (extension parameter)
      (flat.1 parameter) halfPlane argument) test =
      normPower (GeneralLinearGroup.det test) (-binaryInductionExponent degree .line parameter) *
        ∫ coordinates, standardIntegrand extension parameter (lineLevi 1 test * argument)
          coordinates ∂radicalMeasure := by
  rw [value_realizes data extension flat parameter halfPlane]
  have normalization := ScalarBinaryIntegral.integral_lineLevi_normalized data parameter
    (extension parameter) (flat.1 parameter) test argument
  change (∫ coordinates, standardIntegrand extension parameter (lineLevi 1 test * argument)
    coordinates ∂radicalMeasure) = _ at normalization
  rw [normalization, ParabolicInvariance.normPower_neg_mul]

/-- The line cusp lift in the definition of normalized induction is supplied by
the actual full Hilbert integral, with its proved smooth real right orbit. -/
theorem hasSmoothCuspLift {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSmoothCuspLift data .line parameter (fun (_ : Fin 0 → RealGL3) argument =>
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure) := by
  intro argument
  refine ⟨fun real => HilbertStandardSmooth.vector data parameter (extension parameter)
    (flat.1 parameter) halfPlane (argument * atInfinity (real 0)),
    HilbertStandardSmooth.right_smooth data parameter (extension parameter) (flat.1 parameter)
      halfPlane argument, ?_⟩
  intro real test
  exact value_realizes_normalized data extension flat parameter halfPlane
    (argument * atInfinity (real 0)) test

theorem normalized_binaryOrbit_mem {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    (fun test : BinaryAdelicGL =>
      normPower (GeneralLinearGroup.det test) (-binaryInductionExponent degree .line parameter) *
        ∫ coordinates, standardIntegrand extension parameter (lineLevi 1 test * argument)
          coordinates ∂radicalMeasure) ∈ cuspFunctions data.cusp := by
  refine ⟨HilbertStandardSmooth.vector data parameter (extension parameter) (flat.1 parameter) halfPlane argument, ?_⟩
  funext test
  exact value_realizes_normalized data extension flat parameter halfPlane argument test

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertFullRealization
