module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.OrbitLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Cohomological
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.FixedSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.MaximalCompact

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertFixedStandard

theorem atInfinity_continuous : Continuous (atInfinity : RealGL3 → AdelicGL) := by
  exact (MaximalCompact.combineGL_continuous (size := 3)).comp
    (continuous_id.prodMk continuous_const)

theorem value_fixed {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (argument : AdelicGL) :
    HilbertStandard.value data parameter function induced argument ∈
      CuspFixedSpace.fixed data.cusp (LineOrbitLevel.level argument) := by
  intro unit
  obtain ⟨levelElement, translation⟩ := LineOrbitLevel.level_translate argument unit
  have covariance := HilbertBinaryCovariance.value_lineLevi data parameter function induced
    (atFinite unit.val) argument
  rw [translation, HilbertStandard.value_finite_invariant data parameter function induced
    levelElement argument] at covariance
  have normalization : normPower (GeneralLinearGroup.det (atFinite unit.val))
      (binaryInductionExponent degree .line parameter) = 1 := by
    simp [normPower, LineOrbitLevel.level_det_norm_one argument unit]
  rw [normalization, one_smul] at covariance
  exact covariance.symm

theorem value_fixed_rightReal {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (real : RealGL3) :
    HilbertStandard.value data parameter function induced (argument * atInfinity real) ∈
      CuspFixedSpace.fixed data.cusp (LineOrbitLevel.level argument) := by
  rw [← LineOrbitLevel.level_rightReal argument real]
  exact value_fixed data parameter function induced (argument * atInfinity real)

theorem value_principal_fixed_rightReal {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (membership : inMaximalCompact argument)
    (real : RealGL3) :
    HilbertStandard.value data parameter function induced (argument * atInfinity real) ∈
      CuspFixedSpace.fixed data.cusp CuspCommonLevel.principal := by
  intro unit
  exact value_fixed_rightReal data parameter function induced argument real
    ⟨unit.val, LineOrbitLevel.principal_le_level_of_compact argument membership unit.property⟩

def fixedValue {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (argument : AdelicGL) :
    CuspFixedSpace.fixed data.cusp (LineOrbitLevel.level argument) :=
  ⟨HilbertStandard.value data parameter function induced argument,
    value_fixed data parameter function induced argument⟩

def principalValue {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (membership : inMaximalCompact argument)
    (real : RealGL3) :
    CuspFixedSpace.fixed data.cusp CuspCommonLevel.principal :=
  ⟨HilbertStandard.value data parameter function induced (argument * atInfinity real),
    value_principal_fixed_rightReal data parameter function induced argument membership real⟩

theorem principalValue_analytic_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (membership : inMaximalCompact argument)
    (real : RealGL3) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    AnalyticAt ℂ (fun spectral => principalValue data spectral
      (extension spectral) (flat.1 spectral) argument membership real) parameter := by
  let projection :=
    (CuspFixedSpace.fixed data.cusp CuspCommonLevel.principal).orthogonalProjectionOnto
  have pointwise (spectral : ℂ) :
      projection (HilbertStandard.value data spectral (extension spectral)
        (flat.1 spectral) (argument * atInfinity real)) =
          principalValue data spectral (extension spectral) (flat.1 spectral)
            argument membership real :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (principalValue data spectral (extension spectral) (flat.1 spectral)
        argument membership real)
  have analyticity : AnalyticAt ℂ
      (fun spectral => projection (HilbertStandard.value data spectral
        (extension spectral) (flat.1 spectral) (argument * atInfinity real))) parameter :=
    (projection.analyticAt _).comp
      (HilbertFlat.standard_analytic_halfPlane data extension flat
        (argument * atInfinity real) parameter halfPlane)
  simpa only [pointwise] using analyticity

theorem principalValue_jointContinuousAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (membership : inMaximalCompact argument)
    (parameter : ℂ) (real : RealGL3)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    ContinuousAt (fun pair : ℂ × RealGL3 => principalValue data pair.1
      (extension pair.1) (flat.1 pair.1) argument membership pair.2) (parameter, real) := by
  let projection :=
    (CuspFixedSpace.fixed data.cusp CuspCommonLevel.principal).orthogonalProjectionOnto
  have pointwise (pair : ℂ × RealGL3) :
      projection (HilbertStandard.value data pair.1 (extension pair.1)
        (flat.1 pair.1) (argument * atInfinity pair.2)) =
          principalValue data pair.1 (extension pair.1) (flat.1 pair.1)
            argument membership pair.2 :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (principalValue data pair.1 (extension pair.1) (flat.1 pair.1)
        argument membership pair.2)
  have realContinuous : Continuous (fun value : RealGL3 => argument * atInfinity value) :=
    continuous_const.mul atInfinity_continuous
  have inputContinuous : Continuous (fun pair : ℂ × RealGL3 =>
      (pair.1, argument * atInfinity pair.2)) :=
    continuous_fst.prodMk (realContinuous.comp continuous_snd)
  have integralContinuous : ContinuousAt (fun pair : ℂ × RealGL3 =>
      HilbertStandard.value data pair.1 (extension pair.1) (flat.1 pair.1)
        (argument * atInfinity pair.2)) (parameter, real) :=
    ContinuousAt.comp'
      (f := fun pair : ℂ × RealGL3 => (pair.1, argument * atInfinity pair.2))
      (g := fun pair : ℂ × AdelicGL =>
        HilbertStandard.value data pair.1 (extension pair.1) (flat.1 pair.1) pair.2)
      (x := (parameter, real))
      (HilbertTruncation.standard_joint_continuousAt data extension flat parameter
        (argument * atInfinity real) halfPlane) inputContinuous.continuousAt
  have projectedContinuous : ContinuousAt (fun pair : ℂ × RealGL3 =>
      projection (HilbertStandard.value data pair.1 (extension pair.1)
        (flat.1 pair.1) (argument * atInfinity pair.2))) (parameter, real) :=
    projection.continuous.continuousAt.comp integralContinuous
  simpa only [pointwise] using projectedContinuous

theorem cohomological_fixed {degree : ℕ} (data : InducingData degree)
    (atLeastFour : 4 ≤ degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    HilbertCohomological.valueLinear data atLeastFour sectionValue argument ∈
      CuspFixedSpace.fixed data.cusp (LineOrbitLevel.level argument) :=
  value_fixed data cohomologicalPoint sectionValue.val sectionValue.property argument

theorem fixedValue_analytic_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    AnalyticAt ℂ (fun spectral =>
      fixedValue data spectral (extension spectral) (flat.1 spectral) argument) parameter := by
  let projection :=
    (CuspFixedSpace.fixed data.cusp (LineOrbitLevel.level argument)).orthogonalProjectionOnto
  have pointwise (spectral : ℂ) :
      projection (HilbertStandard.value data spectral (extension spectral)
        (flat.1 spectral) argument) =
          fixedValue data spectral (extension spectral) (flat.1 spectral) argument :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (fixedValue data spectral (extension spectral) (flat.1 spectral) argument)
  have analyticity : AnalyticAt ℂ
      (fun spectral => projection (HilbertStandard.value data spectral
        (extension spectral) (flat.1 spectral) argument)) parameter :=
    (projection.analyticAt _).comp
      (HilbertFlat.standard_analytic_halfPlane data extension flat argument parameter halfPlane)
  simpa only [pointwise] using analyticity

theorem cohomological_fixed_analytic {degree : ℕ} (data : InducingData degree)
    (atLeastFour : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    ∃ extension : EisensteinValue.flatFamilies data,
      extension.val cohomologicalPoint = sectionValue.val ∧
      AnalyticAt ℂ (fun spectral => fixedValue data spectral
        (extension.val spectral) (extension.property.1 spectral) argument)
        cohomologicalPoint := by
  let extension := SectionSpace.linearFlatExtension data holomorphic sectionValue
  exact ⟨extension, SectionSpace.linearFlatExtension_endpoint data holomorphic sectionValue,
    fixedValue_analytic_halfPlane data extension.val extension.property argument
      cohomologicalPoint (HilbertCohomological.point_in_halfPlane degree atLeastFour)⟩

theorem cohomological_principal_analytic {degree : ℕ} (data : InducingData degree)
    (atLeastFour : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) (membership : inMaximalCompact argument)
    (real : RealGL3) :
    ∃ extension : EisensteinValue.flatFamilies data,
      extension.val cohomologicalPoint = sectionValue.val ∧
      AnalyticAt ℂ (fun spectral => principalValue data spectral
        (extension.val spectral) (extension.property.1 spectral) argument membership real)
        cohomologicalPoint := by
  let extension := SectionSpace.linearFlatExtension data holomorphic sectionValue
  exact ⟨extension, SectionSpace.linearFlatExtension_endpoint data holomorphic sectionValue,
    principalValue_analytic_halfPlane data extension.val extension.property
      argument membership real cohomologicalPoint
      (HilbertCohomological.point_in_halfPlane degree atLeastFour)⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertFixedStandard
