module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CohomologicalLift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothParameterDerivative

noncomputable def matrixFamily (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (matrix : BinaryMatrix) : data.H := (family (invertibleMatrix matrix)).val

noncomputable def jointFamily (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (matrices : BinaryMatrix × BinaryMatrix) : data.H :=
  realOrbit data (matrixFamily data family matrices.2) matrices.1

theorem jointFamily_contDiffOn (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (regularity : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (family (x 0))).val)) :
    ContDiffOn ℝ ⊤ (jointFamily data family) (binaryDomain ×ˢ binaryDomain) := by
  change ContDiffOn ℝ ⊤
    (fun matrices : Fin 2 → BinaryMatrix => data.π (atInfinity (invertibleMatrix (matrices 1)))
      (family (invertibleMatrix (matrices 0))).val)
    {matrices | ∀ position, (matrices position).det ≠ 0} at regularity
  have insertion : ContDiff ℝ ⊤ (fun matrices : BinaryMatrix × BinaryMatrix =>
      ![matrices.2, matrices.1]) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact contDiff_snd
    · exact contDiff_fst
  have mapsTo : Set.MapsTo (fun matrices : BinaryMatrix × BinaryMatrix => ![matrices.2, matrices.1])
      (binaryDomain ×ˢ binaryDomain) {x : Fin 2 → BinaryMatrix | ∀ position, (x position).det ≠ 0} := by
    intro matrices membership position
    fin_cases position
    · exact membership.2
    · exact membership.1
  have composition := regularity.comp insertion.contDiffOn mapsTo
  change ContDiffOn ℝ ⊤ (fun matrices : BinaryMatrix × BinaryMatrix =>
    data.π (atInfinity (invertibleMatrix matrices.1)) (family (invertibleMatrix matrices.2)).val)
    (binaryDomain ×ˢ binaryDomain) at composition
  exact composition

theorem jointFamily_contDiffAt_one (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (regularity : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (family (x 0))).val)) :
    ContDiffAt ℝ ⊤ (jointFamily data family) (1, 1) := by
  have membership : (1 : BinaryMatrix) ∈ binaryDomain := by simp [binaryDomain]
  exact ((jointFamily_contDiffOn data family regularity) (1, 1) ⟨membership, membership⟩).contDiffAt
    ((binaryDomain_isOpen.prod binaryDomain_isOpen).mem_nhds ⟨membership, membership⟩)

theorem matrixFamily_contDiffOn (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (regularity : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (family (x 0))).val)) :
    ContDiffOn ℝ ⊤ (matrixFamily data family) binaryDomain := by
  have insertion : ContDiff ℝ ⊤ (fun matrix : BinaryMatrix => ((1 : BinaryMatrix), matrix)) :=
    contDiff_const.prodMk contDiff_id
  have mapsTo : Set.MapsTo (fun matrix : BinaryMatrix => ((1 : BinaryMatrix), matrix))
      binaryDomain (binaryDomain ×ˢ binaryDomain) := by
    intro matrix membership
    exact ⟨by simp [binaryDomain], membership⟩
  have composition := (jointFamily_contDiffOn data family regularity).comp insertion.contDiffOn mapsTo
  simpa only [Function.comp_def, jointFamily, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.realOrbit_one] using composition

theorem matrixFamily_contDiffAt_one (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (regularity : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (family (x 0))).val)) :
    ContDiffAt ℝ ⊤ (matrixFamily data family) 1 := by
  have regularityJoint := (jointFamily_contDiffAt_one data family regularity).comp (1 : BinaryMatrix)
    (contDiffAt_const.prodMk contDiffAt_id)
  simpa only [Function.comp_def, jointFamily, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.realOrbit_one] using regularityJoint

noncomputable def derivative (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (direction : BinaryMatrix) : data.H := fderiv ℝ (matrixFamily data family) 1 direction

theorem derivative_translate (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (regularity : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (family (x 0))).val)) (direction matrix : BinaryMatrix) :
    realOrbit data (derivative data family direction) matrix =
      fderiv ℝ (fun parameter => jointFamily data family (matrix, parameter)) 1 direction := by
  let operator := (unitaryOperator data (atInfinity (invertibleMatrix matrix))).restrictScalars ℝ
  have differentiability := (matrixFamily_contDiffAt_one data family regularity).differentiableAt (by simp)
  have derivativeEquality := (operator.hasFDerivAt.comp 1 differentiability.hasFDerivAt).fderiv
  exact (congrArg (fun linear : BinaryMatrix →L[ℝ] data.H => linear direction) derivativeEquality).symm

theorem derivative_orbit_analytic (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (regularity : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (family (x 0))).val)) (direction : BinaryMatrix) :
    AnalyticAt ℝ (realOrbit data (derivative data family direction)) 1 := by
  have regularityJoint : ContDiffAt ℝ ⊤
      (Function.uncurry (fun matrix parameter => jointFamily data family (matrix, parameter)))
      ((1 : BinaryMatrix), (1 : BinaryMatrix)) := jointFamily_contDiffAt_one data family regularity
  have partialRegularity : ContDiffAt ℝ ⊤
      (fun matrix : BinaryMatrix => fderiv ℝ (fun parameter => jointFamily data family (matrix, parameter)) 1) 1 :=
    regularityJoint.fderiv contDiffAt_const (by simp)
  have evaluated : ContDiffAt ℝ ⊤
      (fun matrix : BinaryMatrix => fderiv ℝ (fun parameter => jointFamily data family (matrix, parameter)) 1 direction) 1 :=
    partialRegularity.clm_apply contDiffAt_const
  have equality : realOrbit data (derivative data family direction) =
      (fun matrix => fderiv ℝ (fun parameter => jointFamily data family (matrix, parameter)) 1 direction) :=
    funext (derivative_translate data family regularity direction)
  rw [equality]
  exact evaluated.analyticAt

theorem derivative_fixed (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (regularity : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (family (x 0))).val))
    (level : Subgroup BinaryFiniteGL) (fixed : ∀ matrix, (family matrix).val ∈ fixedSubspace data level)
    (direction : BinaryMatrix) : derivative data family direction ∈ fixedSubspace data level := by
  intro element
  let operator := (unitaryOperator data (atFinite element.val)).restrictScalars ℝ
  have equality : operator ∘ matrixFamily data family = matrixFamily data family := by
    funext matrix
    exact fixed (invertibleMatrix matrix) element
  have differentiability := (matrixFamily_contDiffAt_one data family regularity).differentiableAt (by simp)
  have derivativeEquality := operator.hasFDerivAt.comp 1 differentiability.hasFDerivAt
  rw [equality] at derivativeEquality
  exact (congrArg (fun linear : BinaryMatrix →L[ℝ] data.H => linear direction) derivativeEquality.fderiv).symm

/-- Differentiating an actual jointly smooth family retains the supplied analytic smooth-vector condition. -/
theorem derivative_mem_smooth (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (regularity : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (family (x 0))).val))
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ matrix, (family matrix).val ∈ fixedSubspace data level) (direction : BinaryMatrix) :
    derivative data family direction ∈ data.smooth :=
  (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.fixed_mem_smooth_iff_analyticAt_one data level openness compactness _
    (derivative_fixed data family regularity level fixed direction)).mpr
      (derivative_orbit_analytic data family regularity direction)

noncomputable def smoothDerivative (data : CuspidalRepresentation) (family : BinaryRealGL → data.smooth)
    (regularity : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (family (x 0))).val))
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ matrix, (family matrix).val ∈ fixedSubspace data level) : BinaryMatrix →ₗ[ℝ] data.smooth where
  toFun direction := ⟨derivative data family direction,
    derivative_mem_smooth data family regularity level openness compactness fixed direction⟩
  map_add' first second := Subtype.ext (map_add (fderiv ℝ (matrixFamily data family) 1) first second)
  map_smul' scalar direction := Subtype.ext (map_smul (fderiv ℝ (matrixFamily data family) 1) scalar direction)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothParameterDerivative
