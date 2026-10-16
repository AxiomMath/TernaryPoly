module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CohomologicalCenter
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth

abbrev BinaryMatrix := Matrix (Fin 2) (Fin 2) ℝ
abbrev PlaneMatrix := Matrix (Fin 3) (Fin 3) ℝ
abbrev JointMatrix := BinaryMatrix × PlaneMatrix

def jointDomain : Set JointMatrix := {matrices | matrices.1.det ≠ 0 ∧ matrices.2.det ≠ 0}

theorem jointDomain_isOpen : IsOpen jointDomain :=
  (isOpen_ne.preimage continuous_fst.matrix_det).inter
    (isOpen_ne.preimage continuous_snd.matrix_det)

theorem invertibleMatrix_val {size : ℕ} (matrix : Matrix (Fin size) (Fin size) ℝ)
    (invertibility : matrix.det ≠ 0) : (invertibleMatrix matrix).val = matrix := by
  simp only [invertibleMatrix, dite_eq_left invertibility]
  rfl

theorem invertibleMatrix_units {size : ℕ} (matrix : Matrix.GeneralLinearGroup (Fin size) ℝ) :
    invertibleMatrix matrix.val = matrix := by
  apply Units.ext
  exact invertibleMatrix_val matrix.val (Matrix.GeneralLinearGroup.det_ne_zero matrix)

theorem planeBlock_det (matrix : BinaryMatrix) : (planeBlock matrix 1).det = matrix.det := by
  simp [planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]

def blockProduct (matrices : JointMatrix) : Fin 1 → PlaneMatrix :=
  fun _ => planeBlock matrices.1 1 * matrices.2

theorem blockProduct_contDiff : ContDiff ℝ ⊤ blockProduct := by
  apply contDiff_pi.mpr
  intro index
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;>
    simp [blockProduct, Matrix.mul_apply, Fin.sum_univ_three, planeBlock] <;> fun_prop

theorem blockProduct_mapsTo : Set.MapsTo blockProduct jointDomain (matrixDomain 3 1) := by
  intro matrices membership index
  change (planeBlock matrices.1 1 * matrices.2).det ≠ 0
  rw [Matrix.det_mul, planeBlock_det]
  exact mul_ne_zero membership.1 membership.2

theorem determinant_contDiff : ContDiff ℝ ⊤ (fun matrices : JointMatrix => matrices.1.det) := by
  simp only [Matrix.det_fin_two]
  fun_prop

noncomputable def normalization (exponent : ℂ) (matrices : JointMatrix) : ℂ :=
  Complex.exp (exponent * (Real.log |matrices.1.det| : ℂ))

theorem normalization_contDiffOn (exponent : ℂ) :
    ContDiffOn ℝ ⊤ (normalization exponent) jointDomain := by
  have smoothLog : ContDiffOn ℝ ⊤ (fun matrices : JointMatrix => Real.log |matrices.1.det|)
      jointDomain :=
    by
      simp only [Real.log_abs]
      exact determinant_contDiff.contDiffOn.log (fun _ membership => membership.1)
  exact Complex.contDiff_exp.comp_contDiffOn
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn smoothLog))

noncomputable def jointModel {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : FiniteGL) (matrices : JointMatrix) : data.cusp.H :=
  normalization (-binaryInductionExponent degree .plane parameter) matrices •
    matrixLift (fun realMatrices : Fin 1 → RealGL3 =>
      (planeCuspVector inducedSection (atFinite finiteMatrix * atInfinity (realMatrices 0))).val)
      (blockProduct matrices)

theorem jointModel_contDiffOn {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (finiteMatrix : FiniteGL) :
    ContDiffOn ℝ ⊤ (jointModel inducedSection finiteMatrix) jointDomain := by
  have smoothVector := planeCuspVector_smooth inducedSection (atFinite finiteMatrix)
  exact (normalization_contDiffOn _).smul
    (smoothVector.comp blockProduct_contDiff.contDiffOn blockProduct_mapsTo)

theorem planeLevi_atInfinity (matrix : BinaryRealGL) :
    planeLevi (atInfinity matrix) 1 = atInfinity (planeLevi matrix 1) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, atInfinity, combineGL, pairMatrix] <;> rfl

theorem jointModel_at_units {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : FiniteGL) (binaryMatrix : BinaryRealGL) (realMatrix : RealGL3) :
    jointModel inducedSection finiteMatrix (binaryMatrix.val, realMatrix.val) =
      data.cusp.π (atInfinity binaryMatrix)
        (planeCuspVector inducedSection (atFinite finiteMatrix * atInfinity realMatrix)).val := by
  have productEquality : blockProduct (binaryMatrix.val, realMatrix.val) =
      fun _ => (planeLevi binaryMatrix 1 * realMatrix).val := rfl
  unfold jointModel
  rw [productEquality, matrixLift_at_units]
  have matrixEquality :
      atFinite finiteMatrix * atInfinity (planeLevi binaryMatrix 1 * realMatrix) =
      planeLevi (atInfinity binaryMatrix) 1 * (atFinite finiteMatrix * atInfinity realMatrix) := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, ← planeLevi_atInfinity, ← mul_assoc,
      planeLevi_atInfinity, TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, mul_assoc]
  rw [matrixEquality, planeCuspVector_binaryLevi]
  change normalization (-binaryInductionExponent degree .plane parameter)
      (binaryMatrix.val, realMatrix.val) •
    (normPower (Matrix.GeneralLinearGroup.det (atInfinity binaryMatrix))
      (binaryInductionExponent degree .plane parameter) • _) = _
  have normalizationEquality : normalization (-binaryInductionExponent degree .plane parameter)
      (binaryMatrix.val, realMatrix.val) =
      normPower (Matrix.GeneralLinearGroup.det (atInfinity binaryMatrix))
        (-binaryInductionExponent degree .plane parameter) := by
    rw [normPower, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity]
    rfl
  rw [normalizationEquality, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_neg,
    inv_smul_smul₀ (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_ne_zero _ _)]

theorem jointModel_eq_orbit {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : FiniteGL) (matrices : JointMatrix) (membership : matrices ∈ jointDomain) :
    jointModel inducedSection finiteMatrix matrices =
      data.cusp.π (atInfinity (invertibleMatrix matrices.1))
        (planeCuspVector inducedSection (atFinite finiteMatrix *
          atInfinity (invertibleMatrix matrices.2))).val := by
  have equality := jointModel_at_units inducedSection finiteMatrix
    (invertibleMatrix matrices.1) (invertibleMatrix matrices.2)
  simpa only [invertibleMatrix_val _ membership.1, invertibleMatrix_val _ membership.2,
    Prod.mk.eta] using equality

noncomputable def jointOrbit {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : FiniteGL) (matrices : JointMatrix) : data.cusp.H :=
  data.cusp.π (atInfinity (invertibleMatrix matrices.1))
    (planeCuspVector inducedSection (atFinite finiteMatrix *
      atInfinity (invertibleMatrix matrices.2))).val

theorem jointOrbit_contDiffOn {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (finiteMatrix : FiniteGL) :
    ContDiffOn ℝ ⊤ (jointOrbit inducedSection finiteMatrix) jointDomain := by
  apply (jointModel_contDiffOn inducedSection finiteMatrix).congr
  intro matrices membership
  exact (jointModel_eq_orbit inducedSection finiteMatrix matrices membership).symm

theorem iteratedFDeriv_comp_linear_at {Source Middle Target : Type}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Middle] [NormedSpace ℝ Middle]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (linear : Source →L[ℝ] Middle) (function : Middle → Target) (point : Source)
    (smoothFunction : ContDiffAt ℝ ⊤ function (linear point)) (order : ℕ) :
    iteratedFDeriv ℝ order (function ∘ linear) point =
      (iteratedFDeriv ℝ order function (linear point)).compContinuousLinearMap (fun _ => linear) := by
  obtain ⟨neighborhood, neighborhoodProperty, smoothOn⟩ :=
    smoothFunction.contDiffOn (m := order) le_top (by simp)
  obtain ⟨openSet, subset, openness, membership⟩ := mem_nhds_iff.mp neighborhoodProperty
  have smoothOpen := smoothOn.mono subset
  have openPreimage : IsOpen (linear ⁻¹' openSet) := openness.preimage linear.continuous
  have formula := linear.iteratedFDerivWithin_comp_right smoothOpen openness.uniqueDiffOn
    openPreimage.uniqueDiffOn membership (i := order) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv openPreimage.uniqueDiffOn
      ((smoothFunction.of_le le_top).comp point linear.contDiff.contDiffAt) membership,
    iteratedFDerivWithin_eq_iteratedFDeriv openness.uniqueDiffOn
      (smoothFunction.of_le le_top) membership] at formula
  exact formula

theorem iteratedFDeriv_comp_affine_at {Source Middle Target : Type}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Middle] [NormedSpace ℝ Middle]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (linear : Source →L[ℝ] Middle) (offset : Middle) (function : Middle → Target) (point : Source)
    (smoothFunction : ContDiffAt ℝ ⊤ function (linear point + offset)) (order : ℕ) :
    iteratedFDeriv ℝ order (fun value => function (linear value + offset)) point =
      (iteratedFDeriv ℝ order function (linear point + offset)).compContinuousLinearMap
        (fun _ => linear) := by
  have smoothTranslated : ContDiffAt ℝ ⊤ (fun value => function (value + offset)) (linear point) :=
    smoothFunction.comp (linear point) (contDiff_id.add contDiff_const).contDiffAt
  have formula := iteratedFDeriv_comp_linear_at linear (fun value => function (value + offset))
    point smoothTranslated order
  rw [iteratedFDeriv_comp_add_right] at formula
  exact formula

noncomputable instance binaryMultilinearNorm {order : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) Target) :=
  ContinuousMultilinearMap.normedAddCommGroup

noncomputable instance jointMultilinearNorm {order : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin order => JointMatrix) Target) :=
  ContinuousMultilinearMap.normedAddCommGroup

noncomputable def orbitDerivative (data : CuspidalRepresentation) (order : ℕ) (vector : data.H) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H :=
  iteratedFDeriv ℝ order
    (fun matrix : BinaryMatrix => data.π (atInfinity (invertibleMatrix matrix)) vector) 1

theorem jointOrbit_derivative_continuousOn {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : FiniteGL) (order : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ order (jointOrbit inducedSection finiteMatrix)) jointDomain := by
  intro matrices membership
  have smoothAt := (jointOrbit_contDiffOn inducedSection finiteMatrix matrices membership).contDiffAt
    (jointDomain_isOpen.mem_nhds membership)
  exact (smoothAt.iteratedFDeriv_right (m := 0) (by simp)).continuousAt.continuousWithinAt

theorem orbitDerivative_eq_joint {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : FiniteGL) (realMatrix : RealGL3) (order : ℕ) :
    orbitDerivative data.cusp order
      (planeCuspVector inducedSection (atFinite finiteMatrix * atInfinity realMatrix)).val =
      (iteratedFDeriv ℝ order (jointOrbit inducedSection finiteMatrix) (1, realMatrix.val)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ BinaryMatrix PlaneMatrix) := by
  have membership : (1, realMatrix.val) ∈ jointDomain :=
    ⟨by simp, Matrix.GeneralLinearGroup.det_ne_zero realMatrix⟩
  have smoothAt := (jointOrbit_contDiffOn inducedSection finiteMatrix _ membership).contDiffAt
    (jointDomain_isOpen.mem_nhds membership)
  let inclusion : BinaryMatrix →L[ℝ] JointMatrix := ContinuousLinearMap.inl ℝ BinaryMatrix PlaneMatrix
  have insertEquality (value : BinaryMatrix) :
      inclusion value + (0, realMatrix.val) =
      (value, realMatrix.val) := by
    change (value + 0, 0 + realMatrix.val) = _
    rw [add_zero, zero_add]
  have formula := iteratedFDeriv_comp_affine_at inclusion
    (0, realMatrix.val) (jointOrbit inducedSection finiteMatrix) 1 (by
      exact (congrArg (fun point : JointMatrix =>
        ContDiffAt ℝ ⊤ (jointOrbit inducedSection finiteMatrix) point) (insertEquality 1)).mpr smoothAt) order
  have leftEquality :
      (fun value : BinaryMatrix => jointOrbit inducedSection finiteMatrix
        (inclusion value + (0, realMatrix.val))) =
      fun value => data.cusp.π (atInfinity (invertibleMatrix value))
        (planeCuspVector inducedSection (atFinite finiteMatrix * atInfinity realMatrix)).val := by
    funext value
    calc
      _ = jointOrbit inducedSection finiteMatrix (value, realMatrix.val) :=
        congrArg (jointOrbit inducedSection finiteMatrix) (insertEquality value)
      _ = _ := by simp only [jointOrbit, invertibleMatrix_units]
  have rightEquality := congrArg (fun point : JointMatrix =>
    (iteratedFDeriv ℝ order (jointOrbit inducedSection finiteMatrix) point).compContinuousLinearMap
      (fun _ => inclusion)) (insertEquality 1)
  exact (congrArg (fun function : BinaryMatrix → data.cusp.H => iteratedFDeriv ℝ order function 1)
    leftEquality).symm.trans (formula.trans rightEquality)

theorem orbitDerivative_cuspVector_continuous {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : FiniteGL) (order : ℕ) :
    Continuous (fun realMatrix : RealGL3 => orbitDerivative data.cusp order
      (planeCuspVector inducedSection (atFinite finiteMatrix * atInfinity realMatrix)).val) := by
  have continuousPair : Continuous (fun realMatrix : RealGL3 => ((1 : BinaryMatrix), realMatrix.val)) :=
    continuous_const.prodMk Units.continuous_val
  have continuousJoint := (jointOrbit_derivative_continuousOn inducedSection finiteMatrix order).comp_continuous
      continuousPair
      (fun realMatrix => ⟨by simp, Matrix.GeneralLinearGroup.det_ne_zero realMatrix⟩)
  let restrict :
      ContinuousMultilinearMap ℝ (fun _ : Fin order => JointMatrix) data.cusp.H →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.cusp.H :=
    ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => ContinuousLinearMap.inl ℝ BinaryMatrix PlaneMatrix)
  have equality : (fun realMatrix : RealGL3 => orbitDerivative data.cusp order
      (planeCuspVector inducedSection (atFinite finiteMatrix * atInfinity realMatrix)).val) =
      fun realMatrix => restrict
        (iteratedFDeriv ℝ order (jointOrbit inducedSection finiteMatrix) (1, realMatrix.val)) := by
    funext realMatrix
    exact orbitDerivative_eq_joint inducedSection finiteMatrix realMatrix order
  rw [equality]
  exact restrict.continuous.comp continuousJoint

theorem orbitDerivative_cuspVector_bound_on_compact {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : FiniteGL) (order : ℕ)
    {compactSet : Set RealGL3} (compactness : IsCompact compactSet) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ realMatrix ∈ compactSet,
      ‖orbitDerivative data.cusp order
        (planeCuspVector inducedSection (atFinite finiteMatrix * atInfinity realMatrix)).val‖ ≤ bound := by
  obtain ⟨bound, boundProperty⟩ := compactness.exists_bound_of_continuousOn
    (orbitDerivative_cuspVector_continuous inducedSection finiteMatrix order).continuousOn
  exact ⟨max 0 bound, le_max_left _ _, fun realMatrix membership =>
    (boundProperty realMatrix membership).trans (le_max_right _ _)⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
