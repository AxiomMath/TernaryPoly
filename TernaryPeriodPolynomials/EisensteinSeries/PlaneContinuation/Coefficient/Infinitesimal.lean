module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.DifferentiatedCohomology

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CocycleDifferential TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientSmoothAction TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCocycle
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal

noncomputable def multiplier (degree : ℕ) (matrix : BinaryMatrix) (index other : Index (degree + 1)) : ℂ :=
  normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix matrix))) (((degree : ℂ) + 3) / 2) *
    (binaryCoefficient degree (invertibleMatrix matrix) (basisMonomial other)).val.coeff index.val

theorem multiplier_one (degree : ℕ) (index other : Index (degree + 1)) :
    multiplier degree 1 index other = if other = index then 1 else 0 := by
  classical
  have matrixOne : invertibleMatrix (1 : BinaryMatrix) = (1 : BinaryRealGL) := invertibleMatrix_units 1
  simp only [multiplier, matrixOne, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, map_one,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_one, binaryCoefficient_one, Module.End.one_apply, one_mul,
    basisMonomial, MvPolynomial.coeff_monomial, Subtype.val_inj]

noncomputable def coefficientDerivative (degree : ℕ) (direction : BinaryMatrix) (index other : Index (degree + 1)) : ℂ :=
  fderiv ℝ (fun matrix => multiplier degree matrix index other) 1 direction

theorem hilbertAction_coordinate (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (index : Index (degree + 1)) (matrix : BinaryMatrix) :
    hilbertAction data degree (invertibleMatrix matrix) (fun other => (vectors other).val) index =
      ∑ other : Index (degree + 1), multiplier degree matrix index other • realOrbit data (vectors other).val matrix := by
  rw [hilbertAction_apply, Finset.smul_sum]
  simp only [multiplier, mul_smul, realOrbit]

theorem infinitesimalAction_coordinate (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (direction : BinaryMatrix) (index : Index (degree + 1)) :
    infinitesimalAction data degree direction (fun other => (vectors other).val) index =
      (directionalOperator data direction (vectors index)).val +
        ∑ other : Index (degree + 1), coefficientDerivative degree direction index other • (vectors other).val := by
  classical
  have globalDerivative := ((coefficient_orbit_contDiffAt_one data degree vectors).differentiableAt (by simp)).hasFDerivAt
  have componentDerivative := (ContinuousLinearMap.proj index).hasFDerivAt.comp 1 globalDerivative
  have termDerivative (other : Index (degree + 1)) : HasFDerivAt
      (fun matrix : BinaryMatrix => multiplier degree matrix index other • realOrbit data (vectors other).val matrix)
      (multiplier degree 1 index other • fderiv ℝ (realOrbit data (vectors other).val) 1 +
        (fderiv ℝ (fun matrix => multiplier degree matrix index other) 1).smulRight (realOrbit data (vectors other).val 1)) 1 :=
    (((BinaryCoefficientRegularity.multiplier_contDiffAt degree index other 1 (by simp)).differentiableAt (by simp)).hasFDerivAt).smul
      (((smooth_orbit_contDiffAt_one data (vectors other)).differentiableAt (by simp)).hasFDerivAt)
  have sumDerivative := HasFDerivAt.sum (fun other (_ : other ∈ Finset.univ) => termDerivative other)
  have functionEquality : (fun matrix : BinaryMatrix =>
      hilbertAction data degree (invertibleMatrix matrix) (fun other => (vectors other).val) index) =
      ∑ other : Index (degree + 1), (fun matrix : BinaryMatrix =>
        multiplier degree matrix index other • realOrbit data (vectors other).val matrix) := by
    funext matrix
    simp only [Finset.sum_apply, hilbertAction_coordinate]
  change HasFDerivAt (fun matrix : BinaryMatrix =>
      hilbertAction data degree (invertibleMatrix matrix) (fun other => (vectors other).val) index)
      ((ContinuousLinearMap.proj index).comp (fderiv ℝ
        (fun matrix : BinaryMatrix => hilbertAction data degree (invertibleMatrix matrix)
          (fun other => (vectors other).val)) 1)) 1 at componentDerivative
  rw [functionEquality] at componentDerivative
  have equality := componentDerivative.unique sumDerivative
  have evaluated := congrArg (fun linear : BinaryMatrix →L[ℝ] data.H => linear direction) equality
  change infinitesimalAction data degree direction (fun other => (vectors other).val) index =
    (∑ other : Index (degree + 1), (multiplier degree 1 index other • fderiv ℝ (realOrbit data (vectors other).val) 1 +
      (fderiv ℝ (fun matrix => multiplier degree matrix index other) 1).smulRight (realOrbit data (vectors other).val 1))) direction at evaluated
  simp only [sum_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.realOrbit_one, multiplier_one, Finset.sum_add_distrib, ite_smul,
    one_smul, zero_smul] at evaluated
  simp only [DFunLike.ite_apply, zero_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at evaluated
  exact evaluated

noncomputable def operator (data : CuspidalRepresentation) (degree : ℕ) (direction : BinaryMatrix) :
    Module.End ℂ (Vectors data degree) where
  toFun vectors index := directionalOperator data direction (vectors index) +
    ∑ other : Index (degree + 1), coefficientDerivative degree direction index other • vectors other
  map_add' first second := by
    funext index
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' scalar vectors := by
    funext index
    simp only [Pi.smul_apply, map_smul, smul_add, Finset.smul_sum, RingHom.id_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro other _
    exact smul_comm _ scalar _

theorem operator_val (data : CuspidalRepresentation) (degree : ℕ) (direction : BinaryMatrix)
    (vectors : Vectors data degree) :
    (fun index => (operator data degree direction vectors index).val) =
      infinitesimalAction data degree direction (fun index => (vectors index).val) := by
  funext index
  rw [infinitesimalAction_coordinate]
  change (directionalOperator data direction (vectors index) +
    ∑ other : Index (degree + 1), coefficientDerivative degree direction index other • vectors other).val = _
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]

theorem operator_add (data : CuspidalRepresentation) (degree : ℕ) (first second : BinaryMatrix) :
    operator data degree (first + second) = operator data degree first + operator data degree second := by
  apply LinearMap.ext
  intro vectors
  funext index
  apply Subtype.ext
  have equality := congrFun (operator_val data degree (first + second) vectors) index
  rw [LieCocycle.infinitesimalAction, map_add] at equality
  exact equality.trans (congrArg₂ (· + ·)
    (congrFun (operator_val data degree first vectors) index).symm
    (congrFun (operator_val data degree second vectors) index).symm)

theorem operator_real_smul (data : CuspidalRepresentation) (degree : ℕ) (scalar : ℝ) (direction : BinaryMatrix) :
    operator data degree (scalar • direction) = (scalar : ℂ) • operator data degree direction := by
  apply LinearMap.ext
  intro vectors
  funext index
  apply Subtype.ext
  have equality := congrFun (operator_val data degree (scalar • direction) vectors) index
  rw [LieCocycle.infinitesimalAction, map_smul] at equality
  exact equality.trans (congrArg (fun vector : data.H => scalar • vector)
    (congrFun (operator_val data degree direction vectors) index).symm)

theorem operator_preserves_fixed (data : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL) (direction : BinaryMatrix) (vectors : Vectors data degree)
    (fixed : ∀ index, (vectors index).val ∈ fixedSubspace data level) (index : Index (degree + 1)) :
    (operator data degree direction vectors index).val ∈ fixedSubspace data level := by
  change (directionalOperator data direction (vectors index) +
    ∑ other : Index (degree + 1), coefficientDerivative degree direction index other • vectors other).val ∈ _
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]
  exact (fixedSubspace data level).add_mem
    (directionalOperator_preserves_fixed data level direction (vectors index) (fixed index))
    ((fixedSubspace data level).sum_mem (fun other _ =>
      (fixedSubspace data level).smul_mem _ (fixed other)))

noncomputable def smoothDifferential (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →L[ℝ] HilbertVectors data degree)
    (regularity : ∀ direction index, differential direction index ∈ data.smooth) :
    BinaryMatrix →ₗ[ℝ] Vectors data degree where
  toFun direction index := ⟨differential direction index, regularity direction index⟩
  map_add' first second := by
    funext index
    apply Subtype.ext
    exact congrFun (map_add differential first second) index
  map_smul' scalar direction := by
    funext index
    apply Subtype.ext
    exact congrFun (map_smul differential scalar direction) index

/-- The nontrivial differentiated class is valued in the supplied smooth module itself. -/
theorem exists_nontrivial_smooth_cocycle {degree : ℕ} (data : InducingData degree) :
    ∃ differential : BinaryMatrix →ₗ[ℝ] Vectors data.cusp degree,
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ ∀ direction index,
          (differential direction index).val ∈ fixedSubspace data.cusp level) ∧
      (∀ first second, operator data.cusp degree first (differential second) -
        operator data.cusp degree second (differential first) = differential (first * second - second * first)) ∧
      ¬ ∃ vectors : Vectors data.cusp degree, ∀ direction,
        differential direction = operator data.cusp degree direction vectors := by
  obtain ⟨differential, regularity, fixed, equation, nontrivialClass⟩ :=
    DifferentiatedCohomology.exists_nontrivial_differential data
  refine ⟨smoothDifferential data.cusp degree differential regularity, fixed, ?_, ?_⟩
  · intro first second
    funext index
    apply Subtype.ext
    have firstValue := congrFun (operator_val data.cusp degree first
      (smoothDifferential data.cusp degree differential regularity second)) index
    have secondValue := congrFun (operator_val data.cusp degree second
      (smoothDifferential data.cusp degree differential regularity first)) index
    exact (congrArg₂ (· - ·) firstValue secondValue).trans (congrFun (equation first second) index)
  · rintro ⟨vectors, primitive⟩
    apply nontrivialClass
    refine ⟨vectors, fun direction => ?_⟩
    exact (congrArg (fun tuple : Vectors data.cusp degree => fun index => (tuple index).val)
      (primitive direction)).trans (operator_val data.cusp degree direction vectors)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal
