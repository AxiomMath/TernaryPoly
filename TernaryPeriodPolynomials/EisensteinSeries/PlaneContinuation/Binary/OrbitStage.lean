module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.StageLift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages TernaryPeriodPolynomials.PlaneEisensteinContinuation.LocalAnalyticFamilies
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitStage

def block (matrix : PlaneMatrix) : BinaryMatrix :=
  fun row column => matrix row.castSucc column.castSucc

theorem block_contDiff : ContDiff ℝ ⊤ block := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  exact contDiff_apply_apply ℝ ℝ row.castSucc column.castSucc

theorem invertibleMatrix_mul (first second : BinaryMatrix) (firstNonzero : first.det ≠ 0)
    (secondNonzero : second.det ≠ 0) :
    invertibleMatrix (first * second) = invertibleMatrix first * invertibleMatrix second := by
  apply Units.ext
  rw [invertibleMatrix_val _ (by rw [Matrix.det_mul]; exact mul_ne_zero firstNonzero secondNonzero), Units.val_mul,
    invertibleMatrix_val _ firstNonzero, invertibleMatrix_val _ secondNonzero]

def family (data : CuspidalRepresentation) (vector : data.smooth) (matrix : PlaneMatrix) : data.H :=
  realOrbit data vector.val (block matrix)

theorem family_fixed (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence) (matrix : PlaneMatrix) :
    family data vector matrix ∈ fixedSubspace data finiteCongruence :=
  fixedSubspace_real_stable data finiteCongruence (invertibleMatrix (block matrix)) vector.val fixed

theorem joint_eq (data : CuspidalRepresentation) (vector : data.smooth) (pair : JointMatrix)
    (firstNonzero : pair.1.det ≠ 0) (secondNonzero : (block pair.2).det ≠ 0) :
    familyOrbit data (family data vector) pair = realOrbit data vector.val (pair.1 * block pair.2) := by
  unfold familyOrbit family realOrbit
  rw [invertibleMatrix_mul _ _ firstNonzero secondNonzero, Height.atInfinity_mul, map_mul, Module.End.mul_apply]

theorem joint_analyticAt (data : CuspidalRepresentation) (vector : data.smooth)
    (center : PlaneMatrix) (nonzero : (block center).det ≠ 0) :
    AnalyticAt ℝ (familyOrbit data (family data vector)) (1, center) := by
  have orbitSmooth : ContDiffAt ℝ ⊤ (realOrbit data vector.val) (block center) :=
    (smooth_orbit_contDiffOn data vector).contDiffAt (binaryDomain_isOpen.mem_nhds nonzero)
  have productSmooth : ContDiff ℝ ⊤ (fun pair : JointMatrix => pair.1 * block pair.2) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, block] <;> fun_prop
  have composition : AnalyticAt ℝ (fun pair : JointMatrix => realOrbit data vector.val (pair.1 * block pair.2)) (1, center) := by
    exact AnalyticAt.comp (f := fun pair : JointMatrix => pair.1 * block pair.2)
      (g := realOrbit data vector.val) (x := (1, center))
      (show AnalyticAt ℝ (realOrbit data vector.val) ((1 : BinaryMatrix) * block center) by
        simpa only [one_mul] using orbitSmooth.analyticAt)
        (productSmooth.contDiffAt (x := (1, center))).analyticAt
  have neighborhood : {pair : JointMatrix | pair.1.det ≠ 0 ∧ (block pair.2).det ≠ 0} ∈ nhds (1, center) :=
    ((isOpen_ne.preimage continuous_fst.matrix_det).inter
      (isOpen_ne.preimage (block_contDiff.continuous.comp continuous_snd).matrix_det)).mem_nhds ⟨by simp, nonzero⟩
  apply composition.congr
  filter_upwards [neighborhood] with pair membership
  exact (joint_eq data vector pair membership.1 membership.2).symm

theorem exists_lift (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence)
    (center : PlaneMatrix) (nonzero : (block center).det ≠ 0) :
    ∃ shiftRadius : ℝ≥0, 0 < shiftRadius ∧ ∃ radius : ℝ≥0, ∃ positive : 0 < radius,
      ∃ lift : PlaneMatrix → analyticStage data finiteCongruence radius positive,
        AnalyticOnNhd ℝ lift (Metric.eball 0 (shiftRadius : ENNReal)) ∧
        ∀ offset ∈ Metric.eball 0 (shiftRadius : ENNReal),
          stageHilbertMap data finiteCongruence radius positive (lift offset) = family data vector (center + offset) := by
  obtain ⟨series, expansionRadius, expansion⟩ := joint_analyticAt data vector center nonzero
  obtain ⟨radius, positiveRadius, radiusBound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp expansion.r_pos
  have positiveReal : (0 : ℝ≥0) < radius := by exact_mod_cast positiveRadius
  have halfPositive : (0 : ℝ≥0) < radius / 2 := div_pos positiveReal (by norm_num)
  have halfBound : ((radius / 2 : ℝ≥0) : ENNReal) + ((radius / 2 : ℝ≥0) : ENNReal) < expansionRadius := by
    rw [← ENNReal.coe_add, add_halves]
    exact radiusBound
  have fixedFamily (offset : ParameterBall (radius / 2)) :
      family data vector (center + offset.val) ∈ fixedSubspace data finiteCongruence :=
    family_fixed data vector fixed _
  let lift := AnalyticStageFamilies.stageFamily data finiteCongruence (family data vector) center series expansionRadius expansion
    (radius / 2) (radius / 2) halfPositive halfBound fixedFamily
  refine ⟨radius / 2, halfPositive, radius / 2, halfPositive, lift, ?_, ?_⟩
  · exact AnalyticStageFamilies.stageFamily_analyticOnNhd data finiteCongruence (family data vector) center
      series expansionRadius expansion (radius / 2) (radius / 2) halfPositive halfPositive halfBound fixedFamily
  · intro offset membership
    have bound : ‖offset‖₊ ≤ radius / 2 := by
      have strict : ‖offset‖₊ < radius / 2 := by
        simpa only [Metric.mem_eball, edist_lt_coe, nndist_zero_right] using membership
      exact strict.le
    exact congrArg Prod.fst (AnalyticStageFamilies.stageFamily_val data finiteCongruence (family data vector) center
      series expansionRadius expansion (radius / 2) (radius / 2) halfPositive halfBound fixedFamily offset bound)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitStage
