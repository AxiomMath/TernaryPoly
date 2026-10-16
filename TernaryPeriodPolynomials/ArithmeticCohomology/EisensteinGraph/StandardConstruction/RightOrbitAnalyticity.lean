module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.TaylorBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.PlaneJets

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RightOrbitAnalyticity

open AdelicTaylorBounds SmoothJets

theorem smooth_of_analyticAt_one {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : AdelicGL → E)
    (analytic : ∀ argument, AnalyticAt ℝ (rightMatrix function argument) 1)
    (argument : AdelicGL) :
    Smooth (fun real : Fin 1 → RealGL3 => function (argument * atInfinity (real 0))) := by
  apply (SmoothAnalyticity.smooth_iff_analyticOn _).mpr
  intro matrices membership
  let real : RealGL3 := invertibleMatrix (matrices 0)
  have realValue : real.val = matrices 0 := by
    dsimp [real, invertibleMatrix]
    rw [dite_eq_left (membership 0)]
    rfl
  let linear := TranslatedJets.tupleLeftMulL (fun _ : Fin 1 => real.inv)
  have centered : linear matrices = 1 := by
    funext index
    have indexZero : index = 0 := Subsingleton.elim _ _
    subst index
    change real.inv * matrices 0 = 1
    rw [← realValue]
    exact real.inv_val
  have analytic' : AnalyticAt ℝ (rightMatrix function (argument * atInfinity real)) (linear matrices) := by
    rw [centered]
    exact analytic _
  have composed := analytic'.compContinuousLinearMap
  apply (composed.congr ?_).analyticWithinAt
  filter_upwards [(domain_open 3 1).mem_nhds membership] with other otherMembership
  change function ((argument * atInfinity real) *
    atInfinity (invertibleMatrix (real.inv * other 0))) =
      function (argument * atInfinity (invertibleMatrix (other 0)))
  rw [show real.inv = real⁻¹.val from rfl,
    TranslatedJets.invertibleMatrix_mul_left real⁻¹ (other 0) (otherMembership 0),
    mul_assoc, ← RealTranslations.atInfinity_mul, mul_inv_cancel_left]

def lineBlock (unit : ℝ) (matrix : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![unit, 0, 0; 0, matrix 0 0, matrix 0 1; 0, matrix 1 0, matrix 1 1]

theorem lineBlock_det (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    (lineBlock 1 matrix).det = matrix.det := by
  simp [lineBlock, Matrix.det_fin_three, Matrix.det_fin_two]

theorem invertibleMatrix_lineBlock (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (invertible : matrix.det ≠ 0) :
    invertibleMatrix (lineBlock 1 matrix) = lineLevi 1 (invertibleMatrix matrix) := by
  have blockInvertible : (lineBlock 1 matrix).det ≠ 0 := by rwa [lineBlock_det]
  unfold invertibleMatrix
  rw [dite_eq_left blockInvertible, dite_eq_left invertible]
  apply Units.ext
  simp only [GeneralLinearGroup.val_mkOfDetNeZero, lineLevi_val]
  rfl

theorem left_line_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : AdelicGL → E)
    (smooth : ∀ argument, Smooth (fun real : Fin 1 → RealGL3 =>
      function (argument * atInfinity (real 0))))
    (invariant : ∀ level : finiteLevel, ∀ argument,
      function (argument * atFinite level.val) = function argument)
    (argument : AdelicGL) :
    Smooth (fun real : Fin 1 → BinaryRealGL => function (atInfinity (lineLevi 1 (real 0)) * argument)) := by
  let transform : MatrixTuples 2 1 → Matrices := fun matrices _ =>
    lineBlock 1 (matrices 0) * (realGroup argument).val
  have transformSmooth : ContDiff ℝ ⊤ transform := by
    apply contDiff_pi.mpr
    intro index
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    fin_cases row <;> fin_cases column <;>
      simp [transform, lineBlock, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;>
      fun_prop
  have maps : Set.MapsTo transform (domain 2 1) (domain 3 1) := by
    intro matrices membership index
    change (lineBlock 1 (matrices 0) * (realGroup argument).val).det ≠ 0
    rw [Matrix.det_mul, lineBlock_det]
    exact mul_ne_zero (membership 0) (GeneralLinearGroup.det_ne_zero _)
  have transformed := (smooth (atFinite (finiteGroup argument))).comp transformSmooth.contDiffOn maps
  apply transformed.congr
  intro matrices membership
  change function (atInfinity (lineLevi 1 (invertibleMatrix (matrices 0))) * argument) =
    function (atFinite (finiteGroup argument) * atInfinity
      (invertibleMatrix (lineBlock 1 (matrices 0) * (realGroup argument).val)))
  rw [SmoothTranslations.invertibleMatrix_mul_right _ (by simpa only [lineBlock_det] using membership 0) _,
    invertibleMatrix_lineBlock _ (membership 0)]
  exact AdelicPlaneJets.finite_local_formula function invariant (finiteGroup argument) argument (by simp) _

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RightOrbitAnalyticity
