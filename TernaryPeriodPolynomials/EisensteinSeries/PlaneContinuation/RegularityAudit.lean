module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.OrbitTranslation
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RegularityAudit

/-- The pinned definition of `Smooth` requires real analyticity. -/
theorem smooth_iff_analyticOn {size count : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target) :
    Smooth function ↔ AnalyticOn ℝ
      (fun matrices : Fin count → Matrix (Fin size) (Fin size) ℝ =>
        function (fun index => invertibleMatrix (matrices index)))
      (matrixDomain size count) :=
  contDiffOn_omega_iff_analyticOn (matrixDomain_isOpen size count).uniqueDiffOn

theorem smooth_implies_cInfinity {size count : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target}
    (regularity : Smooth function) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun matrices : Fin count → Matrix (Fin size) (Fin size) ℝ =>
        function (fun index => invertibleMatrix (matrices index)))
      (matrixDomain size count) := regularity.of_le le_top

noncomputable def scalarBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

theorem scalarBump_cInfinity : ContDiff ℝ (↑(⊤ : ℕ∞)) (scalarBump : ℝ → ℝ) :=
  scalarBump.contDiff

theorem scalarBump_not_analytic : ¬ AnalyticOnNhd ℝ (scalarBump : ℝ → ℝ) Set.univ := by
  intro analytic
  have locallyOne : (scalarBump : ℝ → ℝ) =ᶠ[nhds (0 : ℝ)] (fun _ => 1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 by norm_num)] with x membership
    exact scalarBump.one_of_mem_closedBall (Metric.ball_subset_closedBall membership)
  have globallyOne := analytic.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const isPreconnected_univ (Set.mem_univ (0 : ℝ)) locallyOne
  have zeroValue : scalarBump (3 : ℝ) = 0 :=
    scalarBump.zero_of_le_dist (by norm_num [scalarBump, Real.dist_eq])
  have oneValue := globallyOne (Set.mem_univ (3 : ℝ))
  rw [zeroValue] at oneValue
  exact zero_ne_one oneValue

noncomputable def groupBump (matrices : Fin 1 → BinaryRealGL) : ℝ :=
  scalarBump ((matrices 0).val 0 1)

theorem groupBump_matrix_lift (matrices : Fin 1 → BinaryMatrix)
    (membership : matrices ∈ matrixDomain 2 1) :
    groupBump (fun index => invertibleMatrix (matrices index)) =
      scalarBump (matrices 0 0 1) := by
  unfold groupBump
  rw [invertibleMatrix_val _ (membership 0)]

theorem groupBump_cInfinity :
    ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun matrices : Fin 1 → BinaryMatrix =>
        groupBump (fun index => invertibleMatrix (matrices index)))
      (matrixDomain 2 1) := by
  have entrySmooth : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun matrices : Fin 1 → BinaryMatrix => matrices 0 0 1) := by
    fun_prop
  exact (scalarBump_cInfinity.comp entrySmooth).contDiffOn.congr
    (fun matrices membership => groupBump_matrix_lift matrices membership)

theorem groupBump_not_smooth : ¬ Smooth groupBump := by
  intro regularity
  let line : ℝ → (Fin 1 → BinaryMatrix) := fun x _ => !![1, x; 0, 1]
  have lineSmooth : ContDiff ℝ ⊤ line := by
    apply contDiff_pi.mpr
    intro index
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    fin_cases row <;> fin_cases column <;> simp [line] <;> fun_prop
  have lineMaps : Set.MapsTo line Set.univ (matrixDomain 2 1) := by
    intro x _ index
    simp [line, Matrix.det_fin_two]
  have composite := regularity.comp lineSmooth.contDiffOn lineMaps
  have equality : (fun x : ℝ => groupBump (fun index => invertibleMatrix (line x index))) =
      (scalarBump : ℝ → ℝ) := by
    funext x
    rw [groupBump_matrix_lift _ (lineMaps (Set.mem_univ x))]
    rfl
  have bumpSmooth : ContDiff ℝ ⊤ (scalarBump : ℝ → ℝ) :=
    contDiffOn_univ.mp (equality ▸ composite)
  exact scalarBump_not_analytic (fun x _ => bumpSmooth.contDiffAt.analyticAt)

/-- A genuine C-infinity function on the same real matrix group fails `Smooth`. -/
theorem exists_cInfinity_not_smooth :
    ∃ function : (Fin 1 → BinaryRealGL) → ℝ,
      ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (fun matrices : Fin 1 → BinaryMatrix =>
          function (fun index => invertibleMatrix (matrices index)))
        (matrixDomain 2 1) ∧ ¬ Smooth function :=
  ⟨groupBump, groupBump_cInfinity, groupBump_not_smooth⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RegularityAudit
