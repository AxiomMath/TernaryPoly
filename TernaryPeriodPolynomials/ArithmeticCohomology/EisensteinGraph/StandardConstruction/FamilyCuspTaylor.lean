module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.FamilyTaylor
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FamilyCuspLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.TaylorBounds

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FamilyCuspTaylor

open CompactTaylorBounds CuspTaylorBounds

def matrixOrbit {degree arity : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data side parameter (function vertices))
    (argument : AdelicGL) : SmoothJets.MatrixTuples 3 arity.succ → data.cusp.H :=
  AdelicFamilyTaylor.matrixOrbit
    (fun vertices point => (FamilyCuspLift.vector data side parameter function induced vertices point).val) argument

theorem maximalCompact_uniform {degree arity : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data side parameter (function vertices))
    (lift : HasSmoothCuspLift data side parameter function) (real : Fin (arity + 1) → RealGL3) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ compact, inMaximalCompact compact →
        HasFPowerSeriesOnBall (matrixOrbit data side parameter function induced compact)
          (coefficients (matrixOrbit data side parameter function induced compact) (fun index => (real index).val))
          (fun index => (real index).val) radius ∧
        ∀ order, ‖coefficients (matrixOrbit data side parameter function induced compact)
          (fun index => (real index).val) order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order :=
  AdelicFamilyTaylor.uniform_on_compact _ (FamilyCuspLift.joint_smooth data side parameter function induced lift)
    (fun vertices level argument => congrArg Subtype.val
      (FamilyCuspLift.finite_invariant data side parameter function induced vertices argument level))
    real _ MaximalCompact.isCompact

theorem coefficients_continuous {degree arity : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data side parameter (function vertices))
    (lift : HasSmoothCuspLift data side parameter function) (real : Fin (arity + 1) -> RealGL3) (order : ℕ) :
    Continuous (fun argument => coefficients (matrixOrbit data side parameter function induced argument)
      (fun index => (real index).val) order) :=
  AdelicFamilyTaylor.coefficients_continuous _ (FamilyCuspLift.joint_smooth data side parameter function induced lift)
    (fun vertices level argument => congrArg Subtype.val
      (FamilyCuspLift.finite_invariant data side parameter function induced vertices argument level)) real order

theorem plane_decomposition {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ) (compact : AdelicGL) :
    matrixOrbit data .plane parameter function induced
        (planeUnipotent first second * planeLevi binary unit * compact) =
      planeOperator data parameter binary unit ∘ matrixOrbit data .plane parameter function induced compact := by
  funext matrices
  unfold matrixOrbit AdelicFamilyTaylor.matrixOrbit SmoothJets.matrixExtension AdelicFamilyTaylor.orbit FamilyCuspLift.vector
  dsimp only [Function.comp_def]
  rw [mul_assoc (planeUnipotent first second * planeLevi binary unit), mul_assoc,
    CuspLiftCovariance.vector_plane_radical, FlatUniqueness.planeLevi_split, mul_assoc,
    CuspLiftCovariance.vector_plane_rankOne]
  change (data.chi.toMonoidHom unit * normPower unit (-2 * inductionExponent .plane parameter)) •
    (CuspLift.vector data .plane parameter _ _
      (binaryLevi .plane binary * (compact * atInfinity (invertibleMatrix (matrices (Fin.last arity)))))).val = _
  rw [CuspLiftCovariance.vector_binary, smul_smul]
  rfl

theorem plane_decomposition_bound {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (real : Fin (arity + 1) → RealGL3) {radius : ℝ≥0} (positive : 0 < radius) (constant : ℝ)
    (bounded : ∀ compact, inMaximalCompact compact →
      HasFPowerSeriesOnBall (matrixOrbit data .plane parameter function induced compact)
        (coefficients (matrixOrbit data .plane parameter function induced compact) (fun index => (real index).val))
        (fun index => (real index).val) radius ∧
      ∀ order, ‖coefficients (matrixOrbit data .plane parameter function induced compact)
        (fun index => (real index).val) order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order)
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ)
    (compact : AdelicGL) (membership : inMaximalCompact compact) :
    HasFPowerSeriesOnBall
        (matrixOrbit data .plane parameter function induced (planeUnipotent first second * planeLevi binary unit * compact))
        (coefficients (matrixOrbit data .plane parameter function induced
          (planeUnipotent first second * planeLevi binary unit * compact)) (fun index => (real index).val))
        (fun index => (real index).val) radius ∧
      ∀ order, ‖coefficients (matrixOrbit data .plane parameter function induced
          (planeUnipotent first second * planeLevi binary unit * compact)) (fun index => (real index).val) order‖ ≤
        (planeWeight degree parameter binary unit * constant) * (radius : ℝ)⁻¹ ^ order := by
  rw [plane_decomposition]
  exact TaylorFamilies.map positive constant (bounded compact membership)
    (planeOperator data parameter binary unit) (planeWeight degree parameter binary unit)
    (planeWeight_nonnegative degree parameter binary unit) (planeOperator_norm_le data parameter binary unit)

theorem matrixOrbit_analyticAt {degree arity : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data side parameter (function vertices))
    (lift : HasSmoothCuspLift data side parameter function) (real : Fin (arity + 1) → RealGL3)
    (argument : AdelicGL) : AnalyticAt ℝ (matrixOrbit data side parameter function induced argument)
      (fun index => (real index).val) :=
  AnalyticOn.analyticAt ((SmoothJets.domain_open 3 arity.succ).mem_nhds
    (show (fun index => (real index).val) ∈ SmoothJets.domain 3 arity.succ from
      fun _ => GeneralLinearGroup.det_ne_zero _))
    ((SmoothAnalyticity.smooth_iff_analyticOn _).mp (FamilyCuspLift.joint_smooth data side parameter function induced lift argument))

theorem plane_coefficient_norm_le {degree arity : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data .plane parameter (function vertices))
    (lift : HasSmoothCuspLift data .plane parameter function) (real : Fin (arity + 1) → RealGL3)
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ) (argument : AdelicGL) (order : ℕ) :
    ‖coefficients (matrixOrbit data .plane parameter function induced
        (planeUnipotent first second * planeLevi binary unit * argument)) (fun index => (real index).val) order‖ ≤
      planeWeight degree parameter binary unit *
        ‖coefficients (matrixOrbit data .plane parameter function induced argument) (fun index => (real index).val) order‖ := by
  obtain ⟨radius, positive, constant, _, bounded⟩ := CompactTaylorBounds.local_uniform
    (matrixOrbit_analyticAt data .plane parameter function induced lift real argument)
  have expansion := (bounded _ (Metric.mem_ball_self (by exact_mod_cast positive))).1
  rw [plane_decomposition]
  apply (coefficients_norm_le ((planeOperator data parameter binary unit).comp_hasFPowerSeriesOnBall expansion) order).trans
  exact ((planeOperator data parameter binary unit).norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_right (planeOperator_norm_le data parameter binary unit) (norm_nonneg _))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FamilyCuspTaylor
