module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.LiftCovariance

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FamilyCuspLift

def vector {degree arity : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data side parameter (function vertices))
    (vertices : Fin arity → RealGL3) (argument : AdelicGL) : data.cusp.smooth :=
  CuspLift.vector data side parameter (function vertices) (induced vertices) argument

theorem realizes {degree arity : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data side parameter (function vertices))
    (vertices : Fin arity → RealGL3) (argument : AdelicGL) (binary : BinaryAdelicGL) :
    data.cusp.realize (vector data side parameter function induced vertices argument) binary =
      normPower (Matrix.GeneralLinearGroup.det binary) (-binaryInductionExponent degree side parameter) *
        function vertices (binaryLevi side binary * argument) :=
  CuspLift.realizes data side parameter (function vertices) (induced vertices) argument binary

theorem joint_smooth {degree arity : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data side parameter (function vertices))
    (lift : HasSmoothCuspLift data side parameter function) (argument : AdelicGL) :
    Smooth (fun real : Fin (arity + 1) → RealGL3 =>
      (vector data side parameter function induced (fun index => real index.castSucc)
        (argument * atInfinity (real (Fin.last arity)))).val) := by
  obtain ⟨family, smooth, agreement⟩ := lift argument
  have equality (real : Fin (arity + 1) → RealGL3) :
      vector data side parameter function induced (fun index => real index.castSucc)
        (argument * atInfinity (real (Fin.last arity))) = family real := by
    apply data.cusp.injective
    funext binary
    rw [realizes, agreement]
  simpa only [equality] using smooth

theorem finite_invariant {degree arity : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
    (induced : ∀ vertices, IsInduced data side parameter (function vertices))
    (vertices : Fin arity → RealGL3) (argument : AdelicGL) (level : finiteLevel) :
    vector data side parameter function induced vertices (argument * atFinite level.val) =
      vector data side parameter function induced vertices argument :=
  CuspLift.finite_invariant data side parameter (function vertices) (induced vertices) argument level

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FamilyCuspLift
