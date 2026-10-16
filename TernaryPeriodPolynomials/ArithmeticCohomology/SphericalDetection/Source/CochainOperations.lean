module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem smooth_vertex_reindex {dimension sourceCount targetCount : ℕ}
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (function : (Fin sourceCount → GeneralLinearGroup (Fin dimension) ℝ) → V)
    (regular : Smooth function) (reindex : Fin sourceCount → Fin targetCount) :
    Smooth (fun vertices => function (fun index => vertices (reindex index))) := by
  have input_regular : ContDiff ℝ ⊤
      (fun vertices : Fin targetCount → Matrix (Fin dimension) (Fin dimension) ℝ =>
        fun index => vertices (reindex index)) := by fun_prop
  exact regular.comp input_regular.contDiffOn (fun _ member index => member (reindex index))

theorem hasSmoothCuspLift_reindex {degree sourceCount targetCount : ℕ}
    (data : InducingData degree) (side : Side) (parameter : ℂ)
    (function : (Fin sourceCount → RealGL3) → AdelicGL → ℂ)
    (regular : HasSmoothCuspLift data side parameter function)
    (reindex : Fin sourceCount → Fin targetCount) :
    HasSmoothCuspLift data side parameter (fun vertices => function (fun index => vertices (reindex index))) := by
  intro base
  obtain ⟨lift, smooth, realizes⟩ := regular base
  let extended : Fin (sourceCount + 1) → Fin (targetCount + 1) :=
    Fin.lastCases (Fin.last targetCount) (fun index => (reindex index).castSucc)
  refine ⟨fun vertices => lift (fun index => vertices (extended index)),
    smooth_vertex_reindex _ smooth extended, ?_⟩
  intro vertices argument
  simpa only [extended, Fin.lastCases_castSucc, Fin.lastCases_last] using
    realizes (fun index => vertices (extended index)) argument

theorem hasSmoothCuspLift_sub {degree count : ℕ}
    (data : InducingData degree) (side : Side) (parameter : ℂ)
    (first second : (Fin count → RealGL3) → AdelicGL → ℂ)
    (first_regular : HasSmoothCuspLift data side parameter first)
    (second_regular : HasSmoothCuspLift data side parameter second) :
    HasSmoothCuspLift data side parameter (fun vertices argument => first vertices argument - second vertices argument) := by
  intro base
  obtain ⟨first_lift, first_smooth, first_value⟩ := first_regular base
  obtain ⟨second_lift, second_smooth, second_value⟩ := second_regular base
  refine ⟨fun vertices => first_lift vertices - second_lift vertices, first_smooth.sub second_smooth, ?_⟩
  intro vertices argument
  rw [map_sub, Pi.sub_apply, first_value, second_value, mul_sub]

theorem isInduced_sub {degree : ℕ} (data : InducingData degree) (side : Side) (parameter : ℂ)
    (first second : AdelicGL → ℂ) (first_induced : IsInduced data side parameter first)
    (second_induced : IsInduced data side parameter second) :
    IsInduced data side parameter (fun argument => first argument - second argument) := by
  refine ⟨fun base => (first_induced.1 base).sub (second_induced.1 base), ?_,
    hasSmoothCuspLift_sub data side parameter _ _ first_induced.2.2.1 second_induced.2.2.1, ?_⟩
  · intro element argument
    dsimp only
    rw [first_induced.2.1, second_induced.2.1]
  · cases side with
    | plane =>
      refine ⟨?_, ?_, ?_⟩
      · intro first_radical second_radical argument
        dsimp only
        rw [first_induced.2.2.2.1, second_induced.2.2.2.1]
      · intro unit argument
        dsimp only
        rw [first_induced.2.2.2.2.1, second_induced.2.2.2.2.1, mul_sub]
      · intro argument
        simpa only [Pi.sub_def, mul_sub] using
          (cuspFunctions data.cusp).sub_mem (first_induced.2.2.2.2.2 argument) (second_induced.2.2.2.2.2 argument)
    | line =>
      refine ⟨?_, ?_, ?_⟩
      · intro first_radical second_radical argument
        dsimp only
        rw [first_induced.2.2.2.1, second_induced.2.2.2.1]
      · intro unit argument
        dsimp only
        rw [first_induced.2.2.2.2.1, second_induced.2.2.2.2.1, mul_sub]
      · intro argument
        simpa only [Pi.sub_def, mul_sub] using
          (cuspFunctions data.cusp).sub_mem (first_induced.2.2.2.2.2 argument) (second_induced.2.2.2.2.2 argument)

theorem isSourceCocycle_sub {degree : ℕ} (data : InducingData degree) (side : Side)
    (first second : SourceCochain degree) (first_cycle : IsSourceCocycle data side first)
    (second_cycle : IsSourceCocycle data side second) :
    IsSourceCocycle data side (first - second) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro vertices monomial
    simpa only [Pi.sub_apply, Submodule.coe_sub, MvPolynomial.coeff_sub] using
      isInduced_sub data side cohomologicalPoint _ _ (first_cycle.1 vertices monomial) (second_cycle.1 vertices monomial)
  · intro monomial
    simpa only [Pi.sub_apply, Submodule.coe_sub, MvPolynomial.coeff_sub] using
      hasSmoothCuspLift_sub data side cohomologicalPoint _ _ (first_cycle.2.1 monomial) (second_cycle.2.1 monomial)
  · intro element vertices argument
    simp only [Pi.sub_apply, first_cycle.2.2.1, second_cycle.2.2.1, map_sub]
  · intro vertices argument
    have first_closed := first_cycle.2.2.2 vertices argument
    have second_closed := second_cycle.2.2.2 vertices argument
    simp only [Pi.sub_apply]
    linear_combination (norm := abel) first_closed - second_closed

end TernaryPeriodPolynomials.SphericalDetection.Helpers
