module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.UniformCompact

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertSmoothCriterion

theorem smooth_iff_normalizedReal {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function) (argument : AdelicGL) :
    HilbertStandard.value data parameter function induced argument ∈ data.cusp.smooth ↔
      Smooth (fun real : Fin 1 → BinaryRealGL =>
        HilbertUniformCompact.normalizedValue data parameter function induced
          (atInfinity (real 0)) argument) := by
  have orbit :
      (fun real : Fin 1 → BinaryRealGL =>
        HilbertUniformCompact.normalizedValue data parameter function induced
          (atInfinity (real 0)) argument) =
        (fun real : Fin 1 → BinaryRealGL => data.cusp.π (atInfinity (real 0))
          (HilbertStandard.value data parameter function induced argument)) := by
    funext real
    exact HilbertUniformCompact.normalizedValue_eq_action data parameter function induced
      (atInfinity (real 0)) argument
  rw [orbit]
  constructor
  · intro membership
    exact ((data.cusp.smooth_exact _).mp membership).1
  · intro realSmooth
    apply (data.cusp.smooth_exact _).mpr
    refine ⟨realSmooth, LineOrbitLevel.level argument,
      LineOrbitLevel.level_isOpen argument, LineOrbitLevel.level_isCompact argument, ?_⟩
    intro unit
    exact HilbertFixedStandard.value_fixed data parameter function induced argument unit

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertSmoothCriterion
