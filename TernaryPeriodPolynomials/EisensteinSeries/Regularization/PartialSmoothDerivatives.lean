module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SmoothDerivatives

@[expose] public section


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem contDiffOn_iteratedFDeriv_parameter
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {function : X → Y → Z} {first : Set X} {second : Set Y}
    (smooth : ContDiffOn 𝕜 ⊤ (Function.uncurry function) (first ×ˢ second))
    (first_open : IsOpen first) (second_open : IsOpen second) (order : ℕ) :
    ContDiffOn 𝕜 ⊤
      (fun pair : X × Y => iteratedFDeriv 𝕜 order (function pair.1) pair.2)
      (first ×ˢ second) := by
  induction order with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using
      (continuousMultilinearCurryFin0 𝕜 Y Z).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn smooth
  | succ order induction =>
    intro pair member
    have previous : ContDiffAt 𝕜 ⊤
        (fun input : (X × Y) × Y =>
          iteratedFDeriv 𝕜 order (function input.1.1) input.2) (pair, pair.2) :=
      (induction.contDiffAt ((first_open.prod second_open).mem_nhds member)).comp
        (pair, pair.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have differentiated := previous.fderiv
      (f := fun input value => iteratedFDeriv 𝕜 order (function input.1) value)
      contDiffAt_snd (show (⊤ : WithTop ℕ∞) + 1 ≤ ⊤ from le_top)
    have uncurried := (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (order + 1) => Y) Z).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
        pair differentiated
    simpa [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using uncurried.contDiffWithinAt

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
