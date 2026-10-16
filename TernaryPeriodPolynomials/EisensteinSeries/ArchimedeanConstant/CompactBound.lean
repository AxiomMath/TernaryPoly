module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SectionContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.StageTranslation

@[expose] public section


/-!
# Induced sections are bounded on compact sets

Every induced section is continuous on `GL₃(𝔸)` (`induced_continuous`), hence bounded on every
compact set, uniformly over any compact family of right real translates. The only missing uniformity
in the analytic arguments is therefore in the non-compact (cusp) directions.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.ArchimedeanConstant

theorem induced_bounded_on_compact {n : ℕ} {D : InducingData n} {side : Side} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D side s f) {S : Set AdelicGL} (hS : IsCompact S) :
    ∃ C : ℝ, ∀ g ∈ S, ‖f g‖ ≤ C :=
  hS.exists_bound_of_continuousOn
    (EisensteinRegularization.Helpers.induced_continuous hf).continuousOn

/-- Uniform bound over a compact set of arguments and a compact family of real right
translates. -/
theorem induced_bounded_on_compact_translates {n : ℕ} {D : InducingData n} {side : Side} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D side s f) {S : Set AdelicGL} (hS : IsCompact S)
    {T : Set RealGL3} (hT : IsCompact T) :
    ∃ C : ℝ, ∀ g ∈ S, ∀ k ∈ T, ‖f (g * atInfinity k)‖ ≤ C := by
  have hcont : Continuous (fun p : AdelicGL × RealGL3 => f (p.1 * atInfinity p.2)) :=
    (EisensteinRegularization.Helpers.induced_continuous hf).comp
      (continuous_fst.mul
        ((PlaneEisensteinContinuation.StageTranslation.atInfinity_continuous).comp continuous_snd))
  obtain ⟨C, hC⟩ := (hS.prod hT).exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨C, fun g hg k hk => hC (g, k) ⟨hg, hk⟩⟩

end TernaryPeriodPolynomials.ArchimedeanConstant
