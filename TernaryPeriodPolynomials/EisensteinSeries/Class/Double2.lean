module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Double
public import TernaryPeriodPolynomials.EisensteinSeries.Class.IterComm

@[expose] public section


/-!
# `d` commutes with iterated interval integrals

Paper: "the average is a
cochain map".

`extDeriv_iteratedIntegral`: for `f` smooth on `(U × ℝ) × ℝ`, the exterior derivative of the iterated
integral `y ↦ ∫₀¹∫₀¹ f((y, a), b)` at `x ∈ U` is the iterated integral of the exterior derivatives
(`Double.hasFDerivAt_iteratedIntegral` and `iterIntegral_clm_comm`).

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly.SmoothLocalDeRham Set MeasureTheory ContinuousAlternatingMap
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- **`d` commutes with an iterated interval integral over smooth parameters.** -/
theorem extDeriv_iteratedIntegral {U : Set E} (hU : IsOpen U)
    (f : (E × ℝ) × ℝ → E [⋀^Fin k]→L[ℝ] F)
    (hf : ContDiffOn ℝ ∞ f ((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ))) {x : E} (hx : x ∈ U) :
    extDeriv (fun y => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, f ((y, a), b)) x =
      ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, extDeriv (fun y => f ((y, a), b)) x := by
  have hD := hasFDerivAt_iteratedIntegral hU f hf hx
  unfold extDeriv
  rw [hD.fderiv]
  have hDset : IsOpen (((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)) : Set ((E × ℝ) × ℝ)) :=
    (hU.prod isOpen_univ).prod isOpen_univ
  have hM : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ f p).comp (inl2 E))
      ((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hDset).mp hf).2.clm_comp contDiffOn_const
  have hcont : Continuous (Function.uncurry fun a b : ℝ =>
      (fderiv ℝ f ((x, a), b)).comp (inl2 E)) := by
    rw [← continuousOn_univ]
    refine hM.continuousOn.comp (continuous_const.prodMk continuous_fst |>.prodMk
      continuous_snd).continuousOn fun p _ => ⟨⟨hx, trivial⟩, trivial⟩
  have hcomm := iterIntegral_clm_comm
    (alternatizeUncurryFinCLM ℝ E F (n := k))
    (fun a b => (fderiv ℝ f ((x, a), b)).comp (inl2 E)) hcont
  have e : ∀ a b : ℝ, alternatizeUncurryFin ((fderiv ℝ f ((x, a), b)).comp (inl2 E)) =
      alternatizeUncurryFin (fderiv ℝ (fun y : E => f ((y, a), b)) x) := by
    intro a b
    have hdiff : DifferentiableAt ℝ f ((x, a), b) :=
      ((hf _ ⟨⟨hx, trivial⟩, trivial⟩).contDiffAt
        (hDset.mem_nhds ⟨⟨hx, trivial⟩, trivial⟩)).differentiableAt (by simp)
    have hpath : HasFDerivAt (fun y : E => ((y, a), b)) (inl2 E) x := by
      refine (((hasFDerivAt_id x).prodMk (hasFDerivAt_const a x)).prodMk
        (hasFDerivAt_const b x)).congr_fderiv ?_
      ext v <;> simp [inl2]
    have hch := hdiff.hasFDerivAt.comp x hpath
    have h3 : fderiv ℝ (fun y : E => f ((y, a), b)) x = (fderiv ℝ f ((x, a), b)).comp (inl2 E) :=
      hch.fderiv
    rw [h3]
  change (alternatizeUncurryFinCLM ℝ E F)
    (∫ (a : ℝ) (b : ℝ) in 0..1, fderiv ℝ f ((x, a), b) ∘SL inl2 E) = _
  rw [hcomm]
  refine intervalIntegral.integral_congr fun a _ => ?_
  refine intervalIntegral.integral_congr fun b _ => ?_
  exact e a b

end TernaryPeriodPolynomials.Argument.EisensteinClass
