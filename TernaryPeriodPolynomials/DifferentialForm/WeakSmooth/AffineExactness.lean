module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.AffineWeakTransport
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.Zero

@[expose] public section


/-! Actual affine-coordinate preservation of weak Poincare exactness and zero-gradient rigidity. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Closed target weak one-forms pull back to actual closed source weak one-forms. -/
theorem weakOneAffineEquiv_symm_closed (e : E ≃L[ℝ] F) (a : F)
    (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (transportedTestDomain (affineTestHomeomorph e a) Ω))
    (hw : IsClosedScalarWeakOne (transportedTestDomain (affineTestHomeomorph e a) Ω) w) :
    IsClosedScalarWeakOne Ω ((weakOneAffineEquiv e a Ω).symm w) := by
  intro u v
  apply (scalarWeakAffineEquiv e a Ω).injective
  rw [← scalarWeakAffineEquiv_derivative, ← scalarWeakAffineEquiv_derivative]
  simp only [weakOneAffineEquiv_symm_apply, LinearEquiv.apply_symm_apply]
  exact hw (e u) (e v)

/-- Exactness is transported by the literal affine test/current equivalences. -/
theorem scalarWeakOneExact_affine (e : E ≃L[ℝ] F) (a : F) (Ω : TopologicalSpace.Opens E)
    (hΩ : ScalarWeakOneExact Ω) :
    ScalarWeakOneExact (transportedTestDomain (affineTestHomeomorph e a) Ω) := by
  intro w hw
  obtain ⟨T, hT⟩ := hΩ ((weakOneAffineEquiv e a Ω).symm w)
    (weakOneAffineEquiv_symm_closed e a Ω w hw)
  refine ⟨scalarWeakAffineEquiv e a Ω T, ?_⟩
  rw [← weakOneAffineEquiv_gradient, hT, LinearEquiv.apply_symm_apply]

/-- Actual zero-gradient rigidity is preserved, with the mass current explicitly transported. -/
theorem scalarWeakZeroRigid_affine (e : E ≃L[ℝ] F) (a : F) (Ω : TopologicalSpace.Opens E)
    (I : ScalarWeak Ω) (hΩ : ScalarWeakZeroRigid Ω I) :
    ScalarWeakZeroRigid (transportedTestDomain (affineTestHomeomorph e a) Ω)
      (scalarWeakAffineEquiv e a Ω I) := by
  intro T hT
  have hs : HasZeroWeakDerivative Ω ((scalarWeakAffineEquiv e a Ω).symm T) := by
    intro v
    apply (scalarWeakAffineEquiv e a Ω).injective
    rw [← scalarWeakAffineEquiv_derivative, LinearEquiv.apply_symm_apply, hT, map_zero]
  obtain ⟨c, hc⟩ := hΩ ((scalarWeakAffineEquiv e a Ω).symm T) hs
  refine ⟨c, ?_⟩
  have h := congrArg (scalarWeakAffineEquiv e a Ω) hc
  simpa only [LinearEquiv.apply_symm_apply, map_smul] using h

end TernaryPoly.PolynomialFormWeakSmooth
