module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexCoefficients
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Cover.Theta

@[expose] public section


/-!
# General coercivity: determinant-twisted coefficients

The coefficient systems occurring in the paper are the symmetric powers `Sym^n` possibly
twisted by a power of the determinant, `(ρ_{n,e}(g) q) = det(g)^{-e} · (ρ_n(g) q)`, i.e.
`q ↦ det(g)^{-e} q(g⁻¹ X)`.  Every admissible group has determinant one, so on `Γ` the twisted
action coincides with the untwisted one, for real and complex coefficients; the spaces of
equivariant forms, the flat connection, the metrics, and hence the coercivity estimates, are
literally those of the untwisted systems.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.PolynomialCoefficientMetric

/-- The real coefficient action twisted by the power `det(g)^{-e}` (`e : ℤ`). -/
def twistedRealAction (n : ℕ) (e : ℤ) (g : RealGL) : Coefficients n →ₗ[ℝ] Coefficients n :=
  (g.val.det ^ (-e)) • realHomogeneousAction n g

/-- The complex coefficient action twisted by the power `det(g)^{-e}` (`e : ℤ`). -/
def twistedComplexAction (n : ℕ) (e : ℤ) (g : RealGL) :
    ComplexCoefficients n →ₗ[ℝ] ComplexCoefficients n :=
  (g.val.det ^ (-e)) • complexRho n g

theorem twistedRealAction_of_det_one (n : ℕ) (e : ℤ) {g : RealGL} (hg : g.val.det = 1) :
    twistedRealAction n e g = realHomogeneousAction n g := by
  simp [twistedRealAction, hg]

theorem twistedComplexAction_of_det_one (n : ℕ) (e : ℤ) {g : RealGL} (hg : g.val.det = 1) :
    twistedComplexAction n e g = complexRho n g := by
  simp [twistedComplexAction, hg]

/-- **Determinant-twist descent.**  On an admissible group the twisted real action is the
untwisted one. -/
theorem Admissible.twistedRealAction_eq {Γ : Subgroup RealGL} (h : Admissible Γ) (n : ℕ) (e : ℤ)
    (γ : Γ) : twistedRealAction n e (γ : RealGL) = realHomogeneousAction n (γ : RealGL) :=
  twistedRealAction_of_det_one n e (h.det_one γ.1 γ.2)

/-- **Determinant-twist descent, complex coefficients.** -/
theorem Admissible.twistedComplexAction_eq {Γ : Subgroup RealGL} (h : Admissible Γ) (n : ℕ)
    (e : ℤ) (γ : Γ) : twistedComplexAction n e (γ : RealGL) = complexRho n (γ : RealGL) :=
  twistedComplexAction_of_det_one n e (h.det_one γ.1 γ.2)

/-- The Cartan image `θ(Γ)` of an admissible group is admissible, hence the same holds for the
twisted dual systems: the twisted action of `θ γ` is the untwisted one. -/
theorem Admissible.twistedRealAction_theta_eq {Γ : Subgroup RealGL} (h : Admissible Γ) (n : ℕ)
    (e : ℤ) (γ : Γ) :
    twistedRealAction n e (thetaHom (γ : RealGL)) = realHomogeneousAction n (thetaHom (γ : RealGL)) :=
  twistedRealAction_of_det_one n e
    (h.theta.det_one _ ⟨(γ : RealGL), γ.2, rfl⟩)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
