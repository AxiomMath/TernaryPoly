module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Gaffney

@[expose] public section


/-! # General coercivity, Tier B: weak `L²` primitives of closed compactly supported two-forms

With Gaffney's lemma for every admissible group (`gaffneyAt`), Hodge exactness in degree two holds
unconditionally, and every closed compactly supported equivariant two-form is the weak `L²`
derivative of an `L²` one-form.

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive

variable {Γ : Subgroup RealGL} {n : ℕ}

/-- **T1.**  For every admissible group and every `n > 0`, a closed compactly supported smooth
equivariant two-form is the weak `L²` exterior derivative of an `L²` one-form. -/
theorem Admissible.closed_has_weak_primitive [hΓ : Fact (Admissible Γ)] (hn : 0 < n)
    (ω : CForm Γ n 2) (hω : CForm.d Γ n 2 ω = 0) :
    ∃ u : Hilbert Γ n 1, (u, incl Γ n 2 ω) ∈ (maxD Γ n 1).graph :=
  Admissible.closed_has_weak_primitive_of_gaffney hn (gaffneyAt 1) ω hω

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
