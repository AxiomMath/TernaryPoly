module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.CoordinateHodge

@[expose] public section


/-! The actual degree-two Hodge operator in the finite monomial basis. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

def lowHodgeAction2 (x : Fin 10 → Fin 6 → ℝ) : Fin 10 → Fin 6 → ℝ := ![
  ![(14/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (11/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6),
    (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (11/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (11/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6)],
  ![(14/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (11/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6),
    (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (11/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (11/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6)],
  ![(1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (-2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6)],
  ![(1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (-2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6)],
  ![(14/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6),
    (-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (-2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6)],
  ![(-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6)],
  ![(1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (-1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6),
    (1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨0, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (3/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6)],
  ![(-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6),
    (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6)],
  ![(1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (-1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨1, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨4, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6)],
  ![(1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6),
    (-1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6),
    (1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (-1 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨2, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨5, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨1, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨8, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (11/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨4, by decide⟩ : Fin 6),
    (-1/2 : ℝ) * x (⟨3, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (-1/2 : ℝ) * x (⟨6, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1/2 : ℝ) * x (⟨7, by decide⟩ : Fin 10) (⟨3, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨0, by decide⟩ : Fin 6) + (1 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨2, by decide⟩ : Fin 6) + (14/3 : ℝ) * x (⟨9, by decide⟩ : Fin 10) (⟨5, by decide⟩ : Fin 6)]]

theorem lowHodgeAction2_correct_0 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨0, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨0, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct_1 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨1, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨1, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct_2 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨2, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨2, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct_3 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨3, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨3, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct_4 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨4, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨4, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct_5 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨5, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨5, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct_6 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨6, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨6, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct_7 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨7, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨7, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct_8 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨8, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨8, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct_9 (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) (⟨9, by decide⟩ : Fin 10) =
      coordinatePolynomial lowExponent2 (lowHodgeAction2 x (⟨9, by decide⟩ : Fin 10)) := by
  simp [tenHodgeAction, tenCoefficientAction, tenCompactAction,
    lowCoefficientAction2_correct, Fin.sum_univ_succ]
  simp [coordinatePolynomial, lowCoefficientAction2, lowHodgeAction2, Fin.sum_univ_succ]
  module

theorem lowHodgeAction2_correct (x : Fin 10 → Fin 6 → ℝ) :
    tenHodgeAction 2 (fun j => coordinatePolynomial lowExponent2 (x j)) =
      fun j => coordinatePolynomial lowExponent2 (lowHodgeAction2 x j) := by
  funext i
  fin_cases i
  · exact lowHodgeAction2_correct_0 x
  · exact lowHodgeAction2_correct_1 x
  · exact lowHodgeAction2_correct_2 x
  · exact lowHodgeAction2_correct_3 x
  · exact lowHodgeAction2_correct_4 x
  · exact lowHodgeAction2_correct_5 x
  · exact lowHodgeAction2_correct_6 x
  · exact lowHodgeAction2_correct_7 x
  · exact lowHodgeAction2_correct_8 x
  · exact lowHodgeAction2_correct_9 x

end TernaryPoly.SL3PolynomialCoercivity
