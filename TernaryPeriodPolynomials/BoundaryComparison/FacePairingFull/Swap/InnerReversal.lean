module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.Reversal
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.ReversalNeg
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm

@[expose] public section


/-!
# Reversal as an involution of the inner classes

Vertex reversal `revH2` of `H2` (`Swap.Reversal`) maps `InnerBoundary` classes to `InnerBoundary`
classes on either side: the edge primitive `u` of a representative `z` is replaced by `rev1 u`.
It restricts to a linear involution `revInner n side` of `innerClasses n side`, which is `-1`
(`revInner_eq_neg`, from `revH2_eq_neg`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Swap

open TernaryPeriodPolynomials.Argument.FacePairingFull

variable (n : ℕ) (side : Side)

theorem innerBoundary_revH2 {a : StratumH2 n trivialCharacter side}
    (h : InnerBoundary n trivialCharacter side a) :
    InnerBoundary n trivialCharacter side
      (revH2 rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)
        a) := by
  obtain ⟨z, hz, u, hu⟩ := h
  refine ⟨revCocycle _ _ z, by rw [← hz]; rfl, rev1 _ _ u, fun x e => ?_⟩
  rw [differentialOne_rev1]
  exact hu ![x 2, x 1, x 0] e

/-- Vertex reversal on the inner classes of one side. -/
def revInnerMap : innerClasses n side →ₗ[ℂ] innerClasses n side :=
  (revH2 rationalLevel
    (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side)).restrict
    (fun _ ha => innerBoundary_revH2 n side ha)

/-- Vertex reversal as an involutive linear equivalence of the inner classes. -/
def revInner : innerClasses n side ≃ₗ[ℂ] innerClasses n side :=
  LinearEquiv.ofInvolutive (revInnerMap n side) (fun a => Subtype.ext (revH2_revH2 _ _ a.val))

theorem revInner_val (a : innerClasses n side) :
    (revInner n side a).val =
      revH2 rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) side) a.val := rfl

theorem revInner_eq_neg (a : innerClasses n side) : revInner n side a = -a :=
  Subtype.ext (revH2_eq_neg _ _ a.val)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
