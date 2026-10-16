module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.DiagSystem
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.NerveDiagonal

@[expose] public section


/-!
# The diagonal system and cell basis of the model resolutions `ℚ[V^{•+1} × Z]`

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable (Γ : Type) [Group Γ] (V Z : Type) [MulAction Γ V] [MulAction Γ Z]

/-- The Alexander-Whitney diagonal system of the resolution `ℚ[V^{•+1} × Z]`. -/
def nerveDiagSystem : DiagSystem (prodComplex Γ V Z) where
  Δ p q n h := nerveDelta Γ V Z p q n h
  leibniz := nerveDelta_d Γ V Z
  eps := nerveEps Γ V Z
  eps_d := nerveEps_comp_d Γ V Z
  counit p := nerveDelta_counit_right Γ V Z p

/-- The cell basis `V^{n+1} × Z` of the resolution. -/
def nerveCells (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) : CellBasis (prodComplex Γ V Z) :=
  CellBasis.ofIso (fun n => (Fin (n+1) → V) × Z)
    (fun _ γ s h => hfree γ (s.1 0) (congrFun (congrArg Prod.fst h) 0)) (fun _ => Iso.refl _)

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
