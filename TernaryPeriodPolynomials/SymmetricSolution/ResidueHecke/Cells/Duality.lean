module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.KLevelGeneric
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Induced

@[expose] public section


/-!
# Stage 2: the `G`-level duality for the residue module, conditional on equivariance

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.FiberModel

/-- The action of `GL₃(ℤ)` on the Steinberg module. -/
def stG : Representation ℚ IntegralGL OrdinaryIncidenceChains.Cycles :=
  (OrdinaryFullAction.cycleAction).comp OrdinaryFullAction.integral

theorem stG_principal (n : principalSix) :
    stG n.1 = SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep.ρ (MulEquiv.refl _ n) :=
  LinearMap.ext fun c =>
    OrdinaryFullAction.cycleAction_K ⟨n.1, principalSix_le_K n.2⟩ c

/-- **The equivariance of the neat-level duality for `G = GL₃(ℤ)` and the residue module**
(the single missing geometric input of Stage 2). -/
def NeatDualityG (n : ℕ) : Prop :=
  NeatDualityEquivariantGen principalSix (MulEquiv.refl principalSix) stG (ResRep n)

theorem homKGen_stG_eq (n : ℕ) :
    homKGen stG (ResRep n) = OrdinaryFullCoefficient.ResidueHom n (-1) := by
  ext Φ
  rfl

/-- **Conditional duality for `G`**: if the neat-level duality is `G`-equivariant for the residue
module, then `H₃(G, 𝓡_n ⊗ det⁻¹) ≃ Hom_G(St, 𝓡_n ⊗ det⁻¹) = ResidueHom n (-1)`. -/
def dualityG (n : ℕ) (h : NeatDualityG n) :
    groupHomology (ResRep n) 3 ≃ₗ[ℚ] OrdinaryFullCoefficient.ResidueHom n (-1) :=
  (kEquivGeneric (N := principalSix) (e := MulEquiv.refl principalSix) (σ := stG) (M := ResRep n)
    (fun n => stG_principal n) h).trans (LinearEquiv.ofEq _ _ (homKGen_stG_eq n))

end TernaryPeriodPolynomials.Argument.AppendixBResidue
