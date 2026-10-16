module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Duality
public import TernaryPeriodPolynomials.Topology.DualityEquivariance.EpsNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.NeatDualityK

@[expose] public section


/-!
# Stage 2: the `G`-level duality for the residue module, unconditional

Formalized by Claude Sonnet 5.5.

`Duality.lean` proves `dualityG : H₃(G, 𝓡_n ⊗ det⁻¹) ≃ₗ Hom_G(St, 𝓡_n ⊗ det⁻¹)` conditionally on the `G`-equivariance of the
library's neat-level duality for the residue module (`NeatDualityG`).  `DualityEquivariance.capEps` is the
coefficient-reindexing compatibility of the cap product for every `k ∈ GL₃(ℤ)` and every `GL₃(ℤ)`-representation `V₀`, and
`groupOrdinaryIso_equivariant` turns it into the equivariance `Θ(c_k x) = ρ(k) ∘ Θ(x) ∘ σ(k⁻¹)`.  Instantiating
at `N = Γ(6)` inside `G = GL₃(ℤ)` (no passage through the group `K`) gives `neatDualityG`, hence the unconditional
`H3_G_equiv`.  The identity apartment evaluation of this duality is the paper's literal reading of a residue class.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology

/-- For `N = Γ(6)` inside `G` and `e = id`, the transported duality `thetaGen` is the library's neat-level duality. -/
theorem thetaGen_refl_apply (M : Rep.{0} ℚ IntegralGL)
    (y : groupHomology (Rep.res principalSix.subtype M) 3) :
    (thetaGen principalSix (MulEquiv.refl ↥principalSix) M).hom.hom y =
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso (Rep.res principalSix.subtype M)).hom.hom y := by
  have h : (groupHomology.mapIso (MulEquiv.refl ↥principalSix) (LinearEquiv.refl ℚ ↑M)
          (fun n => LinearMap.ext fun a => by
            change M.ρ n.1 a = M.ρ (MulEquiv.refl _ n).1 a
            rfl) 3).hom =
      (𝟙 (groupHomology (Rep.res principalSix.subtype M) 3) :
        groupHomology (Rep.res principalSix.subtype M) 3 ⟶
          groupHomology (transportRep principalSix (MulEquiv.refl ↥principalSix) M) 3) := by
    rw [groupHomology.mapIso_hom, ← groupHomology.map_id (A := Rep.res principalSix.subtype M) (n := 3)]
    exact groupHomology.map_congr rfl rfl 3
  have h3 : ((groupHomology.mapIso (MulEquiv.refl ↥principalSix) (LinearEquiv.refl ℚ ↑M)
          (fun n => LinearMap.ext fun a => by
            change M.ρ n.1 a = M.ρ (MulEquiv.refl _ n).1 a
            rfl) 3).hom.hom y) = y := by
    rw [h]
    rfl
  have e : (thetaGen principalSix (MulEquiv.refl ↥principalSix) M).hom.hom y =
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso
        (transportRep principalSix (MulEquiv.refl ↥principalSix) M)).hom.hom
        ((groupHomology.mapIso (MulEquiv.refl ↥principalSix) (LinearEquiv.refl ℚ ↑M)
          (fun n => LinearMap.ext fun a => by
            change M.ρ n.1 a = M.ρ (MulEquiv.refl _ n).1 a
            rfl) 3).hom.hom y) := rfl
  exact e.trans (congrArg (fun z => (OrdinaryTopBoundaryComparison.groupOrdinaryIso
    (transportRep principalSix (MulEquiv.refl ↥principalSix) M)).hom.hom z) h3)

/-- The `G`-equivariance of the neat-level duality for any `G`-representation `M` satisfying the cap reindexing
compatibility. -/
theorem neatDualityEquivariantGen_of_capEps (M : Rep.{0} ℚ IntegralGL)
    (hM : ∀ k : IntegralGL, CapEpsStatement k M) :
    NeatDualityEquivariantGen principalSix (MulEquiv.refl ↥principalSix) stG M := by
  intro g x
  apply LinearMap.ext
  intro σ
  have h1 := groupOrdinaryIso_equivariant g M (hM g) x σ
  have hx1 := thetaGen_refl_apply M (cAct principalSix M 3 g x)
  have hx2 := thetaGen_refl_apply M x
  change ((thetaGen principalSix (MulEquiv.refl ↥principalSix) M).hom.hom
      (cAct principalSix M 3 g x)).hom σ =
    M.ρ g (((thetaGen principalSix (MulEquiv.refl ↥principalSix) M).hom.hom x).hom
      (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g⁻¹) σ))
  rw [hx1, hx2]
  exact h1

/-- **The `G`-equivariance of the neat-level duality for the residue module.** -/
theorem neatDualityG (n : ℕ) : NeatDualityG n :=
  neatDualityEquivariantGen_of_capEps (ResRep n)
    (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (ResRep n))

/-- **Borel-Serre duality for `G = GL₃(ℤ)` and the residue module**, unconditional:
`H₃(G, 𝓡_n ⊗ det⁻¹) ≃ Hom_G(St, 𝓡_n ⊗ det⁻¹)` (Mathlib's `groupHomology`). -/
def H3_G_equiv (n : ℕ) :
    groupHomology (ResRep n) 3 ≃ₗ[ℚ] OrdinaryFullCoefficient.ResidueHom n (-1) :=
  dualityG n (neatDualityG n)

end TernaryPeriodPolynomials.Argument.AppendixBResidue
