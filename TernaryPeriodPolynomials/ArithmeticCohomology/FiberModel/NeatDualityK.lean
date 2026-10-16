module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.ThetaEquivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.KLevel

@[expose] public section


/-!
# The `K`-equivariance of the neat-level duality, from the cap/coefficient reindexing

`sixEquiv_conj` identifies Mathlib's conjugation action of `g ∈ K` on `H₃(Γ(6)-in-K, E)` with the
conjugation action `c_{g}` for `GL₃(ℤ)` on `H₃(Γ(6), E)` under `mapIso sixEquiv`;
`neatDualityEquivariant_of_capEps` combines this with `groupOrdinaryIso_equivariant`
(`ThetaEquivariance`) and the cycle-action compatibility `cycleAction_K` to obtain
`NeatDualityEquivariant n t` (the hypothesis of `kEquivOfEquivariance`) from the coefficient-reindexing
compatibility of the cap product `CapEpsStatement`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open CategoryTheory TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence
  TernaryPeriodPolynomials.Argument.GroupHomology

/-- The identification `Γ(6)`-in-`K` with `Γ(6)` is compatible with the conjugation actions. -/
theorem sixEquiv_conj (n : ℕ) (t : Fin 2) (g : KT)
    (x : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    (groupHomology.mapIso sixEquiv (LinearEquiv.refl ℚ (V n)) (fun _ => rfl) 3).hom.hom
        (cAct principalSixInK (EK n t) 3 g x) =
      (groupHomology.map (conjN principalSix g.1) (conjRep principalSix (Rep.of (coeff n t)) g.1) 3).hom
        ((groupHomology.mapIso sixEquiv (LinearEquiv.refl ℚ (V n)) (fun _ => rfl) 3).hom.hom x) := by
  have h : groupHomology.map (conjN principalSixInK g) (conjRep principalSixInK (EK n t) g) 3 ≫
        (groupHomology.mapIso sixEquiv (LinearEquiv.refl ℚ (V n)) (fun _ => rfl) 3).hom =
      (groupHomology.mapIso sixEquiv (LinearEquiv.refl ℚ (V n)) (fun _ => rfl) 3).hom ≫
        groupHomology.map (conjN principalSix g.1) (conjRep principalSix (Rep.of (coeff n t)) g.1) 3 := by
    erw [← groupHomology.map_comp, ← groupHomology.map_comp]
    refine groupHomology.map_congr ?_ ?_ 3
    · ext y
      rfl
    · ext y
      rfl
  exact congrArg (fun f => f.hom x) h

/-- **The `K`-equivariance of the neat-level duality**, given the coefficient-reindexing
compatibility of the cap product (`CapEpsStatement`). The hypothesis is discharged by `DualityEquivariance.EpsNaturality.capEps`, used in `Exports/FiberModel.H3_K_equiv`. -/
theorem neatDualityEquivariant_of_capEps (n : ℕ) (t : Fin 2)
    (h : ∀ k : IntegralGL, CapEpsStatement k (Rep.of (coeff n t))) : NeatDualityEquivariant n t := by
  intro g x
  apply LinearMap.ext
  intro σ
  have h1 := groupOrdinaryIso_equivariant g.1 (Rep.of (coeff n t)) (h g.1)
    ((groupHomology.mapIso sixEquiv (LinearEquiv.refl ℚ (V n)) (fun _ => rfl) 3).hom.hom x) σ
  have hst : stK g⁻¹ σ = TernaryPoly.OrdinaryFullAction.cycleAction
      (TernaryPoly.OrdinaryFullAction.integral g.1⁻¹) σ :=
    (TernaryPoly.OrdinaryFullAction.cycleAction_K g⁻¹ σ).symm
  change ((OrdinaryTopBoundaryComparison.groupOrdinaryIso (EGamma n t)).hom.hom
      ((groupHomology.mapIso sixEquiv (LinearEquiv.refl ℚ (V n)) (fun _ => rfl) 3).hom.hom
        (cAct principalSixInK (EK n t) 3 g x))).hom σ =
    (coeffK n t g) (((OrdinaryTopBoundaryComparison.groupOrdinaryIso (EGamma n t)).hom.hom
      ((groupHomology.mapIso sixEquiv (LinearEquiv.refl ℚ (V n)) (fun _ => rfl) 3).hom.hom x)).hom
        (stK g⁻¹ σ))
  rw [sixEquiv_conj n t g x, hst]
  exact h1

end TernaryPeriodPolynomials.Argument.FiberModel
