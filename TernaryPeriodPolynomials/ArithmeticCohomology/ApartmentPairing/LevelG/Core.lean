module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.DualityG

@[expose] public section


/-!
# Lemma 3.3 at level `G = GL₃(ℤ)`: the duality for an arbitrary coefficient module and the equivariance of the evaluator

Formalized by Claude Sonnet 5.5.

* `thetaG M`: Borel--Serre duality `H₃(G, M) ≃ Hom_G(St, M)` for every `G`-representation `M`.
* `thetaG_corN`, `thetaG_corN_of_equivariant`: `Θ^G(Cor y)` is the `G/Γ(6)`-average of the neat-level functional of `y`, and
  is that functional itself when it is already `G`-equivariant.
* `apartmentEvaluation_cAct`: the top evaluator of the conjugate class `c_g x` is `ρ(g)` of the Steinberg functional of `x`
  on the apartment of frame `g⁻¹` (equivariance of the evaluator).
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.AppendixBResidue

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The `G`-level Borel--Serre duality for an arbitrary `G`-representation `M`. -/
def thetaG (M : Rep.{0} ℚ IntegralGL) : groupHomology M 3 ≃ₗ[ℚ] homKGen stG M :=
  kEquivGeneric (N := principalSix) (e := MulEquiv.refl principalSix) (σ := stG) (M := M)
    (fun n => stG_principal n)
    (neatDualityEquivariantGen_of_capEps M (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k M))

/-- **The `G`-level duality on a corestriction.**  `Θ^G(Cor y)` is the average of the neat-level functional of `y`. -/
theorem thetaG_corN (M : Rep.{0} ℚ IntegralGL) (y : groupHomology (Rep.res principalSix.subtype M) 3) :
    ((thetaG M (corN principalSix M 3 y)) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) =
      psiGen principalSix (MulEquiv.refl principalSix) M (avgN principalSix M 3 y) := by
  unfold thetaG kEquivGeneric
  simp only [LinearEquiv.trans_apply]
  have hc : ((corN principalSix M 3).domRestrict (avgN principalSix M 3).range)
      ⟨avgN principalSix M 3 y, y, rfl⟩ = corN principalSix M 3 y :=
    corN_avgN_gen y
  rw [(LinearEquiv.symm_apply_eq _).mpr (hc.symm)]
  rfl

/-- The neat-level functional of `y` in terms of the library's cap isomorphism. -/
theorem psiGen_apply (M : Rep.{0} ℚ IntegralGL) (y : groupHomology (Rep.res principalSix.subtype M) 3)
    (σ : OrdinaryIncidenceChains.Cycles) :
    psiGen principalSix (MulEquiv.refl principalSix) M y σ =
      ((OrdinaryTopBoundaryComparison.groupOrdinaryIso (Rep.res principalSix.subtype M)).hom y).hom σ :=
  congrArg (fun φ => φ.hom σ) (thetaGen_refl_apply M y)

/-- If the neat-level functional of `y` is `G`-equivariant, the `G`-level duality of `Cor y` is that functional. -/
theorem thetaG_corN_of_equivariant (M : Rep.{0} ℚ IntegralGL)
    (y : groupHomology (Rep.res principalSix.subtype M) 3)
    (hy : IsEquivOn stG M.ρ ⊤ (psiGen principalSix (MulEquiv.refl principalSix) M y)) :
    ((thetaG M (corN principalSix M 3 y)) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) =
      psiGen principalSix (MulEquiv.refl principalSix) M y := by
  rw [thetaG_corN, psiGen_avgN (neatDualityEquivariantGen_of_capEps M
    (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k M))]
  exact avg_of_isEquiv_natCard hy (by
    rw [Nat.card_eq_fintype_card]; exact card_ne_zero_gen principalSix)

/-- **The `G`-equivariance of the top evaluator** (O-G1, evaluator part): for `g ∈ GL₃(ℤ)` and a class `x` of
`H₃(Γ(6), Res M)`, the top evaluator of the conjugate class `c_g x` is `ρ(g)` of the Steinberg functional of `x` on
the translated apartment of frame `g⁻¹`. -/
theorem apartmentEvaluation_cAct (M : Rep.{0} ℚ IntegralGL) (g : IntegralGL)
    (x : groupHomology (Rep.res principalSix.subtype M) 3) :
    OrdinaryTopBoundaryComparison.groupApartmentEvaluation (Rep.res principalSix.subtype M)
        (cAct principalSix M 3 g x) =
      M.ρ g (((OrdinaryTopBoundaryComparison.groupOrdinaryIso (Rep.res principalSix.subtype M)).hom x).hom
        (OrdinaryApartmentPresentation.frameCycle g⁻¹)) := by
  have h := groupOrdinaryIso_equivariant g M
    (TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps g M) x
    OrdinaryTopBoundaryComparison.identityApartment
  rw [OrdinaryFullAction.frameCycle_equivariant, mul_one] at h
  exact h

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
