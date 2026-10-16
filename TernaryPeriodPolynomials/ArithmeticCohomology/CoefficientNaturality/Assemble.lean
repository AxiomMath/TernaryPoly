module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.EvalSide
public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.GroupSide
public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.CapSide

@[expose] public section


/-!
# Coefficient naturality of the neat Borel--Serre duality

The arithmetic group `H₃` to ordinary functionals isomorphism `groupOrdinaryIso W` is natural in the
coefficient representation `W` of the principal-six group: for `f : W ⟶ W'`, the functional attached
to the pushforward `groupHomology.map (MonoidHom.id _) f 3 x` is the functional attached to `x`
followed by `f` (`groupOrdinaryIso_natural`).  It is assembled from the three naturality squares
`bordifiedGroupLocalHomologyIso_natural` (group side), `relativeHomCapIso_natural` (cap side) and
`relativeOrdinaryCohomologyIso_natural` (evaluation side).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CoefficientNaturality

open TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SingularLocalHomology
  TernaryPoly.IntegralGL3Congruence

/-- **Coefficient naturality of the neat duality.**  The group-homology-to-ordinary-functionals
isomorphism intertwines the pushforward of `H₃` along `f : W ⟶ W'` with postcomposition by `f`. -/
theorem groupOrdinaryIso_natural {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W')
    (x : groupHomology W 3) :
    (groupOrdinaryIso W').hom ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
      (groupOrdinaryIso W).hom x ≫ f := by
  have hA : (bordifiedGroupLocalHomologyIso W' 3).hom
        ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
      (homologyMap (localCoefficientMap bordifiedProjection bordifiedProjection_quotientCovering f)
        3).hom ((bordifiedGroupLocalHomologyIso W 3).hom x) :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (bordifiedGroupLocalHomologyIso_natural f 3)) x
  have hN0 : ∀ y, (homologyMap (localCoefficientMap bordifiedProjection
      bordifiedProjection_quotientCovering f) 3).hom ((relativeHomCapIso W).hom y) =
      (relativeHomCapIso W').hom ((homologyMap (coefHomPost upstairsRelativeChains f) 2).hom y) :=
    fun y => LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (relativeHomCapIso_natural f)) y
  have hN := hN0 ((relativeHomCapIso W).inv ((bordifiedGroupLocalHomologyIso W 3).hom x))
  rw [Iso.inv_hom_id_apply] at hN
  change (relativeOrdinaryCohomologyIso W').hom ((relativeHomCapIso W').inv
      ((bordifiedGroupLocalHomologyIso W' 3).hom
        ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x))) =
    (relativeOrdinaryCohomologyIso W).hom ((relativeHomCapIso W).inv
      ((bordifiedGroupLocalHomologyIso W 3).hom x)) ≫ f
  rw [hA, hN, Iso.hom_inv_id_apply]
  exact relativeOrdinaryCohomologyIso_natural f _

end TernaryPeriodPolynomials.Argument.CoefficientNaturality

