module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.HomEvaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatApartment
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CoeffAtT0

@[expose] public section


/-!
# Lemma 3.3, G3: the arithmetic evaluator of a cell class is the ambient cochain on the flat chain

`ev_eq_ambient`: if the relative cap class of the interior class of a cocycle `φh` supported in a compact `K`
of the interior is the bordified class `homologyMap (cellToBordified W)` of a cellular cycle `z`, then the
arithmetic top evaluator of the group homology class of `z` (`groupApartmentEvaluation`) is the value on the
compactified flat chain `flatRep` of the ambient equivariant Hom cochain of `φh`.  The proof is
`cappedClass_apartmentEvaluation`, the identification `flatClass = identityApartmentRelativeClass`, and the
Kronecker evaluation `xHom_eval_cycle`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalSupport
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceRelativeCapConnecting
  TernaryPoly.CompactInteriorRelativeBoundary TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SingularLocalCompactCap TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.EquivariantSingularCohomology
  TernaryPeriodPolynomials.Argument.Lemma33
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

theorem ev_eq_ambient (W : Rep.{0} ℚ principalSix) (K : Compacts BordifiedOrbit)
    (hKA : (K : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ)
    (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1)))
    (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0)
    (hcap : SymmetricSpaceRelativeCap.relativeCapMap W 2 3 rfl
        (homologyMap (supportMap wholeProjection W (K : Set BordifiedOrbit)
          (boundary principalSix)ᶜ hKA) 2
          (cochainClass (supportCochains wholeProjection W (K : Set BordifiedOrbit)) 2 φh)) =
      homologyMap (cellToBordified W) 3 (cellClass W z hz)) :
    (groupApartmentEvaluation W).hom ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) =
      (ambientCochain W K φh).hom flatRep := by
  have hcl : (relativeHomCapIso W).hom (xHom W K hKA φh) =
      homologyMap (cellToBordified W) 3 (cellClass W z hz) := (xHom_cap W K hKA φh).trans hcap
  have key := cappedClass_apartmentEvaluation W (xHom W K hKA φh)
  rw [hcl] at key
  have e1 : (cellGroupHomologyMap W 3).hom (cellClass W z hz) =
      (bordifiedGroupLocalHomologyIso W 3).inv (homologyMap (cellToBordified W) 3 (cellClass W z hz)) :=
    rfl
  rw [e1, key, ← flatClass_eq_identityApartmentRelativeClass]
  exact xHom_eval_cycle W K hKA φh flatRep flatRelChain_d

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
