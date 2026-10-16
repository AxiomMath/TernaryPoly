module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CoeffAtT0

@[expose] public section


/-!
# Local degree of a rescaled top-cell generator

Formalized by Claude Sonnet 5.5.

The local degree `degπ` along the unipotent projection onto the three directions normal to the flat (the
three-dimensional local intersection number with the flat) is homogeneous of degree one in the chain
(`degπ_smul`); hence the local degree of the rescaled standard top-cell generator `r • T₀` is `r * dT0`
(`localDegreeGen_eq`).  Needed to compute the local intersection number of the flat with the *normalized* generator
non-circularly from the local data (`Normalized/Main.lean`).
-/

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceFlagCoordinates
  TernaryPoly.SymmetricSpaceParabolicCoordinates
open CategoryTheory Limits HomologicalComplex TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSphere
  TernaryPoly.FreeActionLinearization
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry (T0)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Normalized

/-- The local degree is homogeneous: `degπ (r • c) = r * degπ c`. -/
theorem degπ_smul (r : ℚ) (c : (chains Space).X 3)
    (h : ((localChains 3).d 3 2).hom ((locRel.f 3).hom c) = 0)
    (h' : ((localChains 3).d 3 2).hom ((locRel.f 3).hom (r • c)) = 0) :
    degπ (r • c) h' = r * degπ c h := by
  have hnext : (ComplexShape.down ℕ).next 3 = 2 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map ((localChains 3).iCycles 3)) :=
    (Preadditive.mono_iff_injective ((localChains 3).iCycles 3)).1 inferInstance
  have hl : (locRel.f 3).hom (r • c) = r • (locRel.f 3).hom c := map_smul _ _ _
  let y : ↑((localChains 3).cycles 3) :=
    (localChains 3).cyclesMk ((locRel.f 3).hom c) 2 hnext h
  have hy : ((localChains 3).iCycles 3).hom y = (locRel.f 3).hom c :=
    HomologicalComplex.i_cyclesMk (localChains 3) ((locRel.f 3).hom c) 2 hnext h
  have e : (localChains 3).cyclesMk ((locRel.f 3).hom (r • c)) 2 hnext h' = r • y := by
    apply inj
    refine (HomologicalComplex.i_cyclesMk (localChains 3) ((locRel.f 3).hom (r • c)) 2 hnext h').trans ?_
    change (locRel.f 3).hom (r • c) = ((localChains 3).iCycles 3).hom (r • y)
    rw [hl, map_smul, hy]
  unfold degπ
  rw [e]
  rw [map_smul, map_smul]
  rfl

/-- The chain of the rescaled standard top-cell generator `r • T₀`. -/
def genChain (r : ℚ) : (chains Space).X 3 := r • cellAtSpace 3 T0

theorem genChain_cycle (r : ℚ) :
    ((localChains 3).d 3 2).hom ((locRel.f 3).hom (genChain r)) = 0 := by
  unfold genChain
  rw [map_smul, map_smul, cycle_T0, smul_zero]

/-- The local degree (three-dimensional local intersection number with the flat) of the generator `r • T₀`. -/
def localDegreeGen (r : ℚ) : ℚ := degπ (genChain r) (genChain_cycle r)

theorem localDegreeGen_eq (r : ℚ) : localDegreeGen r = r * dT0 := by
  unfold localDegreeGen genChain dT0
  exact degπ_smul r (cellAtSpace 3 T0) cycle_T0 _

end TernaryPeriodPolynomials.Argument.Lemma33.Normalized
