module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.ParabolicL0
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadOdd
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentPlane

@[expose] public section


/-!
# The local value at the bad line, odd degree: generic core

The identity `lineValue = -(n+1)!/3 * badGoodPairingOdd X Y` for given parabolic classes `X`, `Y`
whose images are the classes of the Levi cocycles `badX`, `badXOdd'` of the bridge
`levelThreeBridgeBadOdd`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossed parabolicCrossedH1 parabolicPairing mem_parabolicCrossed_of_mem
    twistedPairing_badLine_goodPlane TwistedPairing)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (badX badXOdd' levelThreeBridgeBadOdd)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree (badGoodPairing)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.FiberParabolicL0
  (lineValue_badLine_parabolicPairing)

variable {n : ℕ}

/-- The parabolic pairing of classes of cocycles equal to given parabolic classes (generic). -/
theorem parabolicPairing_congr {V' W' : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W']
    [Module ℂ W'] {ρb : Representation ℂ binaryArithmeticLevel V'}
    {ρb' : Representation ℂ binaryArithmeticLevel W'} {B₂ : V' →ₗ[ℂ] W' →ₗ[ℂ] ℂ}
    (P : TwistedPairing ρb ρb' B₂)
    {x : crossedCocycles ρb} {x' : crossedCocycles ρb'}
    (hx : x ∈ parabolicCrossed ρb) (hx' : x' ∈ parabolicCrossed ρb')
    (X : parabolicCrossedH1 ρb) (X' : parabolicCrossedH1 ρb')
    (hxX : (crossedBoundaries ρb).mkQ x = X.1) (hx'X' : (crossedBoundaries ρb').mkQ x' = X'.1) :
    parabolicPairing P ⟨(crossedBoundaries ρb).mkQ x, Submodule.mem_map_of_mem hx⟩
      ⟨(crossedBoundaries ρb').mkQ x', Submodule.mem_map_of_mem hx'⟩ =
    parabolicPairing P X X' :=
  congrArg₂ (fun u v => parabolicPairing P u v) (Subtype.ext hxX) (Subtype.ext hx'X')

/-- A cocycle whose class is a given parabolic class is parabolic (generic). -/
theorem mem_parabolicCrossed_of_eq {V' : Type} [AddCommGroup V'] [Module ℂ V']
    {ρb : Representation ℂ binaryArithmeticLevel V'} {x : crossedCocycles ρb}
    (X : parabolicCrossedH1 ρb) (h : (crossedBoundaries ρb).mkQ x = X.1) :
    x ∈ parabolicCrossed ρb :=
  mem_parabolicCrossed_of_mem ρb (h.symm ▸ X.2)

/-- **The local value at the bad line**, for given `U`-primitives and parabolic classes `X`, `Y`. -/
theorem lineValue_eq_pairing_core (hodd : Odd n)
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : ParabolicDuality.IdentBad.BadLineFiber n Λe ζ η ω ωU θU)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane) (hw : EdgePrimitive z w)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b, θU ![γ * a, γ * b] =
      rationalCoefficientComponent n trivialCharacter ((dualityData n trivialCharacter).φ γ)
        (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀))
    (X : parabolicCrossedH1 (levelRep (n + 1) 0))
    (Y : parabolicCrossedH1 (levelRep (n + 1) (-1)))
    (hxcls : (crossedBoundaries (levelRep (n + 1) 0)).mkQ (badX hodd.pos hF) = X.1)
    (hycls : (crossedBoundaries (levelRep (n + 1) (-1))).mkQ (badXOdd' hodd hF) =
      (thetaPar hodd Y).1) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (-((n + 1).factorial : ℂ) / 3) * badGoodPairingOdd hodd X Y := by
  have hx := mem_parabolicCrossed_of_eq X hxcls
  have hx' := mem_parabolicCrossed_of_eq (thetaPar hodd Y) hycls
  have hval := lineValue_badLine_parabolicPairing (dualityData n trivialCharacter) z w y hw
    (StabilizerVanishing.topVanishing_levelStabilizer L₀) ωU hωU hdωU θU hθU hdθU
    (twistedPairing_badLine_goodPlane hodd) hx hx' (levelThreeBridgeBadOdd hodd hF)
  refine hval.trans (congrArg (fun t => (-((n + 1).factorial : ℂ) / 3) * t) ?_)
  exact (parabolicPairing_congr (twistedPairing_badLine_goodPlane hodd) hx hx' X
    (thetaPar hodd Y) hxcls hycls).trans (badGoodPairingOdd_apply hodd X Y).symm

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd
