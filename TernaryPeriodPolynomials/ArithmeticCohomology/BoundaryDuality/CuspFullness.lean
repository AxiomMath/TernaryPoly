module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspSeparation
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Coordinate

@[expose] public section


/-!
# Duality at a line cusp from local nondegeneracy and the plane coordinate statement

The local value at a representative line `v̄` only depends on the Shapiro coordinate of the plane
class at the dual plane, which lies in the plane cusp orbit `g` (`CuspSeparation`). Duality at the
line cusp therefore splits into
* **local nondegeneracy** (`LocalNondegenerate`): every line summand class with nonzero coordinate
  at `v̄` has nonzero local value against every plane summand class whose coordinate at the cusp
  `g` is a suitable local joint generalized eigenclass `η` of the pair character, and
* **fullness**: every such `η` is the coordinate of a plane summand class, which is the coordinate
  statement of the separation argument (`Separation.CoordinateStatement`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.CuspFullness

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.CuspSeparation
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  {n : ℕ}

/-- **Local nondegeneracy at a line cusp.** Every line summand class `b` with nonzero Shapiro
coordinate at the representative line `v̄` has a local joint generalized eigenclass `η` of the pair
character at the plane cusp `g` such that every plane summand class with coordinate `η` has
nonzero local value with `b` at `v̄`. -/
def LocalNondegenerate (Θ : TraceData ι L P) (D : InducingData n) (T : DualityData n D.chi)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (v : L)
    (g : Bool) : Prop :=
  ∀ b ∈ boundarySummand D .line,
    fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) (Θ.lineRep v) b ≠ 0 →
    ∃ η ∈ localJoint n D.chi (pairCharacter D hecke hhecke) .plane g,
    ∀ ξ ∈ boundarySummand D .plane, cuspRes n D.chi .plane g ξ = η →
    ∃ (z : MaximalCycles n D.chi .line) (w : EdgeCochains n D.chi 1)
      (y : MaximalCycles n D.chi .plane),
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z =
        b ∧
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) y =
        ξ ∧
      EdgePrimitive z w ∧ lineValue Θ T v z w y ≠ 0

/-- **Duality at a line cusp** from local nondegeneracy and the plane coordinate statement. -/
theorem cuspDuality_of_localNondegenerate (Θ : TraceData ι L P) {D : InducingData n}
    (T : DualityData n D.chi) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (v : L) (g : Bool)
    (coordinate : Separation.CoordinateStatement D hecke hhecke .plane g)
    (nondeg : LocalNondegenerate Θ D T hecke hhecke v g) : CuspDuality Θ D T v := by
  intro b hb hne
  obtain ⟨η, hη, H⟩ := nondeg b hb hne
  obtain ⟨ξ, hξ, hξη⟩ := Submodule.mem_map.mp (coordinate hη)
  obtain ⟨z, w, y, hz, hy, hw, hval⟩ := H ξ hξ hξη
  exact ⟨ξ, hξ, z, w, y, hz, hy, hw, hval⟩

/-- **Boundary duality from local nondegeneracy and fullness at the line cusps.** The plane cusp
`good v` of the dual plane of each representative line carries the coordinate statement, and the
local value is nondegenerate there. -/
theorem associateDuality_of_localNondegenerate (Θ : TraceData ι L P) {D : InducingData n}
    (T : DualityData n D.chi) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (good : L → Bool)
    (hdual : ∀ v, ∃ γ : rationalLevel, γ.val • CuspOrbits.cuspFlag .plane (good v) =
      T.dualFlag (Θ.lineRep v))
    (hgood : ∀ u v, u ≠ v → good u = !good v)
    (hlines : ∀ F : Flags .line, ∃ v : L, ∃ γ : rationalLevel, γ.val • Θ.lineRep v = F)
    (coordinate : ∀ v, Separation.CoordinateStatement D hecke hhecke .plane (good v))
    (nondeg : ∀ v, LocalNondegenerate Θ D T hecke hhecke v (good v)) :
    AssociateDuality D T.φ T.dualFlag T.B :=
  associateDuality_of_cuspDuality Θ T good hdual hgood hlines fun v =>
    cuspDuality_of_localNondegenerate Θ T hecke hhecke v (good v) (coordinate v) (nondeg v)

end TernaryPeriodPolynomials.BoundaryDuality.CuspFullness
