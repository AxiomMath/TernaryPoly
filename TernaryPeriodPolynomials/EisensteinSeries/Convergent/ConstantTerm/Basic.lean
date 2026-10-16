module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointEisensteinCocycle
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointSourceStandard
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Basic

@[expose] public section


/-!
# The constant-term defect of the global Eisenstein cocycle (convergent)

The defect `E c - c_side` between the restriction of the global Eisenstein cocycle and the evaluated source of each stratum, for the convergent construction.

Re-port of `TernaryPeriodPolynomials.Argument.EisensteinGraph.ConstantTerm.Basic` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm


open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
variable {n : ℕ}
/-- The source cocycle evaluated on each stratum: `c` on the plane stratum, its standard
continuation `J c` on the line stratum. -/
def sideSource (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) : (side : Side) → SourceSpace.sourceCocycles D side
  | .plane => c
  | .line => EndpointSourceStandard.sourceStandard D large hol c

/-- The Eisenstein value `E c(y)(g)` at real vertices. -/
def eisensteinValue (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (g : AdelicGL) :
    HomogeneousPoly n :=
  GlobalEisensteinCocycle.sourceValueAtReal D hol c y g

/-- The defect `(E c - c_side)(y)(g)`, where `c_side` is `c` or `J c`. -/
def defectValue (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) (side : Side) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  eisensteinValue D hol c y g - (sideSource large D hol c side).val y g

/-- The flag 2-cochain measuring the failure of the restriction formula on one stratum. -/
def defectCochain (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) (side : Side) :
    cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side) 2 :=
  (restrictionCocycle n D.chi side
      (EndpointEisensteinCocycle.globalCocycle D hol large c)).val -
    (SourceSpace.evaluatedSource D side (sideSource large D hol c side)).val

/-- The real translation family of the defect at the rational flag `q`, along the radical of
the standard parabolic scaled by `K`: `r ↦ (E c - c_side)(y)(u(K r) q⁻¹)`. -/
def defectFamily (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) (side : Side) (q : RationalGL3) (K : ℕ)
    (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) : HomogeneousPoly n :=
  defectValue large D hol c side (GlobalEisensteinCocycle.realVertices y)
    (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) * rationalGroup q⁻¹)



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm
